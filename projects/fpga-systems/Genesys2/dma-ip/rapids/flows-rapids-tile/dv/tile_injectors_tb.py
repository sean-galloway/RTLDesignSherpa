# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: tile_injectors_tb
# Purpose: Unit testbench for the rapids tile harness's cell model
#          (tile_cell_tx + tile_credit_rx, rapids TASK-032)
#
# Subsystem: fpga-systems/Genesys2/rapids tile harness
# Author: sean galloway
# Created: 2026-10-19
"""The cocotb side plays RAPIDS for two cells.

It takes each cell's packets on an AXIS slave BFM (with backpressure) and
returns their flits as credit packets through tile_credit_rx, the way
RAPIDS's m_tile_credit_* port would. The checks are the cell's contract:
every packet a header beat (the TILE_SPEC 11.5 layout) then its payload; a
cell never has more flits out than its strap; the payload CRC equals the
cell's expected CRC (so the header took no LFSR step and no beat was lost);
and every strap is whole once the returns are in.
"""

import os
import random
import zlib
from typing import Any, Dict, List, Tuple

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axis4.axis_factories import create_axis_slave
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_cxs_tile_tb import (
    PTYPE_CREDIT, PTYPE_MEM, RAPIDS_COORD, TileHeader, coord)

OP_ADD, OP_SET = 0, 1
CLASS_SPACE, CLASS_DESC = 0, 1
HDR_STRB = (1 << 16) - 1


class TileInjectorsTB(TBBase):
    """tb_tile_cell_loop: cell A (slot 0, channel 2), cell B (slot 6, channel 5)."""

    CELLS = {'a': dict(coord=coord(0, 0, 0, 0, ext=1), channel=2),
             'b': dict(coord=coord(0, 2, 1, 0, ext=1), channel=5)}

    def __init__(self, dut):
        super().__init__(dut)
        self.DW = int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.SW = self.DW // 8
        self.LAND = int(os.environ.get('TEST_LAND_FLITS', '16'))
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.beats: Dict[str, List[Tuple[int, int, int, int]]] = {x: [] for x in self.CELLS}
        self.out_flits = {x: 0 for x in self.CELLS}      # sent and not yet returned
        self.peak_out = {x: 0 for x in self.CELLS}
        self.errors: List[str] = []
        self.slaves = {}
        self.crd = None

    # ---- the three mandatory methods -------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        for name in ('cfg_start', 'cfg_seed', 'cfg_num_beats', 'cfg_beats_per_pkt', 'cfg_hold'):
            getattr(self.dut, name).value = 0
        self._create_bfms()
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- BFMs ----------------------------------------------------------------
    def _create_bfms(self):
        ready = FlexRandomizer({'ready_delay': ([(0, 0), (1, 3), (4, 12)], [6, 3, 1])})
        for x in self.CELLS:
            s = create_axis_slave(dut=self.dut, clock=self.clk, prefix=f"{x}_axis_", log=self.log,
                                  data_width=self.DW, id_width=8, dest_width=4, user_width=1,
                                  randomizer=ready)
            s['slave'].add_callback(lambda pkt, x=x: self._on_beat(x, pkt))
            self.slaves[x] = s
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name='packet', bits=128, format='hex',
                                     description='credit packet: one tile header'))
        self.crd = create_gaxi_master(dut=self.dut, title="CreditMaster", prefix="crd",
                                      clock=self.clk, field_config=fc, log=self.log,
                                      mode='skid', multi_sig=True)

    def _on_beat(self, x: str, pkt):
        f = pkt.fields
        beat = (int(f.get('data', 0)), int(f.get('strb', 0)), int(f.get('last', 0)), int(f.get('id', 0)))
        self.beats[x].append(beat)

    # ---- helpers -------------------------------------------------------------
    def packets(self, x: str) -> List[List[Tuple[int, int, int, int]]]:
        pkts, cur = [], []
        for b in self.beats[x]:
            cur.append(b)
            if b[2]:
                pkts.append(cur)
                cur = []
        return pkts

    def stat(self, name: str) -> int:
        return int(getattr(self.dut, name).value)

    async def send_credit(self, dst: int, count: int, op: int = OP_ADD, cls: int = CLASS_SPACE,
                          ptype: int = PTYPE_CREDIT, src: int = RAPIDS_COORD):
        hdr = TileHeader(dst=dst, src=src, ptype=ptype, op=op, length=count, target=cls, tag=0)
        await self.crd.send(self.crd.create_packet(packet=hdr.pack()))

    async def start(self, num_beats: int, beats_per_pkt: int, seed: int = 0x1234_5678):
        self.dut.cfg_seed.value = seed
        self.dut.cfg_num_beats.value = num_beats
        self.dut.cfg_beats_per_pkt.value = beats_per_pkt
        self.dut.cfg_start.value = 1
        await RisingEdge(self.clk)
        self.dut.cfg_start.value = 0

    def check_packet(self, x: str, k: int, pkt, want_beats: int) -> List[str]:
        c = self.CELLS[x]
        errs = []
        hdr_word, hdr_strb, hdr_last, tid = pkt[0]
        want = TileHeader(dst=RAPIDS_COORD, src=c['coord'], ptype=PTYPE_MEM, op=0,
                          length=want_beats * self.SW, target=0, tag=c['channel'])
        if TileHeader.unpack(hdr_word) != want:
            errs.append(f"{x} packet {k}: header {TileHeader.unpack(hdr_word)} != {want}")
        if hdr_word >> 128:
            errs.append(f"{x} packet {k}: header beat has data above bit 127")
        if hdr_strb != HDR_STRB or hdr_last:
            errs.append(f"{x} packet {k}: header strobe 0x{hdr_strb:X} / last {hdr_last}")
        if len(pkt) - 1 != want_beats:
            errs.append(f"{x} packet {k}: {len(pkt) - 1} payload beats, expected {want_beats}")
        for i, (_d, strb, _l, t) in enumerate(pkt):
            if t != c['channel']:
                errs.append(f"{x} packet {k} beat {i}: tid {t}, expected {c['channel']}")
                break
            if i and strb != (1 << self.SW) - 1:
                errs.append(f"{x} packet {k} beat {i}: strobe 0x{strb:X}")
                break
        return errs

    def payload_crc(self, x: str) -> int:
        """CRC-32 of the low 32-bit LFSR word of every payload beat, as the
        injector's dataint_crc computes it (reflected CRC-32 = zlib)."""
        data = b''.join((d & 0xFFFF_FFFF).to_bytes(4, 'little')
                        for pkt in self.packets(x) for d, _s, _l, _t in pkt[1:])
        return zlib.crc32(data) & 0xFFFF_FFFF

    async def rapids(self, return_after: int = 20, returns: bool = True, stop: List[bool] = None):
        """Play RAPIDS's landing space: a packet's flits come back
        `return_after` cycles (jittered) after its last beat lands."""
        seen = {x: 0 for x in self.CELLS}
        pending = []   # (cycle, cell, flits)
        cycle = 0
        while not (stop and stop[0]):
            await RisingEdge(self.clk)
            cycle += 1
            for x in self.CELLS:
                pk = self.packets(x)
                while seen[x] < len(pk):
                    flits = len(pk[seen[x]])
                    self.out_flits[x] += flits
                    self.peak_out[x] = max(self.peak_out[x], self.out_flits[x])
                    if self.out_flits[x] > self.LAND:
                        self.errors.append(f"{x}: {self.out_flits[x]} flits out, strap {self.LAND}")
                    if returns:
                        pending.append((cycle + return_after + random.randint(0, 15), x, flits))
                    seen[x] += 1
            due = [p for p in pending if p[0] <= cycle]
            for p in due:
                pending.remove(p)
                await self.send_credit(self.CELLS[p[1]]['coord'], p[2])
                self.out_flits[p[1]] -= p[2]

    async def wait_for(self, cond, cycles: int = 20000) -> bool:
        for _ in range(cycles):
            if cond():
                return True
            await RisingEdge(self.clk)
        return cond()

    def _finish(self, errors: List[str], what: str) -> Tuple[bool, Dict[str, Any]]:
        errors = self.errors + errors
        for e in errors:
            self.log.error(f"  SCOREBOARD: {e}")
        if not errors:
            self.log.info(f"  SCOREBOARD: {what} verified")
        return not errors, {'errors': errors}

    def _errs_clean(self) -> List[str]:
        errs = []
        for name in ('a_err_over', 'a_err_big', 'b_err_over', 'b_err_big', 'crd_err'):
            if self.stat(name):
                errs.append(f"{name} set")
        return errs

    # ---- scenarios -----------------------------------------------------------
    async def test_stream(self, num_beats: int = 70, beats_per_pkt: int = 7) -> Tuple[bool, Dict[str, Any]]:
        """Both cells stream past their straps; the returns keep them going."""
        self.log.info(f"=== cells: {num_beats} beats in packets of {beats_per_pkt}, strap {self.LAND} ===")
        stop = [False]
        cocotb.start_soon(self.rapids(stop=stop))
        await self.start(num_beats, beats_per_pkt)
        npk = -(-num_beats // beats_per_pkt)
        ok = await self.wait_for(lambda: all(len(self.packets(x)) >= npk for x in self.CELLS)
                                 and all(self.out_flits[x] == 0 for x in self.CELLS)
                                 and all(self.stat(f"{x}_free") == self.LAND for x in self.CELLS), 40000)
        stop[0] = True
        errors = [] if ok else ["the cells did not finish with their straps whole"]
        for x in self.CELLS:
            pk = self.packets(x)
            if len(pk) != npk:
                errors.append(f"{x}: {len(pk)} packets, expected {npk}")
            for k, p in enumerate(pk):
                left = num_beats - k * beats_per_pkt
                errors += self.check_packet(x, k, p, min(beats_per_pkt, left))
            got, want = self.payload_crc(x), self.stat(f"{x}_crc")
            if got != want:
                errors.append(f"{x}: payload CRC 0x{got:08X}, cell expected 0x{want:08X}")
            sent, ret = self.stat(f"{x}_sent"), self.stat(f"{x}_returned")
            if sent != num_beats + npk or ret != sent:
                errors.append(f"{x}: sent {sent} flits, returned {ret}, expected {num_beats + npk} both")
            if self.peak_out[x] < self.LAND - beats_per_pkt:
                errors.append(f"{x}: at most {self.peak_out[x]} flits out: the strap was never used")
        if self.a_crc_differs_check():
            errors.append("cells A and B sent the same payload: the per-channel seed is not applied")
        return self._finish(errors + self._errs_clean(), "cell stream")

    def a_crc_differs_check(self) -> bool:
        return self.stat('a_crc') == self.stat('b_crc')

    async def test_strap_gate(self, beats_per_pkt: int = 7) -> Tuple[bool, Dict[str, Any]]:
        """No returns: each cell sends exactly what its strap covers, then waits."""
        self.log.info("=== cells: the strap stops a cell with no returns ===")
        stop = [False]
        cocotb.start_soon(self.rapids(returns=False, stop=stop))
        await self.start(10 * beats_per_pkt, beats_per_pkt)
        await self.wait_clocks(self.clk_name, 2000)
        fit = self.LAND // (1 + beats_per_pkt)
        errors = []
        for x in self.CELLS:
            n = len(self.packets(x))
            if n != fit:
                errors.append(f"{x}: {n} packets went with no returns, the strap covers {fit}")
            if self.stat(f"{x}_free") != self.LAND - fit * (1 + beats_per_pkt):
                errors.append(f"{x}: strap_free {self.stat(f'{x}_free')}")
        # One return for A only: A sends one more, B stays put
        await self.send_credit(self.CELLS['a']['coord'], 1 + beats_per_pkt)
        self.out_flits['a'] -= 1 + beats_per_pkt
        await self.wait_clocks(self.clk_name, 500)
        if len(self.packets('a')) != fit + 1 or len(self.packets('b')) != fit:
            errors.append(f"after one return to A: A {len(self.packets('a'))}, B {len(self.packets('b'))} "
                          f"packets, expected {fit + 1}, {fit}")
        stop[0] = True
        return self._finish(errors + self._errs_clean(), "strap gate")

    async def test_bad_returns(self) -> Tuple[bool, Dict[str, Any]]:
        """Malformed returns are counted, flagged and not applied; an
        over-return is flagged by the cell; a set restores the strap."""
        self.log.info("=== credit intake: bad returns ===")
        a = self.CELLS['a']['coord']
        await self.send_credit(a, 1, ptype=PTYPE_MEM)                 # not a credit
        await self.send_credit(a, 1, cls=CLASS_DESC)                  # cell slot, class 1
        await self.send_credit(coord(1, 0, 0, 0, ext=1), 1)           # core slot, class 0
        await self.send_credit(coord(0, 0, 0, 0, ext=0), 1)           # a node: no external slot
        await self.send_credit(a, 1, src=coord(0, 1, 1, 0, ext=1))    # not from RAPIDS
        await self.wait_clocks(self.clk_name, 20)
        errors = []
        if self.stat('crd_errs') != 5 or not self.stat('crd_err'):
            errors.append(f"credit intake counted {self.stat('crd_errs')} errors, expected 5")
        if self.stat('a_free') != self.LAND or self.stat('a_err_over'):
            errors.append("a malformed return reached cell A")
        await self.send_credit(a, 1)                                  # A has nothing out
        await self.wait_clocks(self.clk_name, 10)
        if not self.stat('a_err_over') or self.stat('a_free') != self.LAND:
            errors.append(f"over-return: err {self.stat('a_err_over')}, free {self.stat('a_free')}")
        if self.stat('b_err_over'):
            errors.append("an over-return to A flagged B")
        if self.stat('crd_pkts') != 6 or self.stat('crd_sets') != 0:
            errors.append(f"credit intake: {self.stat('crd_pkts')} packets, {self.stat('crd_sets')} sets")
        # Hold: the intake stops taking
        self.dut.cfg_hold.value = 1
        await self.wait_clocks(self.clk_name, 2)
        if self.stat('crd_ready'):
            errors.append("cfg_hold did not drop crd_ready")
        self.dut.cfg_hold.value = 0
        self.errors = []
        return self._finish(errors, "bad returns")

    async def test_too_big(self) -> Tuple[bool, Dict[str, Any]]:
        """A packet bigger than the strap is refused and flagged, never sent."""
        self.log.info("=== cells: a packet larger than the strap ===")
        await self.start(2 * self.LAND, self.LAND)        # LAND beats + header > LAND
        await self.wait_clocks(self.clk_name, 200)
        errors = []
        for x in self.CELLS:
            if not self.stat(f"{x}_err_big"):
                errors.append(f"{x}: err_pkt_too_big not set")
            if self.beats[x]:
                errors.append(f"{x}: {len(self.beats[x])} beats went out")
        return self._finish(errors, "oversized packet")
