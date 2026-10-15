# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""fb_endpoints testbench: the LFSR source and CRC sink behind their crossings.

Driven on the fabric clock by the framework AXI4 masters, with the endpoint
clock free-running at its own period (EP_PERIOD_NS vs ACLK_PERIOD_NS).

  loopback  every channel reads LFSR bursts from the source and writes the same
            beats back to the sink on the same channel; per channel the sink's
            CRC must equal the source's, and both beat counts must equal what
            was moved -- the run verdict the harness reports
  clear     after i_clear every CRC valid and both counts return to zero
  CH_SEL    'addr' (the default build, CH_SEL_ADDR=1): channel ch's bursts go to
            its 64 KB window and carry an ID whose low bits name a DIFFERENT
            channel, so only address selection keeps the CRCs apart. 'id'
            (CH_SEL_ADDR=0): the ID's low bits are the channel.
  line rate with rready held high and enough reads in flight, R must deliver a
            beat on nearly every fabric cycle: the endpoints and crossings
            cannot be what limits a run (DE10 PRD section 4.1)
"""
from __future__ import annotations

import os
import random

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge

from CocoTBFramework.components.axi4.axi4_factories import create_axi4_master_rd, create_axi4_master_wr
from TBClasses.shared.tbbase import TBBase

DW = 128
BYTES = DW // 8
NC = 8
SLOT_STREAM_RD = 1           # fabric slot of stream_rd / stream_wr (TOML order)
SLOT_STREAM_WR = 2
SRC_BASE = 0x9000_0000
SNK_BASE = 0xA000_0000


class FbEndpointsTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.aclk_ns = float(os.environ.get('ACLK_PERIOD_NS', '10'))
        self.ep_ns = float(os.environ.get('EP_PERIOD_NS', '8'))
        self.rng = random.Random(int(os.environ.get('SEED', '0')))
        self.errors: list[str] = []
        kw = dict(dut=dut, clock=dut.aclk, log=self.log, id_width=10, addr_width=32,
                  data_width=DW, user_width=1)
        self.rd = create_axi4_master_rd(prefix='s_rd', **kw)['interface']
        self.wr = create_axi4_master_wr(prefix='s_wr', **kw)['interface']
        self.rd.r_channel.ready_policy = 'always'
        self.moved = [0] * NC
        self.ch_sel = os.environ.get('CH_SEL', 'addr')

    # ---- mandatory ----------------------------------------------------------
    async def setup_clocks_and_reset(self):
        self.dut.i_clear.value = 0
        await self.start_clock('aclk', self.aclk_ns, 'ns')
        await self.start_clock('ep_clk', self.ep_ns, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 10)

    async def assert_reset(self):
        self.dut.aresetn.value = 0
        self.dut.ep_aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1
        self.dut.ep_aresetn.value = 1

    # ---- phases -------------------------------------------------------------
    def _id_low(self, ch: int) -> int:
        """The ID's low byte for a burst of channel ch."""
        if self.ch_sel == 'id':
            return ch
        return (ch + 1 + self.rng.randrange(NC - 1)) % NC   # never ch

    async def _channel(self, ch: int, bursts: int):
        """Read LFSR bursts on channel ch and write them straight back."""
        for _ in range(bursts):
            beats = self.rng.choice((1, 4, 8, 16))
            data = await self.rd.read_transaction(SRC_BASE + ch * 0x10000, burst_len=beats,
                                                  id=(SLOT_STREAM_RD << 8) | self._id_low(ch))
            res = await self.wr.write_transaction(SNK_BASE + ch * 0x10000, data, burst_len=beats,
                                                  id=(SLOT_STREAM_WR << 8) | self._id_low(ch))
            if res.get('response') != 0:
                self.errors.append(f"ch{ch} write resp {res.get('response')}")
                return
            self.moved[ch] += beats

    async def run_loopback(self, bursts: int) -> bool:
        jobs = [cocotb.start_soon(self._channel(ch, bursts)) for ch in range(NC)]
        for j in jobs:
            await j
        await self.settle()
        d = self.dut
        total = sum(self.moved)
        rd_beats, wr_beats = int(d.o_read_beat_count.value), int(d.o_write_beat_count.value)
        if rd_beats != total or wr_beats != total:
            self.errors.append(f"beat counts rd {rd_beats} wr {wr_beats}, moved {total}")
        rd_v, wr_v = int(d.o_read_crc_valid.value), int(d.o_write_crc_valid.value)
        for ch in range(NC):
            # packed [NC-1:0][31:0]: channel ch is bits [32*ch +: 32]
            rd_crc = (int(d.o_read_crc_value.value) >> (32 * ch)) & 0xFFFFFFFF
            wr_crc = (int(d.o_write_crc_value.value) >> (32 * ch)) & 0xFFFFFFFF
            if not (rd_v >> ch & 1 and wr_v >> ch & 1):
                self.errors.append(f"ch{ch}: crc valid rd {rd_v >> ch & 1} wr {wr_v >> ch & 1}")
            elif rd_crc != wr_crc:
                self.errors.append(f"ch{ch}: sink crc 0x{wr_crc:08X} != source crc 0x{rd_crc:08X}")
        self.log.info(f"loopback: {total} beats over {NC} channels, "
                      f"crc valid rd 0x{rd_v:02X} wr 0x{wr_v:02X}")
        return not self.errors

    async def settle(self):
        """Let the last beats cross and a fresh snapshot arrive (both clocks)."""
        await self.wait_clocks('aclk', 40)

    async def run_clear(self) -> bool:
        d = self.dut
        await FallingEdge(d.aclk)
        d.i_clear.value = 1
        await FallingEdge(d.aclk)
        d.i_clear.value = 0
        await self.settle()
        state = (int(d.o_read_crc_valid.value), int(d.o_write_crc_valid.value),
                 int(d.o_read_beat_count.value), int(d.o_write_beat_count.value))
        if any(state):
            self.errors.append(f"after clear: rd_valid 0x{state[0]:02X} wr_valid 0x{state[1]:02X} "
                               f"rd_beats {state[2]} wr_beats {state[3]}")
        return not self.errors

    async def run_line_rate(self, bursts_per_ch: int, floor: float) -> float:
        """R beats per fabric cycle, measured over the busy window."""
        d = self.dut
        beats = cycles = 0
        done = False

        async def count():
            nonlocal beats, cycles
            started = False
            while not done:
                await RisingEdge(d.aclk)
                hs = int(d.s_rd_rvalid.value) and int(d.s_rd_rready.value)
                started = started or hs
                if started:
                    cycles += 1
                    beats += hs

        async def reader(ch):
            for _ in range(bursts_per_ch):
                await self.rd.read_transaction(SRC_BASE, burst_len=16, id=(SLOT_STREAM_RD << 8) | ch)

        counter = cocotb.start_soon(count())
        jobs = [cocotb.start_soon(reader(ch)) for ch in range(NC)]
        for j in jobs:
            await j
        done = True
        await counter
        rate = beats / cycles if cycles else 0.0
        self.log.info(f"line rate: {beats} beats in {cycles} fabric cycles = {rate:.3f} beats/cycle "
                      f"(aclk {self.aclk_ns} ns, ep_clk {self.ep_ns} ns, floor {floor})")
        if rate < floor:
            self.errors.append(f"line rate {rate:.3f} below {floor}")
        return rate

    def report(self) -> bool:
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
