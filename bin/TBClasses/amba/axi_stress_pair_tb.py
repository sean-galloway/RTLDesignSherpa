# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: AxiStressPairTB
# Purpose: Testbench for axi4_master_stress -> axi4_slave_stress
#          (val/amba/tb_axi_stress_pair.sv)
# Subsystem: framework
#
# TB class lives here per rtl/amba/CLAUDE.md Rule #0 and GLOBAL_REQUIREMENTS
# 2.1/2.3; val/amba/test_axi_stress_pair.py holds only the parameter grid and
# the cocotb_test.run() call ([[tb-structure]]).
"""Closed loop of the two stress blocks, with an independent bus monitor.

The stress master and slave check each other, so "both report zero errors"
on its own would also be the result of two blocks that agree on a wrong
contract, or check nothing. Three things stop that:

* An independent monitor on the wire between them checks every burst
  against the Python model (axi_stress_model): AXI legality of every AR/AW,
  every R beat's data and RLAST against its own burst (by RID, any order),
  every W beat's strobed bytes and WLAST. It also counts reordering and
  interleaving, so an "out of order" run that never reordered fails.
* Every run first proves traffic moved: issued == completed == the budget,
  and the slave saw the same number of bursts.
* The fault injector in the harness corrupts one handshake per fault, and
  each fault must raise the error bit the blocks claim it raises.
"""
from __future__ import annotations

import os
import random
from collections import defaultdict, deque
from typing import Dict, List, Optional

import cocotb
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba import axi_stress_model as M


class AxiStressPairTB(TBBase):
    """Drives tb_axi_stress_pair."""

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate')
        self.DW = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '64'))
        self.NWIN = self.convert_to_int(os.environ.get('TEST_NWIN', '8'))
        self.PROTO = os.environ.get('TEST_PROTO', 'axi4')    # axi4 | axi3
        self.NB = self.DW // 8
        self.BUS_LG2 = self.NB.bit_length() - 1
        random.seed(self.SEED)

        self.hash_seed = 0x1234_5678
        self.windows: List[M.Window] = []
        self.slave_tag = 0x5A
        self.mon_errors: List[str] = []
        self.stats = defaultdict(int)
        self._mon_task = None

    # ---- three mandatory TB methods (GLOBAL_REQUIREMENTS 2.2) --------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        self._park()
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        self._check_layout()
        if self._mon_task is None:
            self._mon_task = cocotb.start_soon(self._monitor())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- configuration -----------------------------------------------------

    def _park(self):
        d = self.dut
        for s in ('go', 'stop', 'clear', 'flt_arm'):
            getattr(d, s).value = 0
        for s in ('cfg_mrd', 'cfg_mwr', 'cfg_win_flat', 'cfg_srd', 'cfg_swr'):
            getattr(d, s).value = 0
        d.cfg_hash_seed.value = self.hash_seed

    def _check_layout(self):
        """The Python field lists must add up to the RTL's struct widths."""
        d = self.dut
        for port, fields in (('o_w_win', M.WIN_FIELDS), ('o_w_mcfg', M.MCFG_FIELDS),
                             ('o_w_msts', M.MSTS_FIELDS), ('o_w_scfg', M.SCFG_FIELDS),
                             ('o_w_ssts', M.SSTS_FIELDS)):
            rtl = int(getattr(d, port).value)
            assert rtl == M.width(fields), \
                f'{port}: RTL struct is {rtl} bits, Python layout {M.width(fields)}'

    def configure(self, windows: List[M.Window], mrd: Dict[str, int],
                  mwr: Dict[str, int], srd: Dict[str, int], swr: Dict[str, int]):
        self.windows = windows
        d = self.dut
        d.cfg_win_flat.value = M.pack_windows([w.fields() for w in windows], self.NWIN)
        d.cfg_mrd.value = M.pack(M.MCFG_FIELDS, mrd)
        d.cfg_mwr.value = M.pack(M.MCFG_FIELDS, mwr)
        d.cfg_srd.value = M.pack(M.SCFG_FIELDS, srd)
        d.cfg_swr.value = M.pack(M.SCFG_FIELDS, swr)
        self.slave_tag = srd.get('tag', 0)

    async def pulse(self, name: str, value: int = 1):
        getattr(self.dut, name).value = value
        await RisingEdge(self.dut.aclk)
        await Timer(100, 'ps')
        getattr(self.dut, name).value = 0

    async def go(self):
        """Clear the slave and start the master (GO is honoured only when idle)."""
        self.dut.clear.value = 1
        self.dut.go.value = 1
        await RisingEdge(self.dut.aclk)
        await Timer(100, 'ps')
        self.dut.clear.value = 0
        self.dut.go.value = 0

    def status(self) -> Dict[str, Dict[str, int]]:
        d = self.dut
        return {
            'mrd': M.unpack(M.MSTS_FIELDS, int(d.sts_mrd.value)),
            'mwr': M.unpack(M.MSTS_FIELDS, int(d.sts_mwr.value)),
            'srd': M.unpack(M.SSTS_FIELDS, int(d.sts_srd.value)),
            'swr': M.unpack(M.SSTS_FIELDS, int(d.sts_swr.value)),
        }

    async def wait_done(self, timeout_cycles: int = 200_000) -> Dict[str, Dict[str, int]]:
        for i in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            if i > 4:
                s = self.status()
                if s['mrd']['done'] and s['mwr']['done']:
                    await self.wait_clocks('aclk', 4)
                    return self.status()
        s = self.status()
        raise TimeoutError(
            f"stress master not done after {timeout_cycles} cycles: "
            f"rd issued {s['mrd']['issued']} completed {s['mrd']['completed']}, "
            f"wr issued {s['mwr']['issued']} completed {s['mwr']['completed']}")

    def describe(self, s: Dict[str, Dict[str, int]]) -> str:
        lines = []
        for k, v in s.items():
            fe = ''
            if v['fe_valid']:
                fe = (f" first={M.ERR_NAMES.get(v['fe_kind'])} id={v['fe_id']:#x} "
                      f"addr={v['fe_addr']:#010x} exp={v['fe_exp']:#010x} "
                      f"act={v['fe_act']:#010x}")
            cnt = (f"issued={v['issued']} completed={v['completed']} beats={v['beats']}"
                   if 'issued' in v else f"bursts={v['bursts']} beats={v['beats']}")
            lines.append(f"  {k}: {cnt} errors={M.err_list(v['err_mask'])} "
                         f"n={v['err_cnt']}{fe}")
        return '\n'.join(lines)

    # ---- the independent monitor ---------------------------------------------

    def _win_of(self, addr: int) -> Optional[M.Window]:
        for w in self.windows:
            if (addr >> w.size_lg2) == (w.base >> w.size_lg2):
                return w
        return None

    def _merr(self, msg: str):
        if len(self.mon_errors) < 20:
            self.log.error(f'monitor: {msg}')
        self.mon_errors.append(msg)

    def reset_monitor(self):
        self.mon_errors.clear()
        self.stats.clear()

    async def _monitor(self):
        d = self.dut
        rd_q: Dict[int, deque] = defaultdict(deque)    # rid -> bursts
        rd_order: deque = deque()                       # AR issue order (seq numbers)
        wr_q: deque = deque()
        cur_w = None
        w_pend: deque = deque()
        seq = 0
        last_rid = None
        while True:
            await RisingEdge(d.aclk)
            if not int(d.aresetn.value):
                continue
            # AR
            if int(d.m_arvalid.value) and int(d.m_arready.value):
                a, ln, sz, bt = (int(d.m_araddr.value), int(d.m_arlen.value),
                                 int(d.m_arsize.value), int(d.m_arburst.value))
                why = M.burst_illegal(a, ln, sz, bt, self.BUS_LG2)
                if why:
                    self._merr(f'AR {a:#x} len {ln} size {sz} burst {bt}: {why}')
                w = self._win_of(a)
                if w is None:
                    self._merr(f'AR {a:#x} in no window')
                addrs = M.beat_addrs(a, ln + 1, sz, bt)
                self.stats['max_len'] = max(self.stats['max_len'], ln)
                rd_q[int(d.m_arid.value)].append(
                    dict(seq=seq, addrs=addrs, size=sz, n=0,
                         resp=w.resp if w else 0))
                rd_order.append(seq)
                seq += 1
                self.stats['ar'] += 1
            # R (wire after the injector, as the master sees it)
            if int(d.m_rvalid.value) and int(d.m_rready.value):
                rid = int(d.m_rid.value)
                q = rd_q.get(rid)
                if not q:
                    self._merr(f'R on ID {rid:#x} with nothing outstanding')
                else:
                    b = q[0]
                    if last_rid is not None and last_rid != rid and self._open_other(rd_q, rid):
                        self.stats['r_interleave'] += 1
                    addr = b['addrs'][b['n']]
                    data = int(d.m_rdata.value)
                    resp = int(d.m_rresp.value)
                    if resp != M.OKAY:
                        self.stats['r_err_beats'] += 1
                    if resp == M.OKAY:
                        for lane in M.beat_lanes(addr, b['size'], self.NB):
                            exp = M.f_byte((addr & ~(self.NB - 1)) + lane, self.hash_seed,
                                           self.slave_tag, True)
                            got = (data >> (8 * lane)) & 0xFF
                            if exp != got:
                                self._merr(f'R ID {rid:#x} beat {b["n"]} addr {addr:#x} '
                                           f'lane {lane}: {got:#04x} != {exp:#04x}')
                                break
                    last = b['n'] == len(b['addrs']) - 1
                    if int(d.m_rlast.value) != int(last):
                        self._merr(f'R ID {rid:#x} RLAST={int(d.m_rlast.value)} on beat '
                                   f'{b["n"]} of {len(b["addrs"])}')
                    b['n'] += 1
                    b['open'] = True
                    if last:
                        q.popleft()
                        if rd_order and rd_order[0] != b['seq']:
                            self.stats['r_ooo'] += 1
                        if b['seq'] in rd_order:
                            rd_order.remove(b['seq'])
                        self.stats['r_bursts'] += 1
                last_rid = rid
                self.stats['r_beats'] += 1
            # AW
            if int(d.m_awvalid.value) and int(d.m_awready.value):
                a, ln, sz, bt = (int(d.m_awaddr.value), int(d.m_awlen.value),
                                 int(d.m_awsize.value), int(d.m_awburst.value))
                why = M.burst_illegal(a, ln, sz, bt, self.BUS_LG2)
                if why:
                    self._merr(f'AW {a:#x} len {ln} size {sz} burst {bt}: {why}')
                if self._win_of(a) is None:
                    self._merr(f'AW {a:#x} in no window')
                self.stats['max_len'] = max(self.stats['max_len'], ln)
                wr_q.append(dict(addrs=M.beat_addrs(a, ln + 1, sz, bt), size=sz, n=0,
                                 id=int(d.m_awid.value)))
                self.stats['aw'] += 1
            # W (before the injector). A W beat may cross the wire before its
            # AW (the slave's skid takes it), so beats wait for their AW here.
            if int(d.m_wvalid.value) and int(d.m_wready.value):
                w_pend.append((int(d.m_wdata.value), int(d.m_wstrb.value),
                               int(d.m_wlast.value), int(d.m_wid.value)))
            while w_pend and (cur_w is not None or wr_q):
                if cur_w is None:
                    cur_w = wr_q.popleft()
                data, strb, wlast, wid = w_pend.popleft()
                b = cur_w
                addr = b['addrs'][b['n']]
                if self.PROTO == 'axi3' and wid != b['id']:
                    self._merr(f'W addr {addr:#x}: WID {wid:#x} != AWID {b["id"]:#x}')
                lanes = set(M.beat_lanes(addr, b['size'], self.NB))
                for lane in range(self.NB):
                    if (strb >> lane) & 1:
                        if lane not in lanes:
                            self._merr(f'W addr {addr:#x}: strobe on lane {lane}')
                            continue
                        exp = M.f_byte((addr & ~(self.NB - 1)) + lane, self.hash_seed,
                                       self.slave_tag, False)
                        if ((data >> (8 * lane)) & 0xFF) != exp:
                            self._merr(f'W addr {addr:#x} lane {lane} data')
                            break
                if strb != sum(1 << l for l in lanes):
                    self.stats['w_partial_strb'] += 1
                last = b['n'] == len(b['addrs']) - 1
                if wlast != int(last):
                    self._merr(f'WLAST on beat {b["n"]} of {len(b["addrs"])}')
                b['n'] += 1
                if last:
                    cur_w = None
                self.stats['w_beats'] += 1
            if int(d.m_bvalid.value) and int(d.m_bready.value):
                self.stats['b'] += 1
                if int(d.m_bresp.value) != M.OKAY:
                    self.stats['b_err'] += 1

    @staticmethod
    def _open_other(rd_q, rid) -> bool:
        """Another ID has a burst part-way through: this beat interleaves."""
        for k, q in rd_q.items():
            if k != rid and q and q[0]['n'] > 0:
                return True
        return False
