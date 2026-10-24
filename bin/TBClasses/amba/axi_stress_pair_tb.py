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
  With AXI5 it also checks every request's NSAID / TRACE / MPAM / MECID
  against f_sb(start address), every RTRACE / BTRACE (the request's TRACE,
  echoed) and every R / W
  poison bit, and counts poisoned beats, so a poison run that never
  poisoned anything fails too. It checks the IDUNQ rule on the wire (a unique
  request only on an ID with nothing outstanding, nothing on an ID whose
  unique burst is out) and that BIDUNQ / RIDUNQ return each burst's bit.
  Atomics: every AWATOP must be a shape the master issues, on an ID with
  nothing else outstanding; each read-return class must get exactly one R
  beat with its ID, RLAST set and the read hash on its lanes. A run counts
  each class, so an atomic run that never issued one fails.
  MTE: AWTAGOP / ARTAGOP, every W beat's WTAG / WTAGUPDATE, every read beat's
  RTAG and every BTAGMATCH against the tag contract; tag operations are
  counted by kind.
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
        self.PROTO = os.environ.get('TEST_PROTO', 'axi4')    # axi4 | axi3 | axi5 | axil4 | axil5
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
        for s in ('go', 'stop', 'clear', 'flt_arm', 'hold_b'):
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

    def _check_req_sb(self, ch: str, a: int, fields=None):
        """AXI5: the request sideband fields of an AR / AW at address a
        (AXI5-Lite carries only TRACE: fields=('trace',))."""
        d = self.dut
        sb = M.f_sb(a, self.hash_seed)
        exp = {'nsaid': sb & 0xF, 'trace': (sb >> 4) & 1,
               'mpam': (sb >> 5) & 0x7FF, 'mecid': (sb >> 16) & 0xFFFF}
        if fields is not None:
            exp = {f: exp[f] for f in fields}
        for f, e in exp.items():
            got = int(getattr(d, f'm_{ch}{f}').value)
            if got != e:
                self._merr(f'{ch.upper()} {a:#x}: {ch.upper()}{f.upper()} {got:#x} != {e:#x}')
        self.stats['sb_req'] += 1

    def _check_uq(self, ch: str, live: list, uq: int, a: int):
        """AXI5 IDUNQ (A5.2) on one ID's outstanding list, then record."""
        if uq and live:
            self._merr(f'{ch.upper()} {a:#x}: IDUNQ with {len(live)} outstanding on the ID')
        if any(live):
            self._merr(f'{ch.upper()} {a:#x}: issued while a unique burst is outstanding')
        live.append(uq)
        self.stats[f'uq_{ch}'] += uq

    async def _monitor(self):
        d = self.dut
        axi5 = self.PROTO == 'axi5'
        lite5 = self.PROTO == 'axil5'       # AXI5-Lite: TRACE and POISON only
        tp = axi5 or lite5                   # TRACE / POISON checked
        b_q: Dict[int, deque] = defaultdict(deque)     # bid -> AW addresses
        uq_out = {'ar': defaultdict(list), 'aw': defaultdict(list)}   # id -> [uq bits]
        rr_exp: Dict[int, tuple] = {}                   # read-return atomics owed: id -> (addr, size, win)
        rd_q: Dict[int, deque] = defaultdict(deque)    # rid -> bursts
        rd_order: deque = deque()                       # AR issue order (seq numbers)
        wr_q: deque = deque()
        cur_w = None
        w_pend: deque = deque()
        seq = 0
        last_rid = None
        wire_out = 0          # requests accepted and not yet answered, both directions
        w_in_burst, w_ahead = False, 0            # W_FIRST mirror state
        has_wlast = hasattr(d, 'm_wlast')
        while True:
            await RisingEdge(d.aclk)
            if not int(d.aresetn.value):
                continue
            # W_FIRST evidence, mirroring axi_stress_w_first_gate: write data is
            # in sight when a W beat is offered or a W burst was taken ahead of
            # its AW (w_ahead = W bursts begun - AWs accepted, floored at 0).
            # Counted: an AW taken with none in sight, and an AW held with none.
            awv, awr, wv = int(d.m_awvalid.value), int(d.m_awready.value), int(d.m_wvalid.value)
            w_hs = wv and int(d.m_wready.value)
            w_begin = w_hs and not w_in_burst
            if w_hs:
                w_in_burst = not (int(d.m_wlast.value) if has_wlast else 1)
            in_sight = wv or w_ahead > 0
            if awv and awr and not in_sight:
                self.stats['aw_hs_no_w'] += 1
            if awv and not awr and not in_sight:
                self.stats['aw_wait_no_w'] += 1
            if w_begin and not (awv and awr):
                w_ahead = min(15, w_ahead + 1)
            elif (awv and awr) and not w_begin:
                w_ahead = max(0, w_ahead - 1)
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
                uq = int(d.m_aridunq.value) if axi5 else 0
                if axi5:
                    self._check_req_sb('ar', a)
                    self._check_uq('ar', uq_out['ar'][int(d.m_arid.value)], uq, a)
                elif lite5:
                    self._check_req_sb('ar', a, fields=('trace',))
                tagop = 0
                if axi5:
                    tagop = int(d.m_artagop.value)
                    if tagop != M.f_artagop(a, self.hash_seed):
                        self._merr(f'AR {a:#x}: ARTAGOP {tagop} != {M.f_artagop(a, self.hash_seed)}')
                    self.stats[f'artagop{tagop}'] += 1
                rd_q[int(d.m_arid.value)].append(
                    dict(seq=seq, addrs=addrs, size=sz, n=0,
                         resp=w.resp if w else 0, win=w, start=a, uq=uq, tagop=tagop))
                rd_order.append(seq)
                seq += 1
                self.stats['ar'] += 1
                wire_out += 1
                self.stats['max_wire_out'] = max(self.stats['max_wire_out'], wire_out)
            # R (wire after the injector, as the master sees it)
            if (axi5 and int(d.m_rvalid.value) and int(d.m_rready.value)
                    and int(d.m_rid.value) in rr_exp):
                rid = int(d.m_rid.value)
                a, sz, w = rr_exp.pop(rid)
                if not int(d.m_rlast.value):
                    self._merr(f'atomic R ID {rid:#x}: RLAST low')
                if int(d.m_rresp.value) == M.OKAY:
                    data = int(d.m_rdata.value)
                    for lane in M.beat_lanes(a, sz, self.NB):
                        exp = M.f_byte((a & ~(self.NB - 1)) + lane, self.hash_seed,
                                       self.slave_tag, True)
                        if ((data >> (8 * lane)) & 0xFF) != exp:
                            self._merr(f'atomic R ID {rid:#x} addr {a:#x} lane {lane}')
                            break
                self.stats['atom_rr'] += 1
            elif int(d.m_rvalid.value) and int(d.m_rready.value):
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
                    if tp:
                        w = b['win']
                        e_tr = M.f_rsb(M.f_sb(b['start'], self.hash_seed)) if (w and w.sb) else 0
                        e_p = int(M.f_poison(addr, self.hash_seed, w.poison_lg2 if w else 0))
                        if int(d.m_rtrace.value) != e_tr:
                            self._merr(f'R ID {rid:#x} addr {addr:#x}: RTRACE != {e_tr}')
                        if int(d.m_rpoison.value) != e_p:
                            self._merr(f'R ID {rid:#x} addr {addr:#x}: RPOISON != {e_p}')
                        self.stats['r_poison'] += e_p
                    if axi5:
                        w = b['win']
                        if int(d.m_ridunq.value) != b['uq']:
                            self._merr(f'R ID {rid:#x} addr {addr:#x}: RIDUNQ != {b["uq"]}')
                        e_t = M.beat_tags(addr, self.NB, self.hash_seed, True,
                                          b['tagop'] if (w and w.mte) else 0)
                        if int(d.m_rtag.value) != e_t:
                            self._merr(f'R ID {rid:#x} addr {addr:#x}: RTAG {int(d.m_rtag.value):#x} != {e_t:#x}')
                    last = b['n'] == len(b['addrs']) - 1
                    if int(d.m_rlast.value) != int(last):
                        self._merr(f'R ID {rid:#x} RLAST={int(d.m_rlast.value)} on beat '
                                   f'{b["n"]} of {len(b["addrs"])}')
                    b['n'] += 1
                    b['open'] = True
                    if last:
                        q.popleft()
                        if axi5:
                            uq_out['ar'][rid].pop(0)
                        if rd_order and rd_order[0] != b['seq']:
                            self.stats['r_ooo'] += 1
                        if b['seq'] in rd_order:
                            rd_order.remove(b['seq'])
                        self.stats['r_bursts'] += 1
                        wire_out -= 1
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
                uq = int(d.m_awidunq.value) if axi5 else 0
                if axi5:
                    self._check_req_sb('aw', a)
                    awid = int(d.m_awid.value)
                    atop = int(d.m_awatop.value)
                    if atop:
                        why = M.atop_illegal(atop, ln, sz, bt, a, self.BUS_LG2)
                        if why:
                            self._merr(f'AW {a:#x} AWATOP {atop:#04x}: {why}')
                        if uq_out['aw'][awid] or awid in rr_exp or rd_q.get(awid):
                            self._merr(f'atomic AW {a:#x} on ID {awid:#x}, which is in use')
                        self.stats[f'atom_{M.atop_class(atop)}'] += 1
                        if atop & 0x20:
                            rr_exp[awid] = (a, sz, self._win_of(a))
                    self._check_uq('aw', uq_out['aw'][awid], uq, a)
                elif lite5:
                    self._check_req_sb('aw', a, fields=('trace',))
                tagop = 0
                if axi5:
                    tagop = int(d.m_awtagop.value)
                    e_op = 0 if int(d.m_awatop.value) else M.f_awtagop(a, self.hash_seed)
                    if tagop != e_op:
                        self._merr(f'AW {a:#x}: AWTAGOP {tagop} != {e_op}')
                    self.stats[f'awtagop{tagop}'] += 1
                b_q[int(d.m_awid.value)].append((a, self._win_of(a), uq, tagop))
                wr_q.append(dict(addrs=M.beat_addrs(a, ln + 1, sz, bt), size=sz, n=0,
                                 id=int(d.m_awid.value), win=self._win_of(a), tagop=tagop))
                self.stats['aw'] += 1
                wire_out += 1
                self.stats['max_wire_out'] = max(self.stats['max_wire_out'], wire_out)
            # W (before the injector). A W beat may cross the wire before its
            # AW (the slave's skid takes it), so beats wait for their AW here.
            if int(d.m_wvalid.value) and int(d.m_wready.value):
                w_pend.append((int(d.m_wdata.value), int(d.m_wstrb.value),
                               int(d.m_wlast.value), int(d.m_wid.value),
                               int(d.m_wpoison.value), int(d.m_wtag.value),
                               int(d.m_wtagupdate.value)))
            while w_pend and (cur_w is not None or wr_q):
                if cur_w is None:
                    cur_w = wr_q.popleft()
                data, strb, wlast, wid, wpoison, wtag, wtagupd = w_pend.popleft()
                b = cur_w
                addr = b['addrs'][b['n']]
                if tp:
                    w = b['win']
                    e_p = int(M.f_poison(addr, self.hash_seed, w.poison_lg2 if w else 0))
                    if wpoison != e_p:
                        self._merr(f'W addr {addr:#x}: WPOISON {wpoison} != {e_p}')
                    self.stats['w_poison'] += e_p
                if axi5:
                    e_t = M.beat_tags(addr, self.NB, self.hash_seed, False, b['tagop'])
                    e_u = M.beat_tagupd(addr, self.NB, self.hash_seed, b['tagop'])
                    if wtag != e_t or wtagupd != e_u:
                        self._merr(f'W addr {addr:#x}: WTAG {wtag:#x}/{wtagupd:#x} != {e_t:#x}/{e_u:#x}')
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
                q = b_q.get(int(d.m_bid.value))
                if q:
                    a, w, uq, tagop = q.popleft()
                    e_tr = M.f_rsb(M.f_sb(a, self.hash_seed)) if (tp and w and w.sb) else 0
                    if tp and int(d.m_btrace.value) != e_tr:
                        self._merr(f'B ID {int(d.m_bid.value):#x} AW {a:#x}: BTRACE != {e_tr}')
                    if axi5:
                        if int(d.m_bidunq.value) != uq:
                            self._merr(f'B ID {int(d.m_bid.value):#x} AW {a:#x}: BIDUNQ != {uq}')
                        uq_out['aw'][int(d.m_bid.value)].pop(0)
                        e_m = M.f_btagmatch(a, self.hash_seed, tagop) if (w and w.mte) else 0
                        if int(d.m_btagmatch.value) != e_m:
                            self._merr(f'B ID {int(d.m_bid.value):#x} AW {a:#x}: BTAGMATCH != {e_m}')
                        self.stats[f'btagmatch{int(d.m_btagmatch.value)}'] += 1
                self.stats['b'] += 1
                wire_out -= 1
                if int(d.m_bresp.value) != M.OKAY:
                    self.stats['b_err'] += 1

    @staticmethod
    def _open_other(rd_q, rid) -> bool:
        """Another ID has a burst part-way through: this beat interleaves."""
        for k, q in rd_q.items():
            if k != rid and q and q[0]['n'] > 0:
                return True
        return False
