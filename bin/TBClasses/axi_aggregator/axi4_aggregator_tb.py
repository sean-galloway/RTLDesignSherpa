# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: axi4_aggregator_tb
# Purpose: Testbench class for axi4_wr_aggregator / axi4_rd_aggregator
#
# Author: sean galloway
# Created: 2026-10-28

"""Testbench for ``axi4_wr_aggregator`` (AW/W/B) and ``axi4_rd_aggregator`` (AR/R).

BFMs (all RDS-DV framework components, nothing hand-driven):
  * upstream (``fub_*``):  AXI4MasterWrite / AXI4MasterRead
  * downstream (``m_axi_*``): memory-backed, in-order AXI4SlaveWrite / AXI4SlaveRead
  * monitors: a GAXIMonitor on every channel on both sides. The downstream
    command monitor carries one extra one-bit field, ``agg``, bound to
    ``m_axi_aw_agg`` / ``m_axi_ar_agg``, so the sideband is sampled on the same
    handshake as the command it flags.
  * delay profiles: FlexConfigGen.DEFAULT_PROFILES through FlexRandomizer, one
    profile per side (valid delays on what that side drives, ready delays on
    what it receives).

Checker rules (every one is counted; see ``verdict``):
  1. every upstream command completes; writes land in the slave memory with the
     right bytes (whole image compared, so a stray write also fails); reads
     return the memory contents; one response per upstream command.
  2. the downstream command stream is a faithful re-encoding of the upstream
     one: an ``agg=1`` command is len 1, 2-beat aligned and is exactly the next
     two upstream single-beat commands at addr and addr+DW/8 with the same id
     and qualifiers; an ``agg=0`` command is the next upstream command unchanged.
  3. W: data/strobes identical, WLAST reframed per downstream command.
     B: each downstream B is replayed twice upstream for an aggregated write.
     R: the upstream burst of an aggregated read is two beats, RLAST on both.
  4. completeness: an eligible lo/hi pair accepted within HOLD_CYCLES+1 cycles
     of each other MUST have been aggregated (derivation in ``_check_cmds``).
  5. protocol: DUT-driven VALID/payload stable until READY (the framework's
     AXI4ComplianceChecker covers VALID_DROPPED only, not payload stability).
"""

import os
import random
from collections import Counter

import cocotb
from cocotb.triggers import ClockCycles, FallingEdge, Timer
from cocotb.utils import get_sim_time

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_field_configs import AXI4FieldConfigHelper
from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead, AXI4MasterWrite, AXI4SlaveRead, AXI4SlaveWrite,
)
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.shared.axi_burst import beat_addr, beat_lanes
from CocoTBFramework.components.shared.field_config import FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import DEFAULT_PROFILES
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel

from .agg_plan import Planner, INCR, QUAL_FIELDS

CMD_KEYS = ('id', 'addr', 'len', 'size', 'burst', 'lock') + QUAL_FIELDS
PERIOD_NS = 10
MEM_BYTES = 1 << 16

# (upstream profile, downstream profile) per random phase, by level
PROFILE_PAIRS = {
    'gate': [('backtoback', 'backtoback'), ('fast', 'constrained')],
    'func': [('backtoback', 'backtoback'), ('fast', 'constrained'), ('bursty', 'slow'),
             ('constrained', 'bursty'), ('stress', 'fast')],
    'full': [('backtoback', 'backtoback'), ('fast', 'fast'), ('mostly_zero', 'stress'),
             ('constrained', 'constrained'), ('bursty', 'bursty'), ('slow', 'backtoback'),
             ('stress', 'stress'), ('efficient', 'jittery'), ('balanced', 'mostly_zero'),
             ('moderate', 'fast'), ('backtoback', 'chaotic'), ('fixed1', 'heavy_pause')],
}
RANDOM_TXNS = {'gate': 30, 'func': 60, 'full': 120}


class Axi4AggregatorTB(TBBase):
    """One class for both flavours; ``AGG_KIND`` = ``wr`` | ``rd``."""

    def __init__(self, dut):
        super().__init__(dut)
        env = os.environ
        self.kind = env.get('AGG_KIND', 'wr')
        self.wr = self.kind == 'wr'
        self.DW = self.convert_to_int(env.get('TEST_DATA_WIDTH', '32'))
        self.AW = self.convert_to_int(env.get('TEST_ADDR_WIDTH', '32'))
        self.IW = self.convert_to_int(env.get('TEST_ID_WIDTH', '4'))
        self.UW = self.convert_to_int(env.get('TEST_USER_WIDTH', '1'))
        self.HOLD = self.convert_to_int(env.get('TEST_HOLD_CYCLES', '4'))
        self.DEPTH = self.convert_to_int(env.get('TEST_AGG_FIFO_DEPTH', '4'))
        self.B = self.DW // 8
        self.full = self.B.bit_length() - 1
        self.mutate = env.get('AGG_TB_MUTATE', '0') == '1'
        self.clk = dut.aclk
        self.cmd = 'aw' if self.wr else 'ar'
        self.errors = []
        self.hwm = 0
        self.count = Counter()
        self.mem = MemoryModel(num_lines=MEM_BYTES // self.B, bytes_per_line=self.B, log=self.log)
        self.shadow = bytearray(MEM_BYTES)
        self.up = {}      # channel -> list of dict records (fub side)
        self.dn = {}      # channel -> list of dict records (m_axi side)
        self._build_bfms()
        self.log.info(f"AGG TB kind={self.kind} DW={self.DW} HOLD={self.HOLD} DEPTH={self.DEPTH}")

    # ---- construction -------------------------------------------------------

    def _build_bfms(self):
        common = dict(data_width=self.DW, id_width=self.IW, addr_width=self.AW,
                      user_width=self.UW, multi_sig=True, log=self.log, timeout_cycles=20000)
        if self.wr:
            self.master = AXI4MasterWrite(dut=self.dut, clock=self.clk, prefix='fub_', **common)
            self.slave = AXI4SlaveWrite(dut=self.dut, clock=self.clk, prefix='m_axi_',
                                        memory_model=self.mem, response_delay=1, **common)
            self.m_valid_ch = (self.master.aw_channel, self.master.w_channel)
            self.m_ready_ch = (self.master.b_channel,)
            self.s_ready_ch = (self.slave.aw_channel, self.slave.w_channel)
            self.s_valid_ch = (self.slave.b_channel,)
        else:
            for a in range(0, MEM_BYTES, 4096):      # distinct, seeded read contents
                chunk = random.Random(a).randbytes(4096)
                self.shadow[a:a + 4096] = chunk
                self.mem.write(a, bytearray(chunk))
            self.master = AXI4MasterRead(dut=self.dut, clock=self.clk, prefix='fub_', **common)
            self.slave = AXI4SlaveRead(dut=self.dut, clock=self.clk, prefix='m_axi_',
                                       memory_model=self.mem, response_delay=1, **common)
            self.m_valid_ch = (self.master.ar_channel,)
            self.m_ready_ch = (self.master.r_channel,)
            self.s_ready_ch = (self.slave.ar_channel,)
            self.s_valid_ch = (self.slave.r_channel,)

    def _add_monitors(self):
        """Built after reset is released (handbook bfm-usage: armed-in-constructor
        samplers judge the reset window)."""
        h, a, i, u = AXI4FieldConfigHelper, self.AW, self.IW, self.UW
        cfgs = {
            'aw': h.create_aw_field_config(i, a, u), 'ar': h.create_ar_field_config(i, a, u),
            'w': h.create_w_field_config(self.DW, u), 'r': h.create_r_field_config(i, self.DW, u),
            'b': h.create_b_field_config(i, u),
        }
        chans = ('aw', 'w', 'b') if self.wr else ('ar', 'r')
        for side, prefix, store in (('fub', 'fub_', self.up), ('m_axi', 'm_axi_', self.dn)):
            for ch in chans:
                cfg = cfgs[ch]
                if side == 'm_axi' and ch == self.cmd:
                    cfg = h.create_aw_field_config(i, a, u) if self.wr else h.create_ar_field_config(i, a, u)
                    cfg.add_field(FieldDefinition(name='agg', bits=1, default=0, format='bin',
                                                  description='aggregated-pair sideband'))
                store[ch] = []
                mon = GAXIMonitor(dut=self.dut, title=f'{side}_{ch}_mon', prefix=prefix,
                                  clock=self.clk, field_config=cfg, pkt_prefix=ch, multi_sig=True,
                                  is_slave=False, mode='skid', log=self.log,
                                  protocol_type=f'axi4_{ch}_slave')
                mon.add_callback(self._recorder(store[ch]))

    def _recorder(self, sink):
        def cb(pkt):
            rec = {k: int(v) for k, v in pkt.fields.items()}
            rec['t'] = int(get_sim_time('ns') // PERIOD_NS)   # cycle index; floor, not round (samples sit mid-cycle)
            sink.append(rec)
        return cb

    # ---- mandatory ------------------------------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=PERIOD_NS, units='ns')
        await self.assert_reset()
        await ClockCycles(self.clk, 10)
        await self.deassert_reset()
        await ClockCycles(self.clk, 5)
        self._add_monitors()
        self._start_stability()
        await ClockCycles(self.clk, 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- protocol stability observer -----------------------------------------

    def _start_stability(self):
        d = self.dut
        watch = [(f'm_axi_{self.cmd}', f'm_axi_{self.cmd}valid', f'm_axi_{self.cmd}ready',
                  [s for s in self._cmd_sigs('m_axi_')])]
        if self.wr:
            watch += [('m_axi_w', 'm_axi_wvalid', 'm_axi_wready',
                       ['m_axi_wdata', 'm_axi_wstrb', 'm_axi_wlast', 'm_axi_wuser']),
                      ('fub_b', 'fub_bvalid', 'fub_bready', ['fub_bid', 'fub_bresp', 'fub_buser'])]
        else:
            watch += [('fub_r', 'fub_rvalid', 'fub_rready',
                       ['fub_rid', 'fub_rdata', 'fub_rresp', 'fub_rlast', 'fub_ruser'])]
        self.hs_seen = Counter()
        for name, v, r, pl in watch:
            sigs = [getattr(d, s) for s in pl]
            cocotb.start_soon(self._stable(name, getattr(d, v), getattr(d, r), sigs))

    def _cmd_sigs(self, p):
        c = self.cmd
        s = [f'{p}{c}{f}' for f in ('id', 'addr', 'len', 'size', 'burst', 'lock', 'cache',
                                   'prot', 'qos', 'region', 'user')]
        return s + [f'{p}{c}_agg']

    async def _stable(self, name, valid, ready, sigs):
        """Once VALID is up without READY, the next cycle must hold VALID and the
        same payload. Sampled 3 ns after the falling edge, i.e. after the slave
        BFM's READY write and the DUT's combinational settle."""
        prev = None
        while True:
            await FallingEdge(self.clk)
            await Timer(3, 'ns')
            if not (valid.value.is_resolvable and ready.value.is_resolvable):
                prev = None
                continue
            v, r = int(valid.value), int(ready.value)
            cur = tuple(int(s.value) for s in sigs)
            if prev is not None:
                self.count[f'stab_{name}'] += 1
                if not v or cur != prev:
                    self._fail(f"{name}: payload/VALID changed while waiting for READY "
                               f"(valid {v}, {prev} -> {cur})")
            if v and r:
                self.hs_seen[name] += 1
            prev = cur if (v and not r) else None

    # ---- helpers --------------------------------------------------------------

    def _fail(self, msg):
        if len(self.errors) < 40:
            self.errors.append(msg)
        self.log.error(msg)

    def set_profile(self, up, down):
        """Upstream side: valid delays on what fub drives, ready delays on B/R.
        Downstream side: ready delays on AW/AR/W, valid delays on B/R."""
        mv = lambda n: FlexRandomizer({'valid_delay': DEFAULT_PROFILES[n]})
        mr = lambda n: FlexRandomizer({'ready_delay': DEFAULT_PROFILES[n]})
        for ch in self.m_valid_ch:
            ch.set_randomizer(mv(up))
        for ch in self.m_ready_ch:
            ch.set_randomizer(mr(up))
        for ch in self.s_ready_ch:
            ch.set_randomizer(mr(down))
        for ch in self.s_valid_ch:
            ch.set_randomizer(mv(down))

    def exp_beats(self, t):
        """[(bus word, wstrb, last)] the master BFM puts on W for this write."""
        out = []
        nb = 1 << t.size
        for i, word in enumerate(t.data):
            strb, lane = beat_lanes(t.addr, i, t.size, t.burst, t.length, self.B)
            if t.strb is not None:
                strb = t.strb
            if nb < self.B:
                word = (word & ((1 << (8 * nb)) - 1)) << (8 * lane)
            out.append((word, strb, int(i == t.length)))
        return out

    def _apply_shadow(self, t):
        for i, (word, strb, _l) in enumerate(self.exp_beats(t)):
            base = beat_addr(t.addr, i, t.size, t.burst, t.length) // self.B * self.B
            for k in range(self.B):
                if (strb >> k) & 1:
                    self.shadow[base + k] = (word >> (8 * k)) & 0xFF

    # ---- driving --------------------------------------------------------------

    async def _do(self, t):
        kw = dict(id=t.id, size=t.size, burst_type=t.burst, lock=t.lock, **t.quals())
        if self.wr:
            if t.strb is not None:
                kw['strb'] = t.strb
            t.result = await self.master.write_transaction(t.addr, t.data, **kw)
        else:
            try:
                t.result = await self.master.read_transaction(t.addr, burst_len=t.length + 1, **kw)
            except Exception as e:                      # noqa: BLE001 - recorded, then judged
                t.error = f"read raised: {e}"

    async def run_group(self, txns):
        tasks = [cocotb.start_soon(self._do(t)) for t in txns]
        for tk in tasks:
            await tk
        await ClockCycles(self.clk, 10)

    def mark(self):
        return {('u', k): len(v) for k, v in self.up.items()} | {('d', k): len(v) for k, v in self.dn.items()}

    def sl(self, side, ch, mark):
        store = self.up if side == 'u' else self.dn
        return store[ch][mark[(side, ch)]:]

    # ---- the checks -------------------------------------------------------------

    def check_phase(self, name, mark, txns, expect_agg=None, latency=False):
        e0 = len(self.errors)
        self.hwm = max(self.hwm, max((t.addr + (t.length + 1) * self.B for t in txns if not t.oor), default=0))
        up_cmd, dn_cmd = self.sl('u', self.cmd, mark), self.sl('d', self.cmd, mark)
        by_addr = {t.addr: t for t in txns}
        self._check_completion(name, txns)
        self._check_upstream_matches_plan(name, up_cmd, by_addr)
        agg = self._check_cmds(name, up_cmd, dn_cmd)
        if expect_agg is not None:
            self.count['directed_agg_checked'] += 1
            if agg != expect_agg:
                self._fail(f"{name}: {agg} aggregation(s), expected {expect_agg}")
        if latency:
            self._check_latency(name, up_cmd, dn_cmd)
        if self.wr:
            self._check_wr_channels(name, mark, up_cmd, dn_cmd, by_addr)
            self._check_memory(name, up_cmd, by_addr)
        else:
            self._check_rd_channels(name, mark, up_cmd, dn_cmd, txns)
        self.log.info(f"phase '{name}': up={len(up_cmd)} dn={len(dn_cmd)} agg={agg} "
                      f"{'ok' if len(self.errors) == e0 else 'FAILED'}")
        return agg

    def _check_completion(self, name, txns):
        for t in txns:
            self.count['txn_issued'] += 1
            if t.error:
                self._fail(f"{name}: {t.label}@0x{t.addr:X} id{t.id}: {t.error}")
                continue
            if self.wr:
                r = t.result or {}
                want = 2 if t.oor else 0
                if r.get('response') != want or r.get('id') != t.id:
                    self._fail(f"{name}: {t.label}@0x{t.addr:X} B id/resp {r.get('id')}/{r.get('response')}"
                               f" expected {t.id}/{want}: {r.get('error', '')}")
                    continue
            else:
                if t.result is None:
                    self._fail(f"{name}: {t.label}@0x{t.addr:X} read never returned")
                    continue
                if t.size == self.full:
                    exp = [int.from_bytes(self.shadow[t.addr + k * self.B:t.addr + (k + 1) * self.B], 'little')
                           for k in range(t.length + 1)]
                    if list(t.result) != exp:
                        self._fail(f"{name}: {t.label}@0x{t.addr:X} returned "
                                   f"{[hex(x) for x in t.result]} expected {[hex(x) for x in exp]}")
                        continue
                    self.count['read_beats_data_ok'] += len(exp)
                elif len(t.result) != t.length + 1:
                    self._fail(f"{name}: narrow read beat count {len(t.result)}")
                    continue
            self.count['txn_completed'] += 1

    def _check_upstream_matches_plan(self, name, up_cmd, by_addr):
        """The upstream monitor must have seen exactly what the plan sent."""
        if len(up_cmd) != len(by_addr):
            self._fail(f"{name}: upstream monitor saw {len(up_cmd)} commands, plan sent {len(by_addr)}")
        for c in up_cmd:
            t = by_addr.get(c['addr'])
            exp = None if t is None else dict(id=t.id, addr=t.addr, len=t.length, size=t.size,
                                              burst=t.burst, lock=t.lock, **t.quals())
            if exp is None or any(c[k] != exp[k] for k in CMD_KEYS):
                self._fail(f"{name}: upstream command {c} not in plan ({exp})")
            self.count['up_cmds_vs_plan'] += 1

    def _single(self, c):
        return (c['len'] == 0 and c['size'] == self.full and c['burst'] == INCR and c['lock'] == 0
                and (c['cache'] & 2) != 0)

    def _is_pair(self, lo, hi):
        return (self._single(lo) and self._single(hi) and lo['addr'] % (2 * self.B) == 0
                and hi['addr'] == lo['addr'] + self.B and lo['id'] == hi['id']
                and all(lo[q] == hi[q] for q in QUAL_FIELDS))

    def _check_cmds(self, name, up, dn):
        """Walk the downstream stream against the upstream one; returns #agg."""
        i, agg = 0, 0
        used = []                                  # per dn command: number of upstream consumed
        for j, d in enumerate(dn):
            self.count['dn_cmds'] += 1
            if i >= len(up):
                self._fail(f"{name}: downstream command {j} {d} has no upstream command")
                return agg
            if d['agg']:
                agg += 1
                self.count['dn_agg'] += 1
                if i + 1 >= len(up):
                    self._fail(f"{name}: aggregated command {j} with only one upstream command left")
                    return agg
                lo, hi = up[i], up[i + 1]
                ok = (d['len'] == 1 and d['addr'] % (2 * self.B) == 0 and d['size'] == self.full
                      and d['burst'] == INCR and d['lock'] == 0 and self._is_pair(lo, hi)
                      and d['addr'] == lo['addr']
                      and all(d[k] == lo[k] for k in ('id', 'size') + QUAL_FIELDS))
                if not ok:
                    self._fail(f"{name}: dn cmd {j} agg=1 {d} is not the merge of up {lo} + {hi}")
                    return agg
                used.append(2)
                i += 2
            else:
                self.count['dn_plain'] += 1
                if any(d[k] != up[i][k] for k in CMD_KEYS):
                    self._fail(f"{name}: dn cmd {j} agg=0 {d} != up cmd {up[i]}")
                    return agg
                used.append(1)
                i += 1
        if i != len(up):
            self._fail(f"{name}: {len(up) - i} upstream command(s) never issued downstream")
        # completeness: lo accepted at t, hi accepted at u <= t + HOLD + 1 cannot be unaggregated.
        # lo is captured at the end of cycle t, held from t+1 with a counter that reads k at
        # t+1+k and flushes (unpaired) at the earliest t+1+HOLD; a non-paired next command is
        # only evaluated the cycle after the flush handshake, i.e. u >= t+HOLD+2.
        if self.HOLD > 0:
            k = 0
            for n in used:
                if k + 1 < len(up) and self._is_pair(up[k], up[k + 1]):
                    gap = up[k + 1]['t'] - up[k]['t']
                    if gap <= self.HOLD + 1:
                        self.count['pair_timing_checks'] += 1
                        if n != 2:
                            self._fail(f"{name}: eligible pair at up[{k}] accepted {gap} cycles apart "
                                       f"(<= HOLD+1) but not aggregated")
                k += n
        else:
            if agg:
                self._fail(f"{name}: HOLD_CYCLES=0 but {agg} aggregation(s)")
        return agg

    def _check_latency(self, name, up, dn):
        # RTL contract: capture-to-presentation is exactly HOLD+1 cycles (pass-through at HOLD=0);
        # the BFM's ready adds up to 2 more before the handshake the monitor sees.
        lo_b = self.HOLD + 1 if self.HOLD > 0 else 0
        hi_b = lo_b + 3
        for u, d in zip(up, dn):
            lat = d['t'] - u['t']
            self.count['latency_checks'] += 1
            self.count['max_lone_latency'] = max(self.count['max_lone_latency'], lat)
            if not lo_b <= lat <= hi_b:
                self._fail(f"{name}: lone command issued {lat} cycles after acceptance, expected {lo_b}..{hi_b}")

    # ---- write channels ----------------------------------------------------------

    def _check_wr_channels(self, name, mark, up_cmd, dn_cmd, by_addr):
        up_w, dn_w = self.sl('u', 'w', mark), self.sl('d', 'w', mark)
        up_b, dn_b = self.sl('u', 'b', mark), self.sl('d', 'b', mark)
        # upstream W stream == plan beats in upstream command order
        exp_up = []
        for c in up_cmd:
            t = by_addr.get(c['addr'])
            if t is not None:
                exp_up += self.exp_beats(t)
        got_up = [(w['data'], w['strb'], w['last']) for w in up_w]
        if got_up != exp_up:
            self._fail(f"{name}: upstream W stream differs from plan ({len(got_up)} vs {len(exp_up)} beats)")
        self.count['up_w_beats'] += len(got_up)
        # downstream W == same data/strobes, WLAST reframed per downstream command
        exp_dn, idx = [], 0
        for d in dn_cmd:
            n = d['len'] + 1
            for k, (w, s, _l) in enumerate(exp_up[idx:idx + n]):
                exp_dn.append((w, s, int(k == n - 1)))
            idx += n
        got_dn = [(w['data'], w['strb'], w['last']) for w in dn_w]
        if got_dn != exp_dn:
            bad = next((n for n, (a, b) in enumerate(zip(got_dn, exp_dn)) if a != b), min(len(got_dn), len(exp_dn)))
            self._fail(f"{name}: downstream W stream differs at beat {bad} "
                       f"(got {len(got_dn)} beats, expected {len(exp_dn)})")
        self.count['dn_w_beats'] += len(got_dn)
        self.count['wlast_reframed'] += sum(1 for d in dn_cmd if d['agg'])
        # B: one per upstream command, an aggregated downstream B replayed twice
        exp_b_up = [(c['id'], 2 if (by_addr.get(c['addr']) and by_addr[c['addr']].oor) else 0) for c in up_cmd]
        got_b_up = [(b['id'], b['resp']) for b in up_b]
        got_b_dn = [(b['id'], b['resp']) for b in dn_b]
        if len(got_b_dn) != len(dn_cmd):
            self._fail(f"{name}: {len(got_b_dn)} downstream B for {len(dn_cmd)} downstream commands")
        replay = []
        for d, b in zip(dn_cmd, got_b_dn):
            replay += [b, b] if d['agg'] else [b]
        if got_b_up != replay:
            self._fail(f"{name}: upstream B stream is not the downstream B replayed per agg flag "
                       f"({got_b_up} vs {replay})")
        if got_b_up != exp_b_up:
            self._fail(f"{name}: upstream B (id,resp) {got_b_up} != expected {exp_b_up}")
        self.count['up_b'] += len(got_b_up)
        self.count['dn_b'] += len(got_b_dn)
        self.count['b_replayed_twice'] += sum(1 for d in dn_cmd if d['agg'])

    def _check_memory(self, name, up_cmd, by_addr):
        for c in up_cmd:
            t = by_addr.get(c['addr'])
            if t is not None and not t.oor:
                self._apply_shadow(t)
        self._compare_image(name, min(MEM_BYTES, self.hwm + 512))

    def _compare_image(self, name, n):
        """Compare the first n bytes of slave memory with the expected image; the
        512 B past the planner's high-water mark catch a stray write."""
        img = bytes(self.mem.read(0, n))
        if img != bytes(self.shadow[:n]):
            bad = next(i for i in range(n) if img[i] != self.shadow[i])
            self._fail(f"{name}: slave memory differs from the expected image at 0x{bad:X} "
                       f"(got 0x{img[bad]:02X}, expected 0x{self.shadow[bad]:02X})")
        self.count['mem_bytes_compared'] += n

    # ---- read channels -----------------------------------------------------------

    def _exp_rbeats(self, cmds):
        out = []
        for c in cmds:
            for k in range(c['len'] + 1):
                a = c['addr'] + k * (1 << c['size'])
                word = None
                if c['size'] == self.full and c['burst'] == INCR:
                    word = int.from_bytes(self.shadow[a:a + self.B], 'little')
                out.append((c['id'], word, int(k == c['len'])))
        return out

    def _check_rd_channels(self, name, mark, up_cmd, dn_cmd, txns):
        up_r, dn_r = self.sl('u', 'r', mark), self.sl('d', 'r', mark)
        got_up = [(r['id'], r['data'], r['last'], r['resp']) for r in up_r]
        exp_up = self._exp_rbeats(up_cmd)
        # an aggregated pair is two single-beat upstream commands: RLAST on both beats
        if len(got_up) != len(exp_up) or any(
                g[0] != e[0] or g[2] != e[2] or g[3] != 0 or (e[1] is not None and g[1] != e[1])
                for g, e in zip(got_up, exp_up)):
            self._fail(f"{name}: upstream R stream differs from expected "
                       f"({len(got_up)} vs {len(exp_up)} beats)")
        self.count['up_r_beats'] += len(got_up)
        self.count['rlast_both_beats'] += sum(1 for d in dn_cmd if d['agg'])
        got_dn = [(r['id'], r['data'], r['last'], r['resp']) for r in dn_r]
        exp_dn = self._exp_rbeats(dn_cmd)
        if len(got_dn) != len(exp_dn) or any(
                g[0] != e[0] or g[2] != e[2] or g[3] != 0 or (e[1] is not None and g[1] != e[1])
                for g, e in zip(got_dn, exp_dn)):
            self._fail(f"{name}: downstream R stream differs from expected "
                       f"({len(got_dn)} vs {len(exp_dn)} beats)")
        if [g[1] for g in got_up] != [g[1] for g in got_dn]:
            self._fail(f"{name}: upstream R data is not the downstream R data")
        self.count['dn_r_beats'] += len(got_dn)

    # ---- the suite ---------------------------------------------------------------

    async def run_suite(self, level):
        seed = self.convert_to_int(os.environ.get('SEED', '1'))
        rng = random.Random(seed)
        P = Planner(self.DW, MEM_BYTES, rng)
        wr = self.wr
        self.log.info(f"AGG suite kind={self.kind} level={level} seed={seed} "
                      f"DW={self.DW} HOLD={self.HOLD} DEPTH={self.DEPTH}")
        # directed: upstream back-to-back, downstream never stalls
        self.set_profile('backtoback', 'backtoback')
        self.master.pipelined = True
        for name, txns, exp in P.directed(wr):
            exp = 0 if self.HOLD == 0 else exp
            if self.mutate and name == 'lo0 lo1 hi0 hi1':
                exp = 2                      # deliberately wrong: mutation check of this checker
            m = self.mark()
            await self.run_group(txns)
            self.check_phase(name, m, txns, expect_agg=exp)
        for name, txns, exp in P.lone_cases(wr):
            m = self.mark()
            await self.run_group(txns)
            self.check_phase(name, m, txns, expect_agg=0, latency=True)
        # random: mixed streams per delay profile, backpressure on both sides
        self.master.pipelined = False
        ids = list(range(min(4, 1 << self.IW)))
        for up, down in PROFILE_PAIRS[level]:
            self.set_profile(up, down)
            txns = []
            m = self.mark()
            for grp in P.random_groups(wr, RANDOM_TXNS[level], ids):
                txns += grp
                await self.run_group(grp)
            self.check_phase(f"random {up}/{down}", m, txns)
        await ClockCycles(self.clk, 20)
        if wr:
            self._compare_image('final full image', MEM_BYTES)
        return self.verdict()

    def verdict(self):
        c = self.count
        stab = sum(v for k, v in c.items() if k.startswith('stab_'))
        hs = dict(self.hs_seen)
        up_hs = hs.get(f'm_axi_{self.cmd}', 0)
        # the independent handshake counter on the downstream command must equal the monitor's
        if up_hs != c['dn_cmds']:
            self._fail(f"downstream command handshakes: observer {up_hs} != monitor records {c['dn_cmds']}")
        must = ['txn_issued', 'txn_completed', 'dn_cmds', 'dn_plain', 'up_cmds_vs_plan',
                'directed_agg_checked', 'latency_checks']
        must += ['up_w_beats', 'dn_w_beats', 'up_b', 'dn_b', 'mem_bytes_compared'] if self.wr \
            else ['up_r_beats', 'dn_r_beats', 'read_beats_data_ok']
        if self.HOLD > 0:
            must += ['dn_agg', 'pair_timing_checks'] + (['wlast_reframed', 'b_replayed_twice'] if self.wr
                                                          else ['rlast_both_beats'])
        for k in must:
            if c[k] == 0:
                self._fail(f"verdict: counter '{k}' is zero -- that check never ran")
        if stab == 0:
            self._fail("verdict: protocol stability observer made no checks")
        if self.HOLD == 0 and c['dn_agg']:
            self._fail("verdict: aggregations seen with HOLD_CYCLES=0")
        if c['txn_completed'] != c['txn_issued']:
            self._fail(f"verdict: {c['txn_issued'] - c['txn_completed']} transaction(s) did not complete cleanly")
        self.log.info(f"VERDICT kind={self.kind} DW={self.DW} HOLD={self.HOLD} DEPTH={self.DEPTH}: "
                      f"mismatches={len(self.errors)} | issued={c['txn_issued']} completed={c['txn_completed']} "
                      f"dn_cmds={c['dn_cmds']} agg={c['dn_agg']} plain={c['dn_plain']} "
                      f"pair_timing_checks={c['pair_timing_checks']} directed_checked={c['directed_agg_checked']} "
                      f"latency_checks={c['latency_checks']} max_lone_latency={c['max_lone_latency']} "
                      + (f"up_w={c['up_w_beats']} dn_w={c['dn_w_beats']} up_b={c['up_b']} dn_b={c['dn_b']} "
                         f"b_replayed={c['b_replayed_twice']} wlast_reframed={c['wlast_reframed']} "
                         f"mem_bytes={c['mem_bytes_compared']}" if self.wr else
                         f"up_r={c['up_r_beats']} dn_r={c['dn_r_beats']} rlast_both={c['rlast_both_beats']} "
                         f"read_data_ok={c['read_beats_data_ok']}")
                      + f" | stab_checks={stab} handshakes={hs}")
        return not self.errors
