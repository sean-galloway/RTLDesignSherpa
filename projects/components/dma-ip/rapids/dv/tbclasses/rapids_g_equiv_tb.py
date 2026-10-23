# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_g_equiv_tb
# Purpose: rapids-g equivalence testbench (rapids TASK-034): the FSM
#          scheduler (side f) and the gatling-sequenced scheduler_g (side g)
#          on the same descriptors must ask the same of their engines.
#
# Author: sean galloway
# Created: 2026-10-21

"""Equivalence of the FSM scheduler and scheduler_g + firmware.

rapids_g_equiv_tb_top holds NUM_CHANNELS of each. Both sides get the same
descriptor lists. Each side has its own engine models with their own random
latencies, so the two run at different speeds; what each side asks for may
not differ:

  * every read and write command, as (address, beats) at the moment an
    engine takes it, in order;
  * every packet record, (bytes, offset), in order;
  * every MonBus packet (all 128 bits), in order;
  * the final channel state.

The engine burst sizes depend only on the address, so a difference in a
sequence is a difference in what the scheduler computed (beat totals, address
advance, EXT run bases), never in timing.

Driving: one coroutine per cycle writes every input at the falling edge, then
samples in ReadOnly and steps every model. The ports are packed per-channel
arrays, so one writer avoids read-modify-write races between models.
"""

import os
import random
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase

SIDES = ('f', 'g')
ST_IDLE, ST_FETCH, ST_XFER, ST_COMPLETE, ST_NEXT, ST_ERROR = 0x01, 0x02, 0x04, 0x08, 0x10, 0x20
DESC_TYPE_EXT = 1
DESC_ALG_LO = 217          # next-address selector, chunk 0 [224:217] (rapids TASK-035)


# ---------------------------------------------------------------------------
# Descriptors (rapids_pkg layout)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Desc:
    """One descriptor: chunk 0 and, for TYPE=EXT, chunk 1."""
    packet: int
    ext: int = 0


def make_desc(src: int, dst: int, length: int, next_ptr: int = 0, valid: bool = True,
              gen_irq: bool = False, last: bool = True, ext: Optional[dict] = None,
              alg: int = 0) -> Desc:
    """alg: the next-address selector, chunk 0 [224:217] (rapids TASK-035)."""
    p = (src & (2**64 - 1)) | ((dst & (2**64 - 1)) << 64) | ((length & 0xFFFFFFFF) << 128)
    p |= (next_ptr & 0xFFFFFFFF) << 160
    p |= int(valid) << 192 | int(gen_irq) << 193 | int(last) << 194
    p |= (alg & 0xFF) << DESC_ALG_LO
    chunk1 = 0
    if ext is not None:
        p |= DESC_TYPE_EXT << 210
        chunk1 = pack_ext(**ext)
    return Desc(packet=p, ext=chunk1)


def pack_ext(rd_s0=0, rd_s1=0, rd_w0=0, rd_w1=0, rd_inner=0,
             wr_s0=0, wr_s1=0, wr_w0=0, wr_w1=0, wr_inner=0) -> int:
    """rapids_pkg::descriptor_ext_t (strides signed 32-bit, wraps log2, inner 16-bit)."""
    m32 = 0xFFFFFFFF
    v = (rd_s0 & m32) | ((rd_s1 & m32) << 32)
    v |= (rd_inner & 0xFFFF) << 64 | (rd_w0 & 0x3F) << 80 | (rd_w1 & 0x3F) << 86
    v |= (wr_s0 & m32) << 96 | (wr_s1 & m32) << 128
    v |= (wr_inner & 0xFFFF) << 160 | (wr_w0 & 0x3F) << 176 | (wr_w1 & 0x3F) << 182
    return v


def morton_xy(k: int) -> Tuple[int, int]:
    """Z-order position k -> (x, y): x is k's even bits, y its odd bits."""
    x = y = 0
    for i in range(16):
        x |= ((k >> (2 * i)) & 1) << i
        y |= ((k >> (2 * i + 1)) & 1) << i
    return x, y


# ---------------------------------------------------------------------------
# Per-side, per-channel state
# ---------------------------------------------------------------------------

@dataclass
class Engine:
    """One direction's engine model."""
    busy: int = 0            # cycles until the done strobe
    n: int = 0               # beats of the burst in flight
    strobe: int = 0          # done strobe this cycle (beats), 0 = none
    commits: List[Tuple[int, int]] = field(default_factory=list)   # (due cycle, beats)
    commit: int = 0


@dataclass
class Chan:
    queue: List[Desc] = field(default_factory=list)
    head: Optional[Desc] = None
    rd: Engine = field(default_factory=Engine)
    wr: Engine = field(default_factory=Engine)
    rd_cmds: List[Tuple[int, int]] = field(default_factory=list)
    wr_cmds: List[Tuple[int, int]] = field(default_factory=list)
    rd_pkts: List[Tuple[int, int]] = field(default_factory=list)
    wr_pkts: List[Tuple[int, int]] = field(default_factory=list)
    mons: List[int] = field(default_factory=list)
    states: List[int] = field(default_factory=list)   # distinct states, in order (CH_STATE)
    rd_error_after: Optional[int] = None    # inject sched_rd_error after this many read commands
    rd_error: int = 0
    err_cycle: Optional[int] = None         # cycle the injected error was driven
    err_to_error: Optional[int] = None      # cycles from it to CH_ERROR
    cmds_in_error: int = 0                  # commands taken while in CH_ERROR (must stay 0)
    skip: List[Tuple[str, int, int]] = field(default_factory=list)  # (what, from, to) not compared
    fetches: int = 0                         # entries into CH_FETCH_DESC
    reset_at: Optional[Tuple[int, int]] = None   # (k-th fetch, state): reset this side there
    reset_left: int = 0
    reset_mark: Optional[Dict[str, int]] = None
    fetch_mark: Dict[str, int] = field(default_factory=dict)
    after_reset: List[Desc] = field(default_factory=list)   # queued once the planned reset ends
    was_reset: bool = False
    skip_from: Dict[str, int] = field(default_factory=dict)  # the k-th descriptor's FETCH mark
    post_reset: Dict[str, int] = field(default_factory=dict) # lengths when the reset ended
    state: int = ST_IDLE
    idle: bool = True


class RapidsGEquivTB(TBBase):
    """FSM scheduler vs scheduler_g + firmware, side by side."""

    def __init__(self, dut):
        super().__init__(dut)
        self.N = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '4'))
        self.harts = self.convert_to_int(os.environ.get('TEST_NUM_HARTS', str(self.N)))
        self.DW = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '256'))
        self.lanes = self.DW // 8
        self.off_w = self.lanes.bit_length() - 1
        self.seed = self.convert_to_int(os.environ.get('SEED', '1'))
        self.rng = random.Random(self.seed)
        self.lat_rng = {s: random.Random(self.seed * 7 + i) for i, s in enumerate(SIDES)}
        self.ch = {s: [Chan() for _ in range(self.N)] for s in SIDES}
        self.pkt_ready = {s: [1] * self.N for s in SIDES}
        self.enable = (1 << self.N) - 1
        self.fixed_lat: Optional[int] = None    # perf: every engine burst takes this many cycles
        self.reset_mask = {s: 0 for s in SIDES}
        self.cycle = 0
        self.log.info(f"rapids-g equivalence: {self.N} channels, DW {self.DW}, seed {self.seed}")

    # -- the three mandatory methods -----------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', 10, 'ns')
        self.dut.cfg_channel_enable.value = 0
        self.dut.f_cfg_channel_reset.value = 0
        self.dut.g_cfg_channel_reset.value = 0
        self.dut.cfg_sched_timeout_cycles.value = 100000
        self.dut.cfg_sched_timeout_limit.value = 0
        self.dut.cfg_sched_timeout_enable.value = 0
        for s in SIDES:
            for sig in ('desc_valid', 'desc_packet', 'desc_ext', 'rd_pkt_ready', 'wr_pkt_ready',
                        'wr_ready', 'rd_done', 'rd_done_beats', 'wr_done', 'wr_done_beats',
                        'wr_commit', 'wr_commit_beats', 'rd_error', 'wr_error'):
                getattr(self.dut, f"{s}_{sig}").value = 0
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # -- packed-array helpers --------------------------------------------------
    @staticmethod
    def _bit(v: int, i: int) -> int:
        return (v >> i) & 1

    @staticmethod
    def _field(v: int, i: int, w: int) -> int:
        return (v >> (i * w)) & ((1 << w) - 1)

    @staticmethod
    def _pack(vals, w: int) -> int:
        out = 0
        for i, x in enumerate(vals):
            out |= (x & ((1 << w) - 1)) << (i * w)
        return out

    # -- the cycle loop -----------------------------------------------------------
    def _burst(self, addr: int, beats: int) -> int:
        """Engine burst size: a function of the address only, so both sides agree."""
        return min(beats, 1 + ((addr >> self.off_w) % 7))

    def _drive(self):
        d = self.dut
        d.cfg_channel_enable.value = self.enable
        d.f_cfg_channel_reset.value = self.reset_mask['f']
        d.g_cfg_channel_reset.value = self.reset_mask['g']
        for s in SIDES:
            cs = self.ch[s]
            getattr(d, f"{s}_desc_valid").value = self._pack([int(c.head is not None) for c in cs], 1)
            getattr(d, f"{s}_desc_packet").value = self._pack([c.head.packet if c.head else 0 for c in cs], 256)
            getattr(d, f"{s}_desc_ext").value = self._pack([c.head.ext if c.head else 0 for c in cs], 256)
            getattr(d, f"{s}_rd_pkt_ready").value = self._pack(self.pkt_ready[s], 1)
            getattr(d, f"{s}_wr_pkt_ready").value = self._pack(self.pkt_ready[s], 1)
            getattr(d, f"{s}_wr_ready").value = (1 << self.N) - 1
            getattr(d, f"{s}_rd_done").value = self._pack([int(c.rd.strobe > 0) for c in cs], 1)
            getattr(d, f"{s}_rd_done_beats").value = self._pack([c.rd.strobe for c in cs], 32)
            getattr(d, f"{s}_wr_done").value = self._pack([int(c.wr.strobe > 0) for c in cs], 1)
            getattr(d, f"{s}_wr_done_beats").value = self._pack([c.wr.strobe for c in cs], 32)
            getattr(d, f"{s}_wr_commit").value = self._pack([int(c.wr.commit > 0) for c in cs], 1)
            getattr(d, f"{s}_wr_commit_beats").value = self._pack([c.wr.commit for c in cs], 32)
            getattr(d, f"{s}_rd_error").value = self._pack([c.rd_error for c in cs], 1)
            getattr(d, f"{s}_wr_error").value = 0

    def _engine_step(self, s: str, eng: Engine, valid: int, addr: int, beats: int, cmds, is_wr: bool):
        eng.strobe = 0
        eng.commit = 0
        if is_wr and eng.commits and eng.commits[0][0] <= self.cycle:
            eng.commit = eng.commits.pop(0)[1]
        if eng.busy > 0:
            eng.busy -= 1
            if eng.busy == 0:
                eng.strobe = eng.n
                if is_wr:
                    eng.commits.append((self.cycle + (self.fixed_lat or self.lat_rng[s].randint(1, 12)), eng.n))
                eng.busy = -1           # one cycle for the scheduler to take the strobe
            return
        if eng.busy == -1:
            eng.busy = 0
            return
        if valid and beats > 0:
            cmds.append((addr, beats))
            eng.n = self._burst(addr, beats)
            eng.busy = self.fixed_lat or self.lat_rng[s].randint(1, 6)

    def _sample(self):
        d = self.dut
        for s in SIDES:
            cs = self.ch[s]
            dvalid = int(getattr(d, f"{s}_desc_valid").value)
            dready = int(getattr(d, f"{s}_desc_ready").value)
            rdv = int(getattr(d, f"{s}_rd_valid").value)
            rda = int(getattr(d, f"{s}_rd_addr").value)
            rdb = int(getattr(d, f"{s}_rd_beats").value)
            wrv = int(getattr(d, f"{s}_wr_valid").value)
            wra = int(getattr(d, f"{s}_wr_addr").value)
            wrb = int(getattr(d, f"{s}_wr_beats").value)
            rpv = int(getattr(d, f"{s}_rd_pkt_valid").value)
            rpb = int(getattr(d, f"{s}_rd_pkt_bytes").value)
            rpo = int(getattr(d, f"{s}_rd_pkt_offset").value)
            wpv = int(getattr(d, f"{s}_wr_pkt_valid").value)
            wpb = int(getattr(d, f"{s}_wr_pkt_bytes").value)
            wpo = int(getattr(d, f"{s}_wr_pkt_offset").value)
            mv = int(getattr(d, f"{s}_mon_valid").value)
            mp = int(getattr(d, f"{s}_mon_packet").value)
            st = int(getattr(d, f"{s}_state").value)
            idl = int(getattr(d, f"{s}_idle").value)
            for i, c in enumerate(cs):
                pre = {w: len(getattr(c, w)) for w in ('rd_cmds', 'wr_cmds', 'rd_pkts', 'wr_pkts', 'mons', 'states')}
                # descriptor handshake completes at the coming rising edge
                if self._bit(dvalid, i) and self._bit(dready, i):
                    c.head = c.queue.pop(0) if c.queue else None
                elif c.head is None and c.queue and not self._bit(self.reset_mask[s], i):
                    c.head = c.queue.pop(0)
                if self._bit(rpv, i) and self.pkt_ready[s][i]:
                    c.rd_pkts.append((self._field(rpb, i, 32), self._field(rpo, i, self.off_w)))
                if self._bit(wpv, i) and self.pkt_ready[s][i]:
                    c.wr_pkts.append((self._field(wpb, i, 32), self._field(wpo, i, self.off_w)))
                if self._bit(mv, i):
                    c.mons.append(self._field(mp, i, 128))
                if self._bit(self.reset_mask[s], i):
                    # the engines take the channel reset too: a burst in flight
                    # is abandoned, its done strobe never comes
                    c.rd, c.wr = Engine(), Engine()
                    c.was_reset = True
                self._engine_step(s, c.rd, self._bit(rdv, i), self._field(rda, i, 64),
                                  self._field(rdb, i, 32), c.rd_cmds, False)
                self._engine_step(s, c.wr, self._bit(wrv, i), self._field(wra, i, 64),
                                  self._field(wrb, i, 32), c.wr_cmds, True)
                if c.state == ST_ERROR and (self._bit(rdv, i) or self._bit(wrv, i)):
                    c.cmds_in_error += 1
                c.rd_error = 0
                if c.rd_error_after is not None and len(c.rd_cmds) >= c.rd_error_after:
                    c.rd_error = 1
                    c.rd_error_after = None
                    c.err_cycle = self.cycle + 1        # driven at the next falling edge
                prev = c.state
                c.state = self._field(st, i, 7)
                if not c.states or c.states[-1] != c.state:
                    c.states.append(c.state)
                if c.state == ST_FETCH and prev != ST_FETCH:
                    c.fetches += 1
                    c.fetch_mark = pre          # before anything this cycle appended
                self._reset_step(s, i, c)
                if c.err_cycle is not None and c.err_to_error is None and c.state == ST_ERROR:
                    c.err_to_error = self.cycle - c.err_cycle
                c.idle = bool(self._bit(idl, i))

    def _reset_step(self, s: str, i: int, c: Chan):
        """A planned reset of this side's channel i: when its k-th descriptor
        reaches the planned state, hold the channel reset 4 cycles. What that
        descriptor did is left out of the comparison (how far it got is engine
        timing); the reset itself, and everything after, is not."""
        if c.reset_left:
            c.reset_left -= 1
            if c.reset_left == 0:
                self.reset_mask[s] &= ~(1 << i)
                for w in ('rd_cmds', 'wr_cmds', 'rd_pkts', 'wr_pkts', 'mons', 'states'):
                    c.skip.append((w, c.skip_from[w], len(getattr(c, w))))
                c.post_reset = {w: len(getattr(c, w)) for w in ('rd_cmds', 'wr_cmds')}
                c.queue.extend(c.after_reset)
                c.after_reset = []
            return
        if c.reset_at and c.fetches == c.reset_at[0] and c.state == c.reset_at[1]:
            c.reset_at = None
            c.reset_mark = {w: len(getattr(c, w)) for w in ('rd_cmds', 'wr_cmds', 'rd_pkts', 'wr_pkts', 'mons', 'states')}
            c.skip_from = dict(c.fetch_mark) if c.fetch_mark else dict(c.reset_mark)
            c.reset_left = 4
            self.reset_mask[s] |= 1 << i

    def _debug_seq(self):
        """DEBUG_SEQ=<channel>: log every firmware write into that channel's window."""
        ch = os.environ.get('DEBUG_SEQ')
        if ch is None:
            return
        ch = int(ch)
        d = self.dut.u_seq
        st = (int(self.dut.g_state.value) >> (7 * ch)) & 0x7F
        if st != getattr(self, '_dbg_st', None):
            g = self.dut.gen_ch[ch].u_g
            self.log.info(f"SEQ c{self.cycle} ch{ch} state 0x{st:02x} rd_done={int(g.r_rd_bases_done.value)} "
                          f"wr_done={int(g.r_wr_bases_done.value)} ext={int(g.u_core.r_is_ext.value)}")
            self._dbg_st = st
        cnt = int(self.dut.gen_ch[ch].u_g.r_cmd_err_cnt.value)
        if cnt != getattr(self, '_dbg_err', 0):
            self.log.info(f"SEQ c{self.cycle} ch{ch} CMD_ERR -> {cnt}")
            self._dbg_err = cnt
        if (int(d.seq_wr_en.value) >> ch) & 1:
            self.log.info(f"SEQ c{self.cycle} ch{ch} st=0x{self.ch['g'][ch].state:02x} "
                          f"w[{int(d.seq_wr_addr.value)}]=0x{int(d.seq_wr_data.value):08x}")

    async def run_cycles(self, n: int):
        for _ in range(n):
            await FallingEdge(self.dut.clk)
            self._drive()
            await ReadOnly()
            self._debug_seq()
            self._sample()
            self.cycle += 1

    # -- scenarios ------------------------------------------------------------------
    def load(self, per_channel: List[List[Desc]]):
        """The same descriptor list for channel i on both sides."""
        for s in SIDES:
            for i, lst in enumerate(per_channel):
                self.ch[s][i].queue.extend(lst)

    def load_one(self, i: int, lst: List[Desc]):
        """The same descriptors for channel i on both sides."""
        for s in SIDES:
            self.ch[s][i].queue.extend(lst)

    def quiet(self, s: str, i: int) -> bool:
        c = self.ch[s][i]
        return (c.head is None and not c.queue and c.rd.busy == 0 and c.wr.busy == 0
                and not c.wr.commits and (c.idle or c.state == ST_ERROR))

    async def cycles_to_quiet(self, max_cycles: int, hold: int = 32) -> Dict[str, int]:
        """Run until each side has been quiet for `hold` cycles; the cycle
        (from now) each became quiet. The hold matters: the cycle a descriptor
        is handed over, the scheduler is still idle and its skid still empty."""
        start, since, done = self.cycle, {}, {}
        while len(done) < len(SIDES) and self.cycle - start < max_cycles:
            await self.run_cycles(1)
            for s in SIDES:
                if s in done:
                    continue
                if all(self.quiet(s, i) for i in range(self.N)):
                    since.setdefault(s, self.cycle - start)
                    if self.cycle - start - since[s] >= hold:
                        done[s] = since[s]
                else:
                    since.pop(s, None)
        return done

    async def run_until_quiet(self, max_cycles: int, hold: int = 64) -> bool:
        still = 0
        for _ in range(max_cycles // 8):
            await self.run_cycles(8)
            if all(self.quiet(s, i) for s in SIDES for i in range(self.N)):
                still += 8
                if still >= hold:
                    return True
            else:
                still = 0
        self.log.error("timed out waiting for both sides to go quiet")
        for s in SIDES:
            for i, c in enumerate(self.ch[s]):
                self.log.error(f"  {s}{i}: state=0x{c.state:02x} idle={c.idle} queue={len(c.queue)} "
                               f"head={c.head is not None} rd.busy={c.rd.busy} wr.busy={c.wr.busy} "
                               f"commits={len(c.wr.commits)}")
        for i in range(self.N):
            g = self.dut.gen_ch[i].u_g
            names = ('r_armed', 'r_staged', 'r_declined', 'r_gen_need', 'r_start_pending',
                     'r_rd_bases_done', 'r_wr_bases_done', 'seq_attn', 'w_rd_cnt', 'w_wr_cnt')
            vals = []
            for n in names:
                try:
                    vals.append(f"{n}={int(getattr(g, n).value)}")
                except Exception:
                    vals.append(f"{n}=?")
            self.log.error(f"  g{i} scheduler_g: " + " ".join(vals))
            core = g.u_core
            cv = []
            for n in ('r_read_beats_remaining', 'r_write_beats_remaining', 'r_write_beats_to_commit',
                      'r_rd_run_remaining', 'r_wr_run_remaining', 'r_is_ext', 'r_rd_per_beat', 'r_wr_per_beat',
                      'r_rd_beats_total', 'r_wr_beats_total'):
                try:
                    obj = core if hasattr(core, n) else g
                    cv.append(f"{n}={int(getattr(obj, n).value)}")
                except Exception:
                    cv.append(f"{n}=?")
            self.log.error(f"  g{i} core: " + " ".join(cv))
        return False

    async def wait_state(self, i: int, state: int, max_cycles: int) -> bool:
        for _ in range(max_cycles):
            await self.run_cycles(1)
            if all(self.ch[s][i].state == state for s in SIDES):
                return True
        return False

    async def channel_reset(self, mask: int, cycles: int = 4):
        self.reset_mask = {s: mask for s in SIDES}
        await self.run_cycles(cycles)
        self.reset_mask = {s: 0 for s in SIDES}
        await self.run_cycles(4)

    def plan_reset(self, i: int, kth_fetch: int, state: int, after: List[Desc] = ()):
        """Reset channel i on each side when its k-th descriptor reaches
        `state`; `after` is queued on that side once its reset ends. A reset
        drains the scheduler's descriptor skid, and how full it is depends on
        each side's timing, so nothing may be queued behind the k-th
        descriptor until then."""
        for s in SIDES:
            self.ch[s][i].reset_at = (kth_fetch, state)
            self.ch[s][i].after_reset = list(after)

    def resets_done(self) -> bool:
        return all(c.reset_at is None and not c.reset_left for s in SIDES for c in self.ch[s])

    def mark(self, i: int) -> Dict[str, Tuple[int, int]]:
        """Command counts of channel i on each side, to bracket a window."""
        return {s: (len(self.ch[s][i].rd_cmds), len(self.ch[s][i].wr_cmds)) for s in SIDES}

    def skip_window(self, i: int, start: Dict, end: Dict):
        """Leave channel i's commands between two marks out of the comparison:
        after an injected engine error, how far the OTHER direction got is a
        matter of engine timing, which differs between the sides by design."""
        for s in SIDES:
            for k, what in enumerate(('rd_cmds', 'wr_cmds')):
                self.ch[s][i].skip.append((what, start[s][k], end[s][k]))

    @staticmethod
    def _kept(c, what):
        drop = set()
        for w, a, b in c.skip:
            if w == what:
                drop.update(range(a, b))
        return [x for j, x in enumerate(getattr(c, what)) if j not in drop]

    def compare(self) -> bool:
        ok = True
        for i in range(self.N):
            f, g = self.ch['f'][i], self.ch['g'][i]
            if f.err_to_error != g.err_to_error:
                ok = False
                self.log.error(f"ch{i}: injected error -> CH_ERROR in {f.err_to_error} cycles (FSM) vs "
                               f"{g.err_to_error} (gatling)")
            if f.cmds_in_error or g.cmds_in_error:
                ok = False
                self.log.error(f"ch{i}: engine requests in CH_ERROR: FSM {f.cmds_in_error}, gatling {g.cmds_in_error}")
            for what in ('rd_cmds', 'wr_cmds', 'rd_pkts', 'wr_pkts', 'mons', 'states'):
                a, b = self._kept(f, what), self._kept(g, what)
                if a != b:
                    ok = False
                    k = next((j for j in range(min(len(a), len(b))) if a[j] != b[j]), min(len(a), len(b)))
                    self.log.error(f"ch{i} {what}: FSM {len(a)} vs gatling {len(b)}, first difference at "
                                   f"#{k}: f={a[k] if k < len(a) else None} g={b[k] if k < len(b) else None}")
                    if len(getattr(f, what)) <= 24 and len(getattr(g, what)) <= 24:
                        for side, c in (('f', f), ('g', g)):
                            self.log.error(f"  {side}{i} {what} (all): {getattr(c, what)}  "
                                           f"skips {[t for t in c.skip if t[0] == what]}")
            if f.state != g.state:
                ok = False
                self.log.error(f"ch{i} final state: FSM 0x{f.state:02x} vs gatling 0x{g.state:02x}")
            self.log.info(f"ch{i}: rd {len(f.rd_cmds)}/{len(g.rd_cmds)} wr {len(f.wr_cmds)}/{len(g.wr_cmds)} "
                          f"records {len(f.rd_pkts)}+{len(f.wr_pkts)}/{len(g.rd_pkts)}+{len(g.wr_pkts)} "
                          f"mon {len(f.mons)}/{len(g.mons)} state 0x{f.state:02x}/0x{g.state:02x}")
        return ok

    def cmd_errors(self) -> int:
        """Illegal commands / dropped pushes counted by scheduler_g on channels
        never reset: must stay 0. A reset channel may count a few -- the
        firmware's command for the state before the reset arrives after it
        and is ignored, which is what the edge table is for."""
        total = 0
        for i in range(self.N):
            n = int(getattr(self.dut.gen_ch[i].u_g, 'r_cmd_err_cnt').value)
            if self.ch['g'][i].was_reset:
                self.log.info(f"g{i}: {n} stale command(s) after a reset, ignored by scheduler_g")
            else:
                total += n
                if n:
                    self.log.error(f"g{i}: {n} illegal command(s) on a channel never reset")
        return total

    # -- golden command model ----------------------------------------------------
    def golden_cmds(self, d: Desc, is_wr: bool) -> List[Tuple[int, int]]:
        """The (address, beats) commands one descriptor must produce on one
        direction, from the descriptor alone: the byte-to-beat ceiling, the
        address advance per burst, and for TYPE=EXT the run bases of
        stream_run_addr_gen / dma_address_gen (base + ((i0*s0) & m0) +
        ((i1*s1) & m1), 16-bit indices). Burst sizes are _burst's."""
        L, M64 = self.lanes, (1 << 64) - 1
        pk = d.packet
        addr = (pk >> (64 if is_wr else 0)) & M64
        length = (pk >> 128) & 0xFFFFFFFF
        if length == 0:
            return []
        total = (addr % L + length + L - 1) // L
        is_ext = ((pk >> 210) & 7) == DESC_TYPE_EXT
        if not is_ext:
            out, left = [], total
            while left:
                out.append((addr, left))
                n = self._burst(addr, left)
                addr, left = (addr - addr % L) + n * L, left - n
            return out
        e = d.ext >> (96 if is_wr else 0)

        def sx(v):
            return v - (1 << 32) if v & (1 << 31) else v

        s0, s1 = sx(e & 0xFFFFFFFF), sx((e >> 32) & 0xFFFFFFFF)
        inner = ((e >> 64) & 0xFFFF) or 1
        w0, w1 = (e >> 80) & 0x3F, (e >> 86) & 0x3F
        m0 = ((1 << w0) - 1) if w0 else M64
        m1 = ((1 << w1) - 1) if w1 else M64
        per_beat = (s0 & 0xFFFFFFFF) != L
        base0 = addr
        bases = []
        if (pk >> DESC_ALG_LO) & 0xFF == 1:
            # selector 1, Z-order (rapids TASK-035): unit k (a beat, or a run
            # of inner beats) at base + ((x * S0) & m0) + ((y * s1) & m1),
            # (x, y) = Morton(k), S0 = stride_0 per beat or inner beats per run
            step = 1 if per_beat else inner
            big_s0 = s0 if per_beat else inner * L
            k, gen = 1, step
            while gen < total:
                x, y = morton_xy(k)
                bases.append((base0 + ((x * big_s0) & m0) + ((y * s1) & m1)) & M64)
                gen += step
                k += 1
        else:
            # the generator's positions after run 0 / beat 0
            if per_beat:
                i0, i1 = (1, 0) if inner > 1 else (0, 1)
                gen, step = 1, 1
            else:
                i0, i1, gen, step = 0, 1, inner, inner
            while gen < total:
                bases.append((base0 + ((i0 * s0) & m0) + ((i1 * s1) & m1)) & M64)
                gen += step
                if per_beat and i0 != inner - 1:
                    i0 += 1
                else:
                    i0 = 0 if per_beat else i0
                    i1 = (i1 + 1) & 0xFFFF
        run_size = 1 if per_beat else inner
        out, left = [], total
        run = min(run_size, total)
        while left:
            out.append((addr, run))
            n = self._burst(addr, run)
            addr, left, run = (addr - addr % L) + n * L, left - n, run - n
            if run == 0 and left:
                addr = bases.pop(0)
                run = min(run_size, left)
        return out

    # -- descriptor generators ----------------------------------------------------
    def rand_linear(self, n: int, chains: bool = True) -> List[Desc]:
        out = []
        while len(out) < n:
            k = self.rng.randint(1, 3) if chains else 1
            for j in range(k):
                last = (j == k - 1)
                src = self.rng.randrange(0x1000, 0xFFFF_FFFF) & ~0xF | self.rng.randrange(self.lanes)
                dst = self.rng.randrange(0x1000, 0xFFFF_FFFF) & ~0xF | self.rng.randrange(self.lanes)
                length = self.rng.choice([0, 1, self.lanes - 1, self.lanes, self.lanes + 1,
                                          self.rng.randint(1, 40 * self.lanes)])
                out.append(make_desc(src, dst, length, next_ptr=0 if last else 0x40 * (j + 1),
                                     gen_irq=self.rng.random() < 0.3, last=last))
        return out          # whole chains: a cut chain would wait in NEXT_DESC forever

    def rand_ext(self, n: int, alg: int = 0) -> List[Desc]:
        L = self.lanes
        out = []
        for _ in range(n):
            beats = self.rng.randint(1, 48)
            src = self.rng.choice([self.rng.randrange(0, 2**40), 0xFFFF_F000, 2**32 - 4 * L]) & ~(L - 1)
            dst = self.rng.choice([self.rng.randrange(0, 2**40), 0x7FFF_F000]) & ~(L - 1)

            def stride():
                return self.rng.choice([L, 2 * L, -L, -3 * L, 5 * L, (1 << 20) * L, -(1 << 18) * L,
                                        self.rng.randint(-4096, 4096) * L])

            def wrap():
                return self.rng.choice([0, 0, self.off_w + 2, self.off_w + 6, 20, 32, 33, 40])

            ext = dict(rd_s0=stride(), rd_s1=stride(), rd_w0=wrap(), rd_w1=wrap(),
                       rd_inner=self.rng.choice([0, 1, 2, 3, 4, 7, 16]),
                       wr_s0=stride(), wr_s1=stride(), wr_w0=wrap(), wr_w1=wrap(),
                       wr_inner=self.rng.choice([0, 1, 2, 3, 4, 7, 16]))
            # stride_0 == beat size runs a row contiguously; anything else is per beat
            if self.rng.random() < 0.5:
                ext['rd_s0'] = L
            if self.rng.random() < 0.5:
                ext['wr_s0'] = L
            out.append(make_desc(src, dst, beats * L, gen_irq=self.rng.random() < 0.2, ext=ext, alg=alg))
        return out
