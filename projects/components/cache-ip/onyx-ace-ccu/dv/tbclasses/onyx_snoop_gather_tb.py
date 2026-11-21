# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: onyx_snoop_gather_tb
# Purpose: the snoop-gather testbench for onyx (onyx TASK-001 step 1) -- N
#   AXI4ACESnoopMaster BFMs (the manager's fanout) against N
#   AXI4ACESnoopSlave BFMs (the caches) through the house ACE transport
#   movers, on onyx_snoop_gather_rig_tb.
#
# Subsystem: onyx (cache-ip)
"""The snoop-gather testbench.

What it proves about the BFM before any onyx RTL exists (PRD D4, D10):

- every (MESI state, snoop type) cell of the caches' CRRESP matrix
  (l1_pkg amber_snoop_crresp, ported here as the golden) comes back
  through the transport with the right CRRESP and the right line data,
  LINE_BYTES / DATA_WIDTH beats of it, on every one of N ports;
- a broadcast to N caches gathers N correct responses when they are issued
  in the same cycle and complete in any order (per-port timing profiles
  make the order differ and the test counts that it did);
- back-to-back snoops per port stay in order under the stricter
  CD-before-CR family convention;
- the BFM's own default responder matrix equals the caches' (l1_pkg says it
  is that matrix bit for bit; this checks the claim).

Checks are counted (``checks`` / ``mismatches``); a compliance checker per
port validates every CRRESP for its snoop type and its violation count must
be zero with a non-zero check count.
"""
import os
import random
from typing import Dict, List, Optional, Tuple

import cocotb
from cocotb.triggers import RisingEdge, Timer

from CocoTBFramework.components.ace.ace_compliance_checker import ACEComplianceChecker
from CocoTBFramework.components.ace.ace_interfaces import (
    AXI4ACESnoopMaster,
    AXI4ACESnoopSlave,
)
from CocoTBFramework.components.ace.ace_transaction import CRRESP, CacheState, SnoopType
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.shared.tbbase import TBBase

MESI_STATES = (CacheState.INVALID, CacheState.SHARED, CacheState.EXCLUSIVE, CacheState.MODIFIED)
SNOOP_TYPES = (SnoopType.READ_ONCE, SnoopType.READ_SHARED, SnoopType.READ_UNIQUE,
               SnoopType.CLEAN_SHARED, SnoopType.CLEAN_INVALID, SnoopType.MAKE_INVALID)


def amber_crresp(state: CacheState, snoop: SnoopType) -> CRRESP:
    """l1_pkg::amber_snoop_crresp, the caches' HAS Table 3.0, as the golden.

    IHI0022 bit order {WasUnique, IsShared, PassDirty, Error, DataTransfer};
    Invalid and anything outside MESI answer the safe default (miss, no
    data).
    """
    dt = pd = is_ = wu = False
    if state == CacheState.MODIFIED:
        if snoop in (SnoopType.READ_SHARED, SnoopType.CLEAN_SHARED, SnoopType.CLEAN_INVALID):
            dt = pd = is_ = True
        elif snoop in (SnoopType.READ_ONCE, SnoopType.READ_UNIQUE):
            dt = pd = True
        # MakeInvalid: no transfer (IHI0022 forbids DataTransfer)
    elif state == CacheState.EXCLUSIVE:
        if snoop in (SnoopType.READ_SHARED, SnoopType.READ_ONCE):
            dt = is_ = wu = True
        elif snoop == SnoopType.READ_UNIQUE:
            dt = wu = True
        elif snoop == SnoopType.CLEAN_SHARED:
            is_ = wu = True
    elif state == CacheState.SHARED:
        if snoop in (SnoopType.READ_SHARED, SnoopType.READ_ONCE):
            is_ = True
    return CRRESP.from_bits(data_transfer=dt, pass_dirty=pd, is_shared=is_, was_unique=wu)


class OnyxSnoopGatherTB(TBBase):
    """N manager-side snoop BFMs against N cache-side snoop BFMs."""

    PROFILES = {
        'fast':   {'valid': ([(0, 0)], [1.0]),                 'ready': ([(0, 0)], [1.0])},
        'normal': {'valid': ([(0, 1), (2, 4)], [0.7, 0.3]),    'ready': ([(0, 0), (1, 3)], [0.8, 0.2])},
        'slow':   {'valid': ([(2, 5), (6, 10)], [0.6, 0.4]),   'ready': ([(2, 5), (6, 10)], [0.6, 0.4])},
        'stress': {'valid': ([(0, 1), (2, 6), (7, 12)], [0.4, 0.4, 0.2]),
                   'ready': ([(0, 0), (2, 5), (6, 12)], [0.4, 0.4, 0.2])},
    }

    def __init__(self, dut):
        super().__init__(dut)
        self.aclk = dut.aclk
        self.aresetn = dut.aresetn
        self.n = int(os.environ.get('TEST_N_CACHES', '2'))
        self.addr_width = int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.data_width = int(os.environ.get('TEST_DATA_WIDTH', '64'))
        self.line_bytes = int(os.environ.get('TEST_LINE_BYTES', '64'))
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.clk_period = int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.compliance = os.environ.get('ACE_COMPLIANCE_CHECK', '1') == '1'
        self.seed = int(os.environ.get('SEED', '0'))
        random.seed(self.seed)
        self.beats = self.line_bytes * 8 // self.data_width
        self.data_mask = (1 << self.data_width) - 1
        self.addr_mask = ((1 << self.addr_width) - 1) & ~(self.line_bytes - 1)

        self.masters: List[AXI4ACESnoopMaster] = []
        self.slaves: List[AXI4ACESnoopSlave] = []
        self.checkers: List[Optional[ACEComplianceChecker]] = []
        for i in range(self.n):
            self.masters.append(AXI4ACESnoopMaster(
                dut=dut, clock=self.aclk, prefix=f"m{i}_", log=self.log,
                ifc_name=f"ccu{i}", data_width=self.data_width,
                addr_width=self.addr_width, timeout_cycles=20000))
            slave = AXI4ACESnoopSlave(
                dut=dut, clock=self.aclk, prefix=f"c{i}_", log=self.log,
                ifc_name=f"cache{i}", data_width=self.data_width,
                addr_width=self.addr_width)
            slave.set_handler(self._make_handler(i))
            self.slaves.append(slave)
            self.checkers.append(ACEComplianceChecker(log=self.log) if self.compliance else None)

        # state[i][line] -- the per-cache line states the golden reads
        self.state: List[Dict[int, CacheState]] = [dict() for _ in range(self.n)]
        self.stats = {
            'checks': 0, 'mismatches': 0, 'snoops': 0,
            'crresp_mismatches': 0, 'beat_count_mismatches': 0, 'data_mismatches': 0,
            'gathers': 0, 'gathers_out_of_order': 0, 'compliance_checks': 0,
            'compliance_violations': 0, 'default_matrix_cells': 0, 'default_matrix_diffs': 0,
            'single_supplier_checks': 0,
            # CD streaming probe (informational): cycles from the first to the
            # last CD handshake of one full-line response on port 0 under the
            # 'fast' profile; beats-1 would be back-to-back streaming
            'cd_span_cycles': -1, 'cd_beats_seen': 0,
        }
        for i in range(self.n):
            self.set_profile(i, 'normal')
        self.log.info(f"OnyxSnoopGatherTB: N={self.n} DW={self.data_width} "
                      f"beats/line={self.beats} level={self.level} seed={self.seed}")

    # ------------------------------------------------------------------
    # the three mandatory methods
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', self.clk_period, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 10)

    async def assert_reset(self):
        self.aresetn.value = 0

    async def deassert_reset(self):
        self.aresetn.value = 1

    # ------------------------------------------------------------------
    # golden
    # ------------------------------------------------------------------
    def line_data(self, i: int, line: int) -> List[int]:
        """The line cache i holds: deterministic, non-zero, distinct per
        cache and beat so a wrong beat or a wrong source is visible."""
        out = []
        for k in range(self.beats):
            v = ((line >> 6) * 0x9E3779B1 + (i + 1) * 0x85EBCA6B + (k + 1) * 0xC2B2AE35) & 0xFFFFFFFFFFFFFFFF
            v = (v ^ (v >> 29)) & self.data_mask
            out.append(v | 1)
        return out

    def _make_handler(self, i: int):
        def handler(addr: int, snoop_type: SnoopType, _state: CacheState):
            line = addr & self.addr_mask
            st = self.state[i].get(line, CacheState.INVALID)
            crresp = amber_crresp(st, snoop_type)
            data = self.line_data(i, line) if crresp.data_transfer else None
            return crresp, data
        return handler

    def set_state(self, i: int, line: int, st: CacheState):
        line &= self.addr_mask
        self.state[i][line] = st
        self.slaves[i].set_line_behavior(line, st)

    def expected(self, i: int, line: int, snoop_type: SnoopType) -> Tuple[CRRESP, Optional[List[int]]]:
        st = self.state[i].get(line & self.addr_mask, CacheState.INVALID)
        crresp = amber_crresp(st, snoop_type)
        return crresp, (self.line_data(i, line & self.addr_mask) if crresp.data_transfer else None)

    def set_profile(self, i: int, name: str):
        cfg = self.PROFILES[name]
        self.masters[i].ac_channel.set_randomizer(FlexRandomizer({'valid_delay': cfg['valid']}))
        self.slaves[i].cr_channel.set_randomizer(FlexRandomizer({'valid_delay': cfg['valid']}))
        self.slaves[i].cd_channel.set_randomizer(FlexRandomizer({'valid_delay': cfg['valid']}))
        self.masters[i].cr_channel.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.masters[i].cd_channel.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))

    # ------------------------------------------------------------------
    # one snoop, checked
    # ------------------------------------------------------------------
    def _check(self, i: int, line: int, snoop_type: SnoopType, result) -> bool:
        exp_crresp, exp_data = self.expected(i, line, snoop_type)
        ok = True
        self.stats['checks'] += 1
        if result.crresp != exp_crresp:
            self.log.error(f"port {i} line=0x{line:08X} {snoop_type.name}: CRRESP got "
                           f"{result.crresp!r} expected {exp_crresp!r}")
            self.stats['crresp_mismatches'] += 1
            ok = False
        if exp_data is None:
            if result.data:
                self.log.error(f"port {i} line=0x{line:08X} {snoop_type.name}: "
                               f"{len(result.data)} unexpected data beats")
                self.stats['beat_count_mismatches'] += 1
                ok = False
        else:
            if len(result.data) != len(exp_data):
                self.log.error(f"port {i} line=0x{line:08X} {snoop_type.name}: "
                               f"{len(result.data)} beats, expected {len(exp_data)}")
                self.stats['beat_count_mismatches'] += 1
                ok = False
            else:
                for k, (g, e) in enumerate(zip(result.data, exp_data)):
                    if g != e:
                        self.log.error(f"port {i} line=0x{line:08X} {snoop_type.name}: beat {k} "
                                       f"got 0x{g:X} expected 0x{e:X}")
                        self.stats['data_mismatches'] += 1
                        ok = False
                        break
        chk = self.checkers[i]
        if chk is not None:
            before = len(chk.violations)
            chk.check_crresp_validity(result.crresp, snoop_type, line)
            self.stats['compliance_checks'] += 1
            self.stats['compliance_violations'] += len(chk.violations) - before
        if not ok:
            self.stats['mismatches'] += 1
        return ok

    async def snoop(self, i: int, line: int, snoop_type: SnoopType):
        line &= self.addr_mask
        self.stats['snoops'] += 1
        result = await self.masters[i].issue_snoop(line, snoop_type)
        self._check(i, line, snoop_type, result)
        return result

    # ------------------------------------------------------------------
    # scenarios
    # ------------------------------------------------------------------
    async def scenario_default_matrix(self):
        """The BFM's default responder against the caches' matrix, in Python."""
        probe = self.slaves[0]
        for st in MESI_STATES:
            for t in SNOOP_TYPES:
                got, _ = probe._default_handler(0x1000, t, st)
                exp = amber_crresp(st, t)
                self.stats['default_matrix_cells'] += 1
                if int(got) != int(exp):
                    self.stats['default_matrix_diffs'] += 1
                    self.log.error(f"BFM default matrix differs from amber_snoop_crresp at "
                                   f"({st.name}, {t.name}): BFM {got!r} caches {exp!r}")
        self.log.info(f"default matrix: {self.stats['default_matrix_cells']} cells, "
                      f"{self.stats['default_matrix_diffs']} differ")

    async def scenario_matrix(self, base: int = 0x0001_0000):
        """Every (state, type) cell on every port, serially."""
        for i in range(self.n):
            for s_idx, st in enumerate(MESI_STATES):
                line = (base + ((i * 8 + s_idx) * self.line_bytes)) & self.addr_mask
                self.set_state(i, line, st)
                for t in SNOOP_TYPES:
                    await self.snoop(i, line, t)

    async def gather(self, line: int, snoop_type: SnoopType) -> List[int]:
        """Broadcast one snoop to every port in the same cycle; return the
        completion order (port indices)."""
        order: List[int] = []

        async def one(i):
            await self.snoop(i, line, snoop_type)
            order.append(i)

        tasks = [cocotb.start_soon(one(i)) for i in range(self.n)]
        for t in tasks:
            await t
        self.stats['gathers'] += 1
        if order != list(range(self.n)):
            self.stats['gathers_out_of_order'] += 1
        return order

    def _assign_states(self, line: int, pattern: str):
        """MESI-legal state assignments for one line across the N caches."""
        for i in range(self.n):
            self.set_state(i, line, CacheState.INVALID)
        if pattern == 'one_m':
            self.set_state(random.randrange(self.n), line, CacheState.MODIFIED)
        elif pattern == 'one_e':
            self.set_state(random.randrange(self.n), line, CacheState.EXCLUSIVE)
        elif pattern == 'all_s':
            for i in range(self.n):
                self.set_state(i, line, CacheState.SHARED)
        elif pattern == 'some_s':
            for i in random.sample(range(self.n), max(1, self.n // 2)):
                self.set_state(i, line, CacheState.SHARED)
        # 'all_i': leave invalid

    async def scenario_gather(self, iterations: int, base: int = 0x0010_0000):
        """Broadcast gathers over the MESI-legal patterns and every snoop
        type; checks each response and that at most one cache supplies data
        with PassDirty or WasUnique (the adjudication precondition onyx D6
        relies on)."""
        patterns = ('one_m', 'one_e', 'all_s', 'some_s', 'all_i')
        n = 0
        for it in range(iterations):
            for p_idx, pattern in enumerate(patterns):
                for t in SNOOP_TYPES:
                    line = (base + n * self.line_bytes) & self.addr_mask
                    n += 1
                    self._assign_states(line, pattern)
                    suppliers = sum(1 for i in range(self.n)
                                    if self.expected(i, line, t)[0].data_transfer)
                    self.stats['single_supplier_checks'] += 1
                    if suppliers > 1:
                        self.stats['mismatches'] += 1
                        self.log.error(f"pattern {pattern} {t.name}: {suppliers} data suppliers")
                    await self.gather(line, t)

    async def scenario_out_of_order(self, iterations: int, base: int = 0x0020_0000):
        """Per-port profiles pull completion order apart; the gather must
        still be right and the order must actually differ somewhere."""
        names = list(self.PROFILES)
        for it in range(iterations):
            for i in range(self.n):
                self.set_profile(i, names[(i + it) % len(names)])
            line = (base + it * self.line_bytes) & self.addr_mask
            self._assign_states(line, 'all_s' if it % 2 else 'one_m')
            t = SNOOP_TYPES[it % len(SNOOP_TYPES)]
            order = await self.gather(line, t)
            self.log.info(f"ooo gather {it}: {t.name} order {order}")
        for i in range(self.n):
            self.set_profile(i, 'normal')

    async def scenario_back_to_back(self, count: int, base: int = 0x0030_0000):
        """count snoops per port, every port at once, each to its own
        lines with mixed states; the BFM allows one outstanding per port so
        this is the fastest legal issue rate."""
        async def stream(i):
            for k in range(count):
                line = (base + (i * count + k) * self.line_bytes) & self.addr_mask
                self.set_state(i, line, random.choice(MESI_STATES))
                await self.snoop(i, line, random.choice(SNOOP_TYPES))

        for i in range(self.n):
            self.set_profile(i, 'fast')
        tasks = [cocotb.start_soon(stream(i)) for i in range(self.n)]
        for t in tasks:
            await t
        for i in range(self.n):
            self.set_profile(i, 'normal')

    async def scenario_cd_streaming(self, line: int = 0x0050_0000):
        """How the BFM streams a line: span of the CD handshakes on port 0
        under the fast profile.  Not a pass/fail; the number is the finding
        (RDS-DV GAXIMaster.send waits for the pipeline to drain per beat, so a
        responder that loops send() cannot stream -- see send_burst)."""
        i = 0
        self.set_profile(i, 'fast')
        line &= self.addr_mask
        self.set_state(i, line, CacheState.MODIFIED)
        cdvalid = getattr(self.dut, f"m{i}_cdvalid")
        cdready = getattr(self.dut, f"m{i}_cdready")
        first = last = None
        beats = 0
        done = False

        async def probe():
            nonlocal first, last, beats
            cyc = 0
            while not done:
                await RisingEdge(self.aclk)
                cyc += 1
                if int(cdvalid.value) and int(cdready.value):
                    beats += 1
                    if first is None:
                        first = cyc
                    last = cyc

        task = cocotb.start_soon(probe())
        await self.snoop(i, line, SnoopType.READ_UNIQUE)
        await self.wait_clocks('aclk', 4)
        done = True
        await task
        self.stats['cd_beats_seen'] = beats
        self.stats['cd_span_cycles'] = (last - first) if first is not None else -1
        self.log.info(f"CD streaming probe: {beats} beats over {self.stats['cd_span_cycles']} "
                      f"cycles first-to-last (back-to-back would be {self.beats - 1})")
        self.set_profile(i, 'normal')

    async def run(self) -> bool:
        plan = {
            'gate': dict(gather=1, ooo=2, b2b=4),
            'func': dict(gather=2, ooo=8, b2b=16),
            'full': dict(gather=4, ooo=24, b2b=48),
        }[self.level if self.level in ('gate', 'func', 'full') else 'gate']
        await self.scenario_default_matrix()
        await self.scenario_matrix()
        await self.scenario_gather(plan['gather'])
        await self.scenario_out_of_order(plan['ooo'])
        await self.scenario_back_to_back(plan['b2b'])
        await self.scenario_cd_streaming()
        if self.level == 'full':
            for i in range(self.n):
                self.set_profile(i, 'stress')
            await self.scenario_gather(1, base=0x0040_0000)
        await self.wait_clocks('aclk', 20)
        return self.verdict()

    def verdict(self) -> bool:
        s = self.stats
        ok = (s['mismatches'] == 0 and s['default_matrix_diffs'] == 0
              and s['compliance_violations'] == 0 and s['checks'] > 0
              and (not self.compliance or s['compliance_checks'] > 0))
        if self.n > 1 and s['gathers'] >= 4 and s['gathers_out_of_order'] == 0:
            self.log.warning("no gather completed out of issue order -- the "
                             "out-of-order path was not exercised")
        return ok

    def get_test_report(self) -> dict:
        return dict(self.stats, n_caches=self.n, beats_per_line=self.beats,
                    data_width=self.data_width, level=self.level)
