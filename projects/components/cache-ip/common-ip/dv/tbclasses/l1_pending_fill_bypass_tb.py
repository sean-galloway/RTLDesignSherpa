"""
l1_pending_fill_bypass testbench

Pending-fill / load-miss bypass register leaf: direct pin-level stimulus
(no bus interface, no BFM -- same pattern as l1_repl_tb). Scores the
register against a small golden model of the ALWAYS_FF_RST block:

    if pf_load:        active <= 1, addr/state load, beat mask clears
    elif pf_clear:     active <= 0
    elif pf_beat_set:  data_valid[pf_beat_idx] <= 1

Combinational outputs scored every settled cycle: pf_match ==
active && (pf_snoop_addr == pf_addr) and pf_beat_valid ==
data_valid[pf_beat_idx].

Directed phases cover the points the integration suite cannot reach
(testplan gaps section): reset values, the E-state load path (integration
only ever loads S/M), re-arm while active (mask resets), and the strobe
priority corners (load > clear > beat). A random soak then mixes
idle/load/beat/clear traffic.

Author: RTL Design Sherpa
Created: 2026-10-30
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase

# l1_pkg cache_state_t encodings scored by this TB
STATE_I = 0
STATE_S = 1
STATE_E = 2
STATE_M = 3


class L1PendingFillBypassTB(TBBase):
    """Drives l1_pending_fill_bypass and scores all fields every cycle."""

    OP_COUNTS = {'gate': 100, 'func': 2000, 'full': 20000}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.OP_COUNTS:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.LINE_BYTES = self.convert_to_int(os.environ.get('LINE_BYTES', '64'))
        self.BUS_WIDTH = self.convert_to_int(os.environ.get('BUS_WIDTH', '64'))
        self.LINE_OFFSET_WIDTH = self.LINE_BYTES.bit_length() - 1
        self.LINE_ADDR_WIDTH = self.ADDR_WIDTH - self.LINE_OFFSET_WIDTH
        self.FILL_BEATS = (self.LINE_BYTES * 8) // self.BUS_WIDTH
        self.checks = 0
        self.mismatches = 0
        # golden model: the four MAS ch02_blocks/02 fields
        self.m_active = False
        self.m_addr = 0
        self.m_state = STATE_I
        self.m_mask = 0
        self.log.info(f"L1PendingFillBypassTB line_addr_width={self.LINE_ADDR_WIDTH} "
                      f"fill_beats={self.FILL_BEATS} level={self.TEST_LEVEL} "
                      f"seed={self.SEED}")

    # -- the three mandatory methods -----------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self.dut.pf_load.value = 0
        self.dut.pf_clear.value = 0
        self.dut.pf_beat_set.value = 0
        self.dut.pf_load_addr.value = 0
        self.dut.pf_load_state.value = STATE_I
        self.dut.pf_beat_idx.value = 0
        self.dut.pf_snoop_addr.value = 0
        await self.assert_reset()
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()
        await self.wait_clocks('clk', 1)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # -- scoring --------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got {got} expected {exp}")

    # -- one cycle: drive strobes, clock, settle, model-update, score ---------
    async def _cycle(self, load, clear, beat_set, beat_idx, load_addr,
                     load_state, snoop_addr, tag):
        self.dut.pf_load.value = 1 if load else 0
        self.dut.pf_clear.value = 1 if clear else 0
        self.dut.pf_beat_set.value = 1 if beat_set else 0
        self.dut.pf_beat_idx.value = beat_idx
        self.dut.pf_load_addr.value = load_addr
        self.dut.pf_load_state.value = load_state
        self.dut.pf_snoop_addr.value = snoop_addr
        await RisingEdge(self.dut.clk)
        # model: load > clear > beat (RTL priority chain)
        if load:
            self.m_active = True
            self.m_addr = load_addr
            self.m_state = load_state
            self.m_mask = 0
        elif clear:
            self.m_active = False
        elif beat_set:
            self.m_mask |= 1 << beat_idx
        await Timer(1, units='ns')
        exp_match = 1 if (self.m_active and snoop_addr == self.m_addr) else 0
        exp_beat_valid = (self.m_mask >> beat_idx) & 1
        self._score(f"{tag} pf_active", int(self.dut.pf_active.value),
                    1 if self.m_active else 0)
        self._score(f"{tag} pf_addr", int(self.dut.pf_addr.value), self.m_addr)
        self._score(f"{tag} pf_state", int(self.dut.pf_state.value), self.m_state)
        self._score(f"{tag} pf_data_valid", int(self.dut.pf_data_valid.value),
                    self.m_mask)
        self._score(f"{tag} pf_match", int(self.dut.pf_match.value), exp_match)
        self._score(f"{tag} pf_beat_valid", int(self.dut.pf_beat_valid.value),
                    exp_beat_valid)
        self.dut.pf_load.value = 0
        self.dut.pf_clear.value = 0
        self.dut.pf_beat_set.value = 0

    def _rand_line_addr(self):
        return random.getrandbits(self.LINE_ADDR_WIDTH)

    # -- tests ------------------------------------------------------------------
    async def run(self) -> bool:
        # Post-reset values: inactive, Invalid state, empty mask, no match
        # even when the snoop address equals the (zeroed) register address.
        await Timer(1, units='ns')
        self._score("reset pf_active", int(self.dut.pf_active.value), 0)
        self._score("reset pf_state", int(self.dut.pf_state.value), STATE_I)
        self._score("reset pf_data_valid", int(self.dut.pf_data_valid.value), 0)
        self._score("reset pf_match", int(self.dut.pf_match.value), 0)

        # Directed: load arms {addr, state, empty mask}; match is the
        # {tag, set} compare (the snoop port is already offset-free).
        addr = self._rand_line_addr()
        await self._cycle(True, False, False, 0, addr, STATE_S, addr, "load S")
        other = addr ^ 1 if self.LINE_ADDR_WIDTH > 0 else addr
        await self._cycle(False, False, False, 0, 0, STATE_I, other,
                          "no-match other line")
        # Beat accumulation in a shuffled order; pf_beat_valid follows the
        # driven beat index combinationally.
        order = list(range(self.FILL_BEATS))
        random.shuffle(order)
        for i, beat in enumerate(order):
            await self._cycle(False, False, True, beat, 0, STATE_I, addr,
                              f"beat {beat}")
            # spot-check an unset index too (wrap to stay in range)
            probe = (beat + 1) % self.FILL_BEATS
            await self._cycle(False, False, False, probe, 0, STATE_I, addr,
                              f"probe idx {probe}")
        # Directed: clear retires the register; match drops even with the
        # snoop address still parked on the line.
        await self._cycle(False, True, False, 0, 0, STATE_I, addr, "clear")
        # Directed: the E-state load path -- integration only loads S/M
        # (READ_SHARED / READ_UNIQUE fills); the leaf mux is the same, so
        # arm E here (testplan gaps section).
        addr_e = self._rand_line_addr()
        await self._cycle(True, False, False, 0, addr_e, STATE_E, addr_e,
                          "load E")
        # Directed: re-arm while active -- new addr/state, mask resets.
        await self._cycle(False, False, True, 0, 0, STATE_I, addr_e,
                          "beat before re-arm")
        addr_m = self._rand_line_addr()
        await self._cycle(True, False, False, 0, addr_m, STATE_M, addr_m,
                          "re-arm M")
        # Directed priority corners: load+clear+beat -> load wins (armed,
        # empty mask); then clear+beat -> clear wins (beat bit NOT set).
        await self._cycle(True, True, True, 1, addr, STATE_S, addr,
                          "load+clear+beat")
        await self._cycle(False, True, True, 2, 0, STATE_I, addr,
                          "clear+beat")

        # Random soak: weighted load / beat / clear / idle traffic.
        n_ops = self.OP_COUNTS[self.TEST_LEVEL]
        self.log.info(f"l1_pending_fill_bypass: {n_ops} random cycles at "
                      f"{self.TEST_LEVEL}")
        for i in range(n_ops):
            r = random.random()
            load = r < 0.15
            clear = 0.15 <= r < 0.3
            beat_set = 0.3 <= r < 0.8
            await self._cycle(load, clear, beat_set,
                              random.randrange(self.FILL_BEATS),
                              self._rand_line_addr(),
                              random.choice([STATE_S, STATE_M, STATE_E]),
                              self._rand_line_addr(), f"rnd{i}")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
