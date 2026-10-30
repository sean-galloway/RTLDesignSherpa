"""
l1_victim testbench

Depth-1 victim buffer leaf: direct pin-level stimulus (no bus interface,
no BFM -- same pattern as l1_repl_tb). Scores the register against a small
golden model of the ALWAYS_FF_RST block:

    if victim_clear:                 valid <= 0          (clear wins)
    elif victim_load && !valid:      valid <= 1, payload loads

Directed phases cover the points the integration suite cannot reach
(testplan gaps section): reset values, the load-while-busy ignore path
driven deliberately, and the load+clear coincidence (clear wins
defensively). A random soak then mixes idle/load/clear/coincident strobes
with busy == valid and empty == !valid scored every settled cycle.

Author: RTL Design Sherpa
Created: 2026-10-30
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


class L1VictimTB(TBBase):
    """Drives l1_victim and scores valid/busy/empty/payload every cycle."""

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
        self.LINE_WIDTH = self.LINE_BYTES * 8
        self.checks = 0
        self.mismatches = 0
        # golden model: the three MAS ch02_blocks/05 fields
        self.m_valid = False
        self.m_addr = 0
        self.m_data = 0
        self.log.info(f"L1VictimTB addr_width={self.ADDR_WIDTH} "
                      f"line_bytes={self.LINE_BYTES} level={self.TEST_LEVEL} "
                      f"seed={self.SEED}")

    # -- the three mandatory methods -----------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self.dut.victim_load.value = 0
        self.dut.victim_clear.value = 0
        self.dut.victim_addr_in.value = 0
        self.dut.victim_data_in.value = 0
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
    async def _cycle(self, load, clear, addr, data, tag):
        self.dut.victim_load.value = 1 if load else 0
        self.dut.victim_clear.value = 1 if clear else 0
        self.dut.victim_addr_in.value = addr
        self.dut.victim_data_in.value = data
        await RisingEdge(self.dut.clk)
        # model: clear wins; a load while busy is ignored (depth-1 safety net)
        if clear:
            self.m_valid = False
        elif load and not self.m_valid:
            self.m_valid = True
            self.m_addr = addr
            self.m_data = data
        await Timer(1, units='ns')
        self._score(f"{tag} victim_valid", int(self.dut.victim_valid.value),
                    1 if self.m_valid else 0)
        self._score(f"{tag} victim_busy", int(self.dut.victim_busy.value),
                    1 if self.m_valid else 0)
        self._score(f"{tag} victim_empty", int(self.dut.victim_empty.value),
                    0 if self.m_valid else 1)
        if self.m_valid:
            self._score(f"{tag} victim_addr", int(self.dut.victim_addr.value),
                        self.m_addr)
            self._score(f"{tag} victim_data", int(self.dut.victim_data.value),
                        self.m_data)
        self.dut.victim_load.value = 0
        self.dut.victim_clear.value = 0

    def _rand_addr(self):
        return random.getrandbits(self.ADDR_WIDTH)

    def _rand_data(self):
        return random.getrandbits(self.LINE_WIDTH)

    # -- tests ------------------------------------------------------------------
    async def run(self) -> bool:
        # Post-reset values: empty buffer, zeroed fields.
        await Timer(1, units='ns')
        self._score("reset victim_valid", int(self.dut.victim_valid.value), 0)
        self._score("reset victim_busy", int(self.dut.victim_busy.value), 0)
        self._score("reset victim_empty", int(self.dut.victim_empty.value), 1)
        self._score("reset victim_addr", int(self.dut.victim_addr.value), 0)
        self._score("reset victim_data", int(self.dut.victim_data.value), 0)

        # Directed: load arms valid + payload the next cycle.
        addr, data = self._rand_addr(), self._rand_data()
        await self._cycle(True, False, addr, data, "load")
        # Payload holds stable across idle cycles while valid.
        for i in range(4):
            await self._cycle(False, False, self._rand_addr(), self._rand_data(),
                              f"hold{i}")
        # Directed: a load while busy is IGNORED -- the draining victim is
        # never overwritten (MAS ch02_blocks/05 Review Focus 2). Not
        # stimulus-reachable in integration; driven deliberately here.
        await self._cycle(True, False, self._rand_addr(), self._rand_data(),
                          "load-while-busy")
        # Directed: clear retires the buffer.
        await self._cycle(False, True, 0, 0, "clear")
        # Directed: load+clear coincidence -- clear wins defensively.
        await self._cycle(True, True, self._rand_addr(), self._rand_data(),
                          "load+clear on empty")
        assert not self.m_valid
        # ...and while busy: the valid victim retires, the new load is dropped.
        await self._cycle(True, False, self._rand_addr(), self._rand_data(),
                          "rearm")
        await self._cycle(True, True, self._rand_addr(), self._rand_data(),
                          "load+clear while busy")

        # Random soak: idle / load / clear / coincident strobes.
        n_ops = self.OP_COUNTS[self.TEST_LEVEL]
        self.log.info(f"l1_victim: {n_ops} random cycles at {self.TEST_LEVEL}")
        for i in range(n_ops):
            r = random.random()
            load = r < 0.35
            clear = 0.35 <= r < 0.55 or (load and random.random() < 0.1)
            await self._cycle(load, clear, self._rand_addr(), self._rand_data(),
                              f"rnd{i}")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
