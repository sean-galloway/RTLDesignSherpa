# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterBinLoadTB
# Purpose: Testbench for counter_bin_load
# Subsystem: framework
#
# Extracted from val/common/test_counter_bin_load.py, which had no TB class at
# all -- five flat cocotb functions each repeating the same ten lines of clock
# start and reset. That is the shape the contract exists to prevent: the reset
# sequence had five independent copies, so a change to it had five places to
# miss ([[tb-structure]]).

import os

import cocotb
from cocotb.triggers import ClockCycles

from TBClasses.shared.tbbase import TBBase


class CounterBinLoadTB(TBBase):
    """Testbench for counter_bin_load, a FIFO-pointer counter with load."""

    def __init__(self, dut):
        super().__init__(dut)

        self.WIDTH = int(dut.WIDTH.value)
        self.MAX = int(dut.MAX.value)

        # Per-test depth. REG_LEVEL picks how many parameter combinations run;
        # TEST_LEVEL decides how hard each one works.
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = {'gate': 1, 'func': 2, 'full': 5}[self.TEST_LEVEL]

        self.log.info(f"CounterBinLoadTB: WIDTH={self.WIDTH}, MAX={self.MAX}, "
                      f"TEST_LEVEL={self.TEST_LEVEL}")

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ------------------

    async def assert_reset(self):
        """Assert reset and park every input at its idle value."""
        self.dut.rst_n.value = 0
        self.dut.enable.value = 0
        self.dut.load.value = 0
        self.dut.load_value.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the reset sequence.

        Byte-for-byte the sequence the five cocotb functions each carried
        inline: 5 cycles asserted, 2 cycles to settle after release.
        """
        await self.start_clock('clk', 10, 'ns')
        await self.assert_reset()
        await ClockCycles(self.dut.clk, 5)
        await self.deassert_reset()
        await ClockCycles(self.dut.clk, 2)
