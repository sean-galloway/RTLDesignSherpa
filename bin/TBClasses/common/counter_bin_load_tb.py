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
from cocotb.triggers import ClockCycles, RisingEdge

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
        # add_enable/add_value were never driven at all before 2026-08-08,
        # which is how the entire variable-increment branch stayed at zero
        # coverage. Park them with everything else.
        self.dut.add_enable.value = 0
        self.dut.add_value.value = 0

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

    # ---- variable increment (add_enable) ---------------------------------

    async def load_to(self, value):
        """Put the counter at a known value via the load port."""
        self.dut.load.value = 1
        self.dut.load_value.value = value
        await RisingEdge(self.dut.clk)
        self.dut.load.value = 0
        await RisingEdge(self.dut.clk)
        got = int(self.dut.counter_bin_curr.value)
        assert got == value, f"load_to({value}) left the counter at {got}"

    async def add_once(self, addend):
        """One add_enable step; returns the counter value after it lands."""
        self.dut.add_enable.value = 1
        self.dut.add_value.value = addend
        await RisingEdge(self.dut.clk)
        self.dut.add_enable.value = 0
        self.dut.add_value.value = 0
        await RisingEdge(self.dut.clk)
        return int(self.dut.counter_bin_curr.value)

    async def test_variable_increment(self):
        """Exercise add_enable, both the wrapping and non-wrapping arms.

        The counter is a FIFO pointer: it counts modulo WRAP_BOUNDARY = 2*MAX,
        and the MSB-carrying wrap is what separates full from empty. So an add
        that crosses 2*MAX must land at sum - 2*MAX, not saturate and not
        simply truncate.
        """
        wrap = 2 * self.MAX
        cases = []

        # No-wrap arm: start + addend stays under 2*MAX.
        cases.append((0, 1))
        cases.append((0, self.MAX - 1))
        cases.append((1, self.MAX))

        # Wrap arm: start + addend reaches or passes 2*MAX.
        cases.append((wrap - 1, 1))                 # exactly on the boundary
        cases.append((self.MAX, self.MAX))          # exactly 2*MAX
        cases.append((wrap - 2, 3))                 # just past it

        if self.LEVEL_MULT > 1:
            # func/full also sweep every addend that fits, from a few starts.
            span = min(wrap, (1 << self.WIDTH))
            starts = [0, self.MAX // 2, self.MAX, wrap - 1]
            for st in starts:
                for add in range(0, span, max(1, span // (4 * self.LEVEL_MULT))):
                    cases.append((st % span, add))

        checked = 0
        for start, addend in cases:
            if start >= (1 << self.WIDTH) or addend >= (1 << self.WIDTH):
                continue
            await self.load_to(start)
            got = await self.add_once(addend)
            expected = (start + addend) % wrap
            assert got == expected, (
                f"add_enable: {start} + {addend} gave {got}, expected "
                f"{expected} (WIDTH={self.WIDTH}, MAX={self.MAX}, "
                f"wrap boundary={wrap}). "
                f"{'wrapping' if start + addend >= wrap else 'non-wrapping'} arm")
            checked += 1

        assert checked, "no add_enable case was legal for this configuration"
        self.log.info(f"counter_bin_load: {checked} variable-increment case(s) "
                      f"checked across both wrap arms")

    async def test_add_priority(self):
        """load beats add_enable, and add_enable beats enable."""
        await self.load_to(1)

        # load wins over add
        self.dut.add_enable.value = 1
        self.dut.add_value.value = 3
        self.dut.load.value = 1
        self.dut.load_value.value = 7
        await RisingEdge(self.dut.clk)
        self.dut.load.value = 0
        self.dut.add_enable.value = 0
        self.dut.add_value.value = 0
        await RisingEdge(self.dut.clk)
        got = int(self.dut.counter_bin_curr.value)
        assert got == 7, f"load must beat add_enable: got {got}, expected 7"

        # add wins over enable
        self.dut.add_enable.value = 1
        self.dut.add_value.value = 4
        self.dut.enable.value = 1
        await RisingEdge(self.dut.clk)
        self.dut.add_enable.value = 0
        self.dut.add_value.value = 0
        self.dut.enable.value = 0
        await RisingEdge(self.dut.clk)
        got = int(self.dut.counter_bin_curr.value)
        expected = (7 + 4) % (2 * self.MAX)
        assert got == expected, (
            f"add_enable must beat enable (a +1 would give "
            f"{(7 + 1) % (2 * self.MAX)}): got {got}, expected {expected}")

        self.log.info("counter_bin_load: load > add_enable > enable priority holds")
