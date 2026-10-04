# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Testbench for the andesite infra smoke module.

Deliberately minimal: the smoke test's job is to prove the cocotb + verilator
pipeline end-to-end, so this class drives its own clock rather than pulling in
TBBase. The block-level testbenches (Tasks 3-5) drive their own clocks and protocol checks.
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge


class AndesiteSmokeTB:
    def __init__(self, dut):
        self.dut = dut

    async def setup_clock(self, period_ns=10):
        self._clk = Clock(self.dut.clk, period_ns, units="ns")
        await cocotb.start(self._clk.start())

    async def reset(self, cycles=3):
        self.dut.rst_n.value = 0
        for _ in range(cycles):
            await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        await RisingEdge(self.dut.clk)

    async def tick(self, n=1):
        for _ in range(n):
            await RisingEdge(self.dut.clk)
