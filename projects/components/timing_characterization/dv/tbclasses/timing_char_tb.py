"""
Timing Characterization Testbench Base Class

Provides shared testbench functionality for all timing characterization FUBs.
Each FUB test creates this TB (or a subclass) and uses it to drive clocks,
assert/deassert reset, and perform basic functional checks.

Since timing characterization modules are simple (input flops -> combinational
logic -> output flops), the testbench primarily verifies that outputs toggle
correctly when inputs change, confirming the combinational path is not
optimized away.

Also provides a Python reference model for the left-shift Galois LFSR used
in char_top.sv (polynomial x^32 + x^22 + x^2 + x + 1, constant 0x0040_0007).
"""

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


# =========================================================================
# Left-shift Galois LFSR reference model (matches char_top.sv)
# =========================================================================
# char_top uses: r_lfsr <= {r_lfsr[30:0], 1'b0} ^ (r_lfsr[31] ? 32'h0040_0007 : 0);
# This is NOT the same as the right-shift tap-based Galois LFSR in
# val/common/test_shifter_lfsr_galois.py -- different architecture entirely.

CHAR_TOP_LFSR_POLY = 0x0040_0007
CHAR_TOP_LFSR_DEFAULT_SEED = 0xDEAD_BEEF


def lfsr_step(state, poly=CHAR_TOP_LFSR_POLY):
    """Single step of the 32-bit left-shift Galois LFSR.

    Matches the RTL:
        r_lfsr <= {r_lfsr[30:0], 1'b0} ^ (r_lfsr[31] ? poly : 0);

    Args:
        state: Current 32-bit LFSR state.
        poly:  Feedback polynomial (default: char_top polynomial).

    Returns:
        Next 32-bit LFSR state.
    """
    feedback = (state >> 31) & 1
    shifted = (state << 1) & 0xFFFF_FFFF
    if feedback:
        shifted ^= poly
    return shifted


def lfsr_sequence(seed, count, poly=CHAR_TOP_LFSR_POLY):
    """Build a list of LFSR states: [seed, step(seed), ...].

    Args:
        seed:  Initial LFSR value (loaded via i_seed_valid).
        count: Total number of entries to return.
        poly:  Feedback polynomial (default: char_top polynomial).

    Returns:
        List of length *count* with LFSR states.
    """
    states = [seed]
    s = seed
    for _ in range(count - 1):
        s = lfsr_step(s, poly)
        states.append(s)
    return states


def bit(val, idx):
    """Extract bit *idx* from integer *val*."""
    return (val >> idx) & 1


class TimingCharTB(TBBase):
    """Base testbench for timing characterization FUBs.

    All timing characterization modules share:
    - clk / rst_n interface
    - Input flops -> combinational logic -> output flops
    - 2-cycle pipeline latency (input FF + output FF)
    """

    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.clk
        self.rst_n = dut.rst_n

    async def setup_clocks_and_reset(self):
        """Standard initialization: start clock, assert reset, release."""
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        """Assert active-low reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert active-low reset."""
        self.dut.rst_n.value = 1

    async def wait_pipeline(self, cycles=3):
        """Wait for pipeline to flush (input FF + comb + output FF)."""
        await ClockCycles(self.clk, cycles)

    async def toggle_and_check(self, drive_fn, read_fn, num_toggles=20):
        """Generic toggle test: drive inputs, wait pipeline, read outputs.

        Args:
            drive_fn: async callable(cycle_num) that drives DUT inputs
            read_fn:  callable() that returns current output value
            num_toggles: number of toggle cycles

        Returns:
            True if output changed at least once (not stuck)
        """
        seen_values = set()
        for i in range(num_toggles):
            await drive_fn(i)
            await self.wait_pipeline()
            val = read_fn()
            seen_values.add(val)

        # Output should have changed at least once
        return len(seen_values) > 1
