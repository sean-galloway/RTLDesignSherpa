# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: divider_tb_common
# Purpose: Shared cocotb driver/checker for the integer divider family
#          (math_divider_restoring / nonrestoring / srt_radix2 /
#          srt_radix2_csa / srt_radix4).
#
# Documentation: docs/markdown/rtl-math/overview.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-11

"""
Shared testbench utilities for the integer divider family.

Handshake: pulse i_valid for one cycle with the operands; the divider raises
ow_done for one cycle when ow_quotient/ow_remainder (and ow_dbz) are valid.
A new division is accepted only after ow_done (ow_busy is low in idle).

Golden model: Python integer divmod -- exact, independent of the RTL algorithm.
"""

import logging
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles


async def start_clock_and_reset(dut):
    """Start the clock and apply the active-low reset."""
    clock = Clock(dut.i_clk, 10, unit="ns")
    cocotb.start_soon(clock.start())
    dut.i_rst_n.value = 0
    dut.i_valid.value = 0
    dut.i_dividend.value = 0
    dut.i_divisor.value = 0
    await ClockCycles(dut.i_clk, 5)
    dut.i_rst_n.value = 1
    await ClockCycles(dut.i_clk, 2)


async def run_division(dut, x, d, data_width):
    """Pulse i_valid and wait for ow_done. Returns (quotient, remainder, dbz)."""
    dut.i_dividend.value = x
    dut.i_divisor.value = d
    dut.i_valid.value = 1
    await RisingEdge(dut.i_clk)
    dut.i_valid.value = 0
    timeout = 4 * data_width + 100
    for _ in range(timeout):
        await RisingEdge(dut.i_clk)
        if int(dut.ow_done.value) == 1:
            q = int(dut.ow_quotient.value)
            r = int(dut.ow_remainder.value)
            dbz = int(dut.ow_dbz.value)
            return q, r, dbz
    raise AssertionError(
        f"timeout waiting for ow_done (X={x}, D={d}, W={data_width})"
    )


def check_result(dut_name, data_width, x, d, q, r, dbz):
    """Check one division result against the Python golden model."""
    if d == 0:
        assert dbz == 1, (
            f"{dut_name} W={data_width}: X={x} D=0: ow_dbz not set "
            f"(q={q}, r={r})"
        )
        assert q == 0 and r == 0, (
            f"{dut_name} W={data_width}: X={x} D=0: expected q=0 r=0, "
            f"got q={q} r={r}"
        )
        return
    assert dbz == 0, (
        f"{dut_name} W={data_width}: X={x} D={d}: unexpected ow_dbz"
    )
    exp_q, exp_r = divmod(x, d)
    assert q == exp_q and r == exp_r, (
        f"{dut_name} W={data_width}: X={x} D={d}: "
        f"expected q={exp_q} r={exp_r}, got q={q} r={r}"
    )
    assert q * d + r == x and 0 <= r < d


async def divider_suite(dut, dut_name, data_width, level, seed):
    """Full test suite for one divider DUT at one width.

    level: 'gate' | 'func' | 'full'
    """
    random.seed(seed)
    await start_clock_and_reset(dut)
    log = logging.getLogger(dut_name)

    mask = (1 << data_width) - 1
    count = 0

    # ---- directed cases ----
    directed = [
        (0, 1), (0, mask), (1, 1), (1, 2),
        (mask, 1), (mask, 2), (mask, 3), (mask, mask),
        (mask, mask - 1), (mask - 1, mask), (2, mask),
        (3, 2), (mask, 2 ** (data_width - 1)),
        (2 ** (data_width - 1), mask),
        (2 ** (data_width - 1), 2 ** (data_width - 2)),
    ]
    for x, d in directed:
        q, r, dbz = await run_division(dut, x, d, data_width)
        check_result(dut_name, data_width, x, d, q, r, dbz)
        count += 1
    log.info(f"directed: {len(directed)} passed")

    # ---- divide-by-zero ----
    for x in (0, 1, mask, mask // 2):
        q, r, dbz = await run_division(dut, x, 0, data_width)
        check_result(dut_name, data_width, x, 0, q, r, dbz)
        count += 1
    log.info("dbz: 4 passed")

    # ---- random sweep ----
    if level == 'gate':
        n_random = 200
    elif level == 'func':
        n_random = 2000
    else:
        n_random = 5000
    for _ in range(n_random):
        x = random.randint(0, mask)
        d = random.randint(1, mask)
        q, r, dbz = await run_division(dut, x, d, data_width)
        check_result(dut_name, data_width, x, d, q, r, dbz)
        count += 1
    log.info(f"random: {n_random} passed")

    # ---- FULL extras ----
    if level == 'full':
        # Exhaustive at W=8: all (X, D) pairs.
        if data_width == 8:
            for x in range(256):
                for d in range(1, 256):
                    q, r, dbz = await run_division(dut, x, d, data_width)
                    check_result(dut_name, data_width, x, d, q, r, dbz)
                    count += 1
            log.info("exhaustive W=8: 65280 passed")
        # Back-to-back: issue the next i_valid the cycle after ow_done.
        for _ in range(500):
            x = random.randint(0, mask)
            d = random.randint(1, mask)
            q, r, dbz = await run_division(dut, x, d, data_width)
            check_result(dut_name, data_width, x, d, q, r, dbz)
            count += 1
        log.info("back-to-back: 500 passed")

    log.info(f"suite done: {count} checks passed")
