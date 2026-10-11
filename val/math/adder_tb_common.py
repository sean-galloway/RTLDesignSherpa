# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: adder_tb_common
# Purpose: Shared cocotb checker for combinational adder modules
#          (used by the hybrid ripple-prefix adder wrapper tests).
#
# Documentation: docs/markdown/rtl-math/overview.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-11

"""
Shared testbench utilities for combinational adder modules.

Golden model: Python integer addition -- exact, independent of the adder
architecture (ripple, prefix, or hybrid).
"""

import logging
import random

from cocotb.triggers import Timer


async def adder_check_one(dut, a, b, c_in, n):
    """Drive one vector, settle, and check against the Python golden model."""
    mask = (1 << n) - 1
    dut.i_a.value = a
    dut.i_b.value = b
    dut.i_c.value = c_in
    await Timer(1, unit="ns")
    total = a + b + c_in
    exp_sum = total & mask
    exp_carry = 1 if total > mask else 0
    got_sum = int(dut.ow_sum.value)
    got_carry = int(dut.ow_carry.value)
    assert got_sum == exp_sum and got_carry == exp_carry, (
        f"adder mismatch: n={n} a={a} b={b} c_in={c_in}: "
        f"expected sum={exp_sum} carry={exp_carry}, "
        f"got sum={got_sum} carry={got_carry}"
    )


async def adder_suite(dut, n, level, seed):
    """Directed + random sweep for an n-bit combinational adder."""
    random.seed(seed)
    log = logging.getLogger("adder_tb_common")
    mask = (1 << n) - 1

    alt_a = int('10' * ((n + 1) // 2), 2) & mask
    alt_b = int('01' * ((n + 1) // 2), 2) & mask

    directed = [
        (0, 0, 0), (0, 0, 1), (mask, mask, 0), (mask, mask, 1),
        (mask, 0, 1), (0, mask, 0), (1, 1, 1), (1, 1, 0),
        (mask - 1, 1, 1), (alt_a, alt_b, 1), (alt_a, alt_b, 0),
    ]
    if n >= 2:
        directed.append(((1 << (n - 1)), (1 << (n - 1)), 1))
    for a, b, c in directed:
        await adder_check_one(dut, a, b, c, n)
    log.info(f"directed: {len(directed)} passed")

    if level == 'gate':
        n_random = 500
    elif level == 'func':
        n_random = 5000
    else:
        n_random = 50000
    for _ in range(n_random):
        await adder_check_one(
            dut, random.randint(0, mask), random.randint(0, mask),
            random.randint(0, 1), n)
    log.info(f"random: {n_random} passed")
