# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_adder_hybrid_ripple_prefix
# Purpose: Test for the parameterized hybrid ripple-prefix adder module.
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-11

"""
Test for the parameterized hybrid ripple-prefix adder module.
"""
import os
import random
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


def _param_grid():
    """Parameter grid based on REG_LEVEL.

    Default build uses N=32/RIPPLE_BITS=8.  FULL adds a sweep across valid
    (N, RIPPLE_BITS) combinations to exercise the core's parameter space.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    # (N, RIPPLE_BITS, random_count_override)
    grid = [(32, 8, None)]
    if reg_level == 'FULL':
        for n in (8, 32):
            for r in (1, 2, 3, n // 2, n - 1):
                grid.append((n, r, 2000))
    return grid


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def adder_test(dut):
    """Test the hybrid ripple-prefix adder."""
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)

    n = int(os.environ.get('PARAM_N', '32'))
    mask = (1 << n) - 1
    max_val = 1 << n

    count_override = os.environ.get('PARAM_RANDOM_COUNT', '')
    if count_override:
        random_count = int(count_override)
    else:
        level = os.environ.get('TEST_LEVEL', 'func').lower()
        if level == 'gate':
            random_count = 500
        elif level == 'full':
            random_count = 50000
        else:
            random_count = 5000

    log = dut._log
    log.info(f"Hybrid ripple-prefix adder test: N={n} seed={seed} random_count={random_count}")

    directed = []

    # Basic corner cases
    directed.extend([(0, 0, 0), (0, 0, 1)])
    directed.extend([(mask, mask, 0), (mask, mask, 1)])

    # Alternating patterns
    alt_even = sum(1 << i for i in range(0, n, 2)) & mask
    alt_odd = sum(1 << i for i in range(1, n, 2)) & mask
    directed.extend([
        (alt_even, alt_odd, 0),
        (alt_even, alt_odd, 1),
        (alt_odd, alt_even, 0),
        (alt_odd, alt_even, 1),
        (alt_even, alt_even, 0),
        (alt_odd, alt_odd, 1),
    ])

    # Powers of two against zero/self with both carry values
    for i in range(n):
        p = (1 << i) & mask
        directed.extend([
            (p, 0, 0),
            (0, p, 1),
            (p, p, 0),
        ])

    # Walking-ones pair with i_c sweep
    for i in range(n):
        a = (1 << i) & mask
        b = (1 << ((i + 1) % n)) & mask
        for c in (0, 1):
            directed.append((a, 0, c))
            directed.append((0, a, c))
            directed.append((a, b, c))

    # De-duplicate while preserving order
    seen = set()
    unique_directed = []
    for vec in directed:
        if vec not in seen:
            seen.add(vec)
            unique_directed.append(vec)
    directed = unique_directed

    pass_count = 0
    fail_count = 0

    async def check(a, b, c_in):
        nonlocal pass_count, fail_count
        dut.i_a.value = a
        dut.i_b.value = b
        dut.i_c.value = c_in
        await Timer(1, units='ns')

        ow_sum = int(dut.ow_sum.value)
        ow_carry = int(dut.ow_carry.value)

        total = a + b + (1 if c_in else 0)
        expected_sum = total & mask
        expected_carry = 1 if total >= max_val else 0

        if ow_sum != expected_sum or ow_carry != expected_carry:
            fail_count += 1
            log.error(f"FAILED: a={a} b={b} c={c_in}")
            log.error(f"  expected sum={expected_sum} carry={expected_carry}")
            log.error(f"  actual   sum={ow_sum} carry={ow_carry}")
            log.error(f"  a      = {bin(a)[2:].zfill(n)}")
            log.error(f"  b      = {bin(b)[2:].zfill(n)}")
            log.error(f"  c_in   = {c_in}")
            log.error(f"  exp_sum= {bin(expected_sum)[2:].zfill(n)}")
            log.error(f"  act_sum= {bin(ow_sum)[2:].zfill(n)}")
            assert False, (
                f"Adder test failed: a={a}, b={b}, c_in={c_in}\n"
                f"Expected: sum={expected_sum}, carry={expected_carry}\n"
                f"Got: sum={ow_sum}, carry={ow_carry}"
            )
        else:
            pass_count += 1

    # Directed tests
    for a, b, c in directed:
        await check(a, b, c)

    # Random tests vs Python golden
    for _ in range(random_count):
        a = random.randint(0, mask)
        b = random.randint(0, mask)
        c = random.randint(0, 1)
        await check(a, b, c)

    log.info(f"Test summary: {pass_count} passed, {fail_count} failed")
    assert fail_count == 0, f"{fail_count} check(s) failed"


@pytest.mark.parametrize("n, ripple_bits, random_override", _param_grid())
def test_math_adder_hybrid_ripple_prefix(request, n, ripple_bits, random_override):
    """PyTest function to run the cocotb test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "math_adder_hybrid_ripple_prefix"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module=dut_name
    )

    parameters = {'N': n, 'RIPPLE_BITS': ripple_bits}

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_N{n}_R{ripple_bits}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)

    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': test_level,
        'PARAM_N': str(n),
        'PARAM_RIPPLE_BITS': str(ripple_bits),
    }

    if random_override is not None:
        extra_env['PARAM_RANDOM_COUNT'] = str(random_override)

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,
            waves=enable_waves,
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise
