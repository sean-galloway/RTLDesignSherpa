# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rlb_top
# Purpose: Light integration smoke tests for rlb_top -- every peripheral
#          present, decoded and answering on its own 4KB window.
#
# Documentation: projects/components/retro_legacy_blocks/rtl/rlb_top/
# Subsystem: retro_legacy_blocks/rlb_top
#
# Created: 2026-09-14

"""Integration smoke tests for the whole RLB subsystem.

WHY THIS EXISTS: until now NOTHING elaborated rlb_top -- no test, no make
target. Ports could be added to a block and left unconnected here and the
suite stayed green; that is exactly how two PINMISSING breaks reached the
tree. These tests are deliberately LIGHT. Each block already has its own
suite (75 cells across the area); re-verifying them here would be slow and
would duplicate coverage. What is NOT covered anywhere else is the
integration: that all ten windows decode to the right slave, that each slave
is actually wired up and answers, and that the cross-block paths work.

Pattern B per GLOBAL_REQUIREMENTS 2.x: the cocotb entry point is prefixed
`cocotb_test_` so pytest does not collect it, and the pytest wrapper names it
explicitly via `testcase=`.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.retro_legacy_blocks.dv.tbclasses.rlb_top.rlb_top_tb import RLBTopTB
from projects.components.retro_legacy_blocks.dv.tbclasses.rlb_top.rlb_top_tests import (
    RLBTopTests,
)


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_rlb_top_smoke(dut):
    """Single comprehensive test; TEST_LEVEL selects the depth."""
    tb = RLBTopTB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'RLB top integration smoke test with seed: {seed}')

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'

    await tb.setup_clocks_and_reset()
    await tb.setup_components()

    tests = RLBTopTests(tb)

    gate_methods = [
        ('Every window answers', tests.test_every_window_answers),
    ]
    func_methods = [
        ('Reserved window errors with DEADBEEF',
         tests.test_reserved_window_errors),
        ('Decode isolation across windows',
         tests.test_decode_isolation),
    ]
    full_methods = [
        ('Boot interrupt reaches the 8259',
         tests.test_boot_interrupt_reaches_the_pic),
    ]

    if test_level == 'gate':
        methods = gate_methods
    elif test_level == 'func':
        methods = gate_methods + func_methods
    else:
        methods = gate_methods + func_methods + full_methods

    tb.log.info(f"Starting {test_level.upper()} RLB top smoke test "
                f"({len(methods)} test(s))")

    results = []
    for name, method in methods:
        tb.log.info("\n" + "=" * 80)
        tb.log.info(f"Running: {name}")
        tb.log.info("=" * 80)
        results.append((name, await method()))

    tb.log.info("\n" + "=" * 80)
    tb.log.info("TEST SUMMARY")
    tb.log.info("=" * 80)
    for name, ok in results:
        tb.log.info(f"{name:52s} {'PASSED' if ok else 'FAILED'}")

    passed = sum(1 for _, ok in results if ok)
    total = len(results)
    tb.log.info(f"\nPassed: {passed}/{total}")

    # A run that asked nothing is not a pass.
    assert total > 0, "no smoke tests selected -- TEST_LEVEL produced an empty list"
    if passed != total:
        assert False, f"RLB top smoke test failed: {passed}/{total} passed"
    tb.log.info("\nAll RLB top integration smoke tests PASSED!")


def generate_test_params():
    """REG_LEVEL selects the grid; TEST_LEVEL gates the depth."""
    return [(lvl, f"RLB top smoke {lvl}") for lvl in reg_level_grid()]


@pytest.mark.parametrize("test_level, description", generate_test_params())
def test_rlb_top(request, test_level, description):
    """Pytest wrapper -- calls cocotb_test_rlb_top_smoke."""
    module, repo_root_local, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "rlb_top"
    test_name_plus_params = f"test_rlb_top_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path='projects/components/retro_legacy_blocks/rtl/rlb_top/rlb_top.f'
    )

    rtl_parameters = {
        'IOAPIC_NUM_IRQS':  '24',
        'HPET_NUM_TIMERS':  '2',
        'PIT_NUM_COUNTERS': '3',
        'GPIO_WIDTH':       '32',
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        'TEST_APB_CLOCK_PERIOD': '10',
    }

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "--timescale", "1ns/1ps",
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND", "-Wno-CASEINCOMPLETE",
        "-Wno-BLKANDNBLK", "-Wno-MULTIDRIVEN", "-Wno-TIMESCALEMOD",
        "-Wno-MODDUP", "-Wno-GENUNNAMED", "-Wno-PINCONNECTEMPTY",
        "-Wno-UNUSEDSIGNAL", "-Wno-UNUSEDPARAM", "-Wno-SYNCASYNCNET",
        "-Wno-DECLFILENAME", "-Wno-VARHIDDEN",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_rlb_top_smoke",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
        compile_args=compile_args,
    )
