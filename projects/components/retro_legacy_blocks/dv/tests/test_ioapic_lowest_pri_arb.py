# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ioapic_lowest_pri_arb
# Purpose: Runner for the arbiter companion on a real IOAPIC channel (RLB-008).
#
# Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
# Subsystem: retro_legacy_blocks/ioapic
#
# Created: 2026-09-14

"""System-context test for ioapic_lowest_pri_arb.

The DUT is ioapic_lowest_pri_arb_tb_top (dv/tb/), which wires the arbiter onto
a real apb4_ioapic delivery channel. The arbiter's own contract is proved by
formal; this covers the SEAM -- see ioapic_arb_tests.py for what is deliberately
not re-tested here.

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

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_arb_tb import IOAPICArbTB
from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_arb_tests import IOAPICArbTests

NUM_CPUS = 4


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_arb_seam(dut):
    """Single comprehensive test; TEST_LEVEL selects the depth.

    The level picks which seam questions get asked, following this area's
    runner idiom (the suites themselves do not branch on level).
    """
    tb = IOAPICArbTB(dut, num_cpus=NUM_CPUS)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'IOAPIC arbiter seam test with seed: {seed}')

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'

    await tb.setup_clocks_and_reset()
    await tb.setup_components()

    tests = IOAPICArbTests(tb)

    gate_methods = [
        ('Physical destination reaches that CPU', tests.test_physical_delivery_reaches_that_cpu),
    ]
    func_methods = [
        ('LowestPriority picks one CPU', tests.test_lowest_priority_picks_one_cpu),
        ('Refusal from cpu_can_accept, then delivery', tests.test_no_acceptor_retries_then_delivers),
    ]
    full_methods = [
        ('Fixed signals the whole set', tests.test_fixed_mode_signals_whole_set),
    ]

    if test_level == 'gate':
        methods = gate_methods
    elif test_level == 'func':
        methods = gate_methods + func_methods
    else:
        methods = gate_methods + func_methods + full_methods

    tb.log.info(f"Starting {test_level.upper()} IOAPIC arbiter seam test "
                f"({len(methods)} test(s), NUM_CPUS={NUM_CPUS})")

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
    assert total > 0, "no seam tests selected -- TEST_LEVEL produced an empty list"
    if passed != total:
        assert False, f"IOAPIC arbiter seam test failed: {passed}/{total} passed"
    tb.log.info("\nAll IOAPIC arbiter seam tests PASSED!")


def generate_test_params():
    """REG_LEVEL selects the grid; TEST_LEVEL gates the depth."""
    return [(lvl, f"IOAPIC arbiter seam {lvl}") for lvl in reg_level_grid()]


@pytest.mark.parametrize("test_level, description", generate_test_params())
def test_ioapic_lowest_pri_arb(request, test_level, description):
    """Pytest wrapper -- calls cocotb_test_arb_seam."""
    module, repo_root_local, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "ioapic_lowest_pri_arb_tb_top"
    test_name_plus_params = f"test_ioapic_lowest_pri_arb_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path='projects/components/retro_legacy_blocks/dv/tb/ioapic_lowest_pri_arb_tb_top.f'
    )

    rtl_parameters = {
        'NUM_IRQS':   '24',
        'CDC_ENABLE': '0',
        'NUM_CPUS':   str(NUM_CPUS),
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
        'TEST_IOAPIC_CLOCK_PERIOD': '10',   # CDC_ENABLE=0 ties them together
        'TEST_NUM_CPUS': str(NUM_CPUS),
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
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_arb_seam",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
        compile_args=compile_args,
    )
