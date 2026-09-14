# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ioapic_deliv_merge
# Purpose: Runner for the multi-IOAPIC delivery merge on two real IOAPIC
#          channels (RLB-008).
#
# Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
# Subsystem: retro_legacy_blocks/ioapic
#
# Created: 2026-09-14

"""System-context test for ioapic_deliv_merge.

The DUT is ioapic_deliv_merge_tb_top (dv/tb/): two apb4_ioapic instances on
distinct APB prefixes, their delivery channels merged onto one receiver. The
merge's own contract is proved by formal with free inputs; this covers the
seam -- see ioapic_merge_tests.py for what it asks and why formal cannot.

Pattern B per GLOBAL_REQUIREMENTS 2.x: the cocotb entry point is prefixed
`cocotb_test_` so pytest does not collect it, and the wrapper names it via
`testcase=`.
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

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_merge_tb import IOAPICMergeTB
from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_merge_tests import IOAPICMergeTests

NUM_SRC = 2


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_merge_seam(dut):
    """Single comprehensive test; TEST_LEVEL selects which seam questions run."""
    tb = IOAPICMergeTB(dut, num_src=NUM_SRC)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'IOAPIC merge seam test with seed: {seed}')

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'

    await tb.setup_clocks_and_reset()
    await tb.setup_components()

    tests = IOAPICMergeTests(tb)

    gate_methods = [
        ('m_src_id names the true origin', tests.test_src_id_names_the_true_origin),
    ]
    func_methods = [
        ('Both sources served when simultaneous', tests.test_both_sources_served_when_simultaneous),
        ('Retry reaches only the refused source', tests.test_retry_reaches_only_the_refused_source),
    ]
    full_methods = [
        ('Backpressure holds the message', tests.test_backpressure_holds_the_message),
    ]

    if test_level == 'gate':
        methods = gate_methods
    elif test_level == 'func':
        methods = gate_methods + func_methods
    else:
        methods = gate_methods + func_methods + full_methods

    tb.log.info(f"Starting {test_level.upper()} IOAPIC merge seam test "
                f"({len(methods)} test(s), NUM_SRC={NUM_SRC})")

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

    assert total > 0, "no seam tests selected -- TEST_LEVEL produced an empty list"
    if passed != total:
        assert False, f"IOAPIC merge seam test failed: {passed}/{total} passed"
    tb.log.info("\nAll IOAPIC merge seam tests PASSED!")


def generate_test_params():
    """REG_LEVEL selects the grid; TEST_LEVEL gates the depth."""
    return [(lvl, f"IOAPIC merge seam {lvl}") for lvl in reg_level_grid()]


@pytest.mark.parametrize("test_level, description", generate_test_params())
def test_ioapic_deliv_merge(request, test_level, description):
    """Pytest wrapper -- calls cocotb_test_merge_seam."""
    module, repo_root_local, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "ioapic_deliv_merge_tb_top"
    test_name_plus_params = f"test_ioapic_deliv_merge_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path='projects/components/retro_legacy_blocks/dv/tb/ioapic_deliv_merge_tb_top.f'
    )

    rtl_parameters = {
        'NUM_IRQS':   '24',
        'CDC_ENABLE': '0',
        'NUM_SRC':    str(NUM_SRC),
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
        'TEST_NUM_SRC': str(NUM_SRC),
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
        testcase="cocotb_test_merge_seam",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
        compile_args=compile_args,
    )
