# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ioapic_boot_intx
# Purpose: Runner for the boot-interrupt companion on a real IOAPIC (RLB-008).
#
# Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
# Subsystem: retro_legacy_blocks/ioapic
#
# Created: 2026-09-14

"""System-context test for ioapic_boot_intx.

The DUT is ioapic_boot_intx_tb_top (dv/tb/), which wires the companion onto a
real apb4_ioapic's exported mask vector and its own enable register. The
companion's contract is proved by formal; this covers the SEAM -- see
ioapic_boot_intx_tests.py for what is deliberately not re-tested here.

Unlike the arb / merge / msi_emit runners this one uses IOAPICTB unchanged:
ioapic_boot_intx never touches irq_out_ready or irq_out_retry, so the
testbench keeps the delivery handshake it normally owns.

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

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import IOAPICTB
from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_boot_intx_tests import (
    IOAPICBootIntxTests,
)


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_boot_intx_seam(dut):
    """Single comprehensive test; TEST_LEVEL selects the depth."""
    tb = IOAPICTB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'IOAPIC boot-intx seam test with seed: {seed}')

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'

    await tb.setup_clocks_and_reset()
    await tb.setup_components()

    tests = IOAPICBootIntxTests(tb)

    gate_methods = [
        ('Masked pin reroutes to its legacy input',
         tests.test_masked_pin_reroutes_to_its_legacy_input),
    ]
    func_methods = [
        ('Unmasked pin does not reroute',
         tests.test_unmasked_pin_does_not_reroute),
        ('Disable stops rerouting',
         tests.test_disable_stops_rerouting),
    ]
    full_methods = [
        ('Unmapped pin reaches no legacy input',
         tests.test_unmapped_pin_reaches_no_legacy_input),
    ]

    if test_level == 'gate':
        methods = gate_methods
    elif test_level == 'func':
        methods = gate_methods + func_methods
    else:
        methods = gate_methods + func_methods + full_methods

    tb.log.info(f"Starting {test_level.upper()} IOAPIC boot-intx seam test "
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
    assert total > 0, "no seam tests selected -- TEST_LEVEL produced an empty list"
    if passed != total:
        assert False, f"IOAPIC boot-intx seam test failed: {passed}/{total} passed"
    tb.log.info("\nAll IOAPIC boot-intx seam tests PASSED!")


def generate_test_params():
    """REG_LEVEL selects the grid; TEST_LEVEL gates the depth."""
    return [(lvl, f"IOAPIC boot-intx seam {lvl}") for lvl in reg_level_grid()]


@pytest.mark.parametrize("test_level, description", generate_test_params())
def test_ioapic_boot_intx(request, test_level, description):
    """Pytest wrapper -- calls cocotb_test_boot_intx_seam."""
    module, repo_root_local, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "ioapic_boot_intx_tb_top"
    test_name_plus_params = f"test_ioapic_boot_intx_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path='projects/components/retro_legacy_blocks/dv/tb/ioapic_boot_intx_tb_top.f'
    )

    rtl_parameters = {
        'NUM_IRQS':   '24',
        'CDC_ENABLE': '0',
        'NUM_PIC':    '8',
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
        testcase="cocotb_test_boot_intx_seam",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
        compile_args=compile_args,
    )
