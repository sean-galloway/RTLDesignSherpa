# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_pic_8259_cascade
# Purpose: Runner for the 8259 PC/AT cascade pair (RLB/pic_8259 TASK-001).
#
# Documentation: projects/components/retro_legacy_blocks/rtl/pic_8259/README.md
# Subsystem: retro_legacy_blocks/pic_8259
#
# Created: 2026-09-28

"""Cascade test for the 8259 master/slave pair.

The DUT is pic_8259_cascade_tb_top (dv/tb/), which instantiates TWO
apb4_pic_8259 in the PC/AT arrangement: the slave's int_out drives master IR2,
and cas_ack / cas_vector cross-connect so the master's PIC_INTA read returns
the slave's vector and retires the level in both controllers.

This exists because the block's own DUT is a BARE apb4_pic_8259 -- two PICs
cannot be instantiated in that harness at all, which is why the cascade RTL
landed with no coverage.

Both PICs sit behind ONE APB port: PADDR[11] is the wrapper's chip select, so
the slave's registers are at +0x800 and PIC8259TB binds unchanged.

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

from projects.components.retro_legacy_blocks.dv.tbclasses.pic_8259.pic_8259_tb import PIC8259TB
from projects.components.retro_legacy_blocks.dv.tbclasses.pic_8259.pic_8259_cascade_tests import (
    PIC8259CascadeTests,
)


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_pic_cascade(dut):
    """Single comprehensive test; TEST_LEVEL selects the depth."""
    tb = PIC8259TB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'PIC 8259 cascade test with seed: {seed}')

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'

    await tb.setup_clocks_and_reset()
    await tb.setup_components()

    tests = PIC8259CascadeTests(tb)

    # The two criteria the cascade RTL landed WITHOUT coverage for are the
    # gate pair: the slave raising the master, and the master's read returning
    # the slave's vector. Everything else builds on those.
    gate_methods = [
        ('Cascade init: both PICs, ICW3 written, SNGL clear',
         tests.test_cascade_initialization),
        ('Slave INT raises the master on its cascade level',
         tests.test_slave_int_raises_master),
    ]
    func_methods = [
        ('Master INTA returns the SLAVE vector, not its own',
         tests.test_master_inta_returns_slave_vector),
        ('Masking the cascade level blocks the slave',
         tests.test_masked_cascade_level_blocks_slave),
    ]
    full_methods = [
        ('EOI retires the level in BOTH controllers',
         tests.test_eoi_retires_both),
        ('A non-cascade master level still returns the MASTER vector',
         tests.test_non_cascade_level_unaffected),
    ]

    if test_level == 'gate':
        methods = gate_methods
    elif test_level == 'func':
        methods = gate_methods + func_methods
    else:
        methods = gate_methods + func_methods + full_methods

    tb.log.info(f"Starting {test_level.upper()} PIC cascade test "
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
        tb.log.info(f"{name:58s} {'PASSED' if ok else 'FAILED'}")

    passed = sum(1 for _, ok in results if ok)
    total = len(results)
    tb.log.info(f"\nPassed: {passed}/{total}")

    # A run that asked nothing is not a pass.
    assert total > 0, "no cascade tests selected -- TEST_LEVEL produced an empty list"
    if passed != total:
        assert False, f"PIC 8259 cascade test failed: {passed}/{total} passed"
    tb.log.info("\nAll PIC 8259 cascade tests PASSED!")


def generate_test_params():
    """REG_LEVEL selects the grid; TEST_LEVEL gates the depth."""
    return [(lvl, f"PIC 8259 cascade {lvl}") for lvl in reg_level_grid()]


@pytest.mark.parametrize("test_level, description", generate_test_params())
def test_pic_8259_cascade(request, test_level, description):
    """Pytest wrapper -- calls cocotb_test_pic_cascade."""
    module, repo_root_local, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "pic_8259_cascade_tb_top"
    test_name_plus_params = f"test_pic_8259_cascade_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path='projects/components/retro_legacy_blocks/dv/tb/pic_8259_cascade_tb_top.f'
    )

    rtl_parameters = {
        'SYNC_STAGES': '2',
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
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_pic_cascade",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
        compile_args=compile_args,
    )
