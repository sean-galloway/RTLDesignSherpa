# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_age_fifo_sync
# Purpose: gaxi_age_fifo_sync runner - REG_LEVEL grid + cocotb_test.run();
#          the test itself is GaxiAgeFifoTB.run_suite
#
# Documentation: docs/markdown/rtl-amba/gaxi/gaxi_age_fifo_sync.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-25
"""gaxi_age_fifo_sync runner: the parameter grid and run().

REG_LEVEL selects the grid: GATE 1 cell, FUNC 4 cells, FULL 48 cells.
TEST_LEVEL gates the depth inside GaxiAgeFifoTB.run_suite (gate / func / full).
The stimulus and checks live in bin/TBClasses/gaxi/gaxi_age_fifo.py; the
age-carrying BFM wrappers in bin/TBClasses/gaxi/gaxi_age_bfm.py.
"""

import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.gaxi.gaxi_age_fifo import GaxiAgeFifoTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def gaxi_age_fifo_sync_test(dut):
    tb = GaxiAgeFifoTB(dut, dut.axi_aclk, dut.axi_aresetn)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if level not in ('gate', 'func', 'full'):
        level = 'gate'
    await tb.setup_clocks_and_reset()
    ok = await tb.run_suite(level)
    assert ok, f"{len(tb.errors)} violation(s):\n  " + "\n  ".join(tb.errors[:20])


def generate_test_params():
    """(data_width, age_width, depth, test_level) per REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(8, 4, 4, 'gate')]
    if reg_level == 'FUNC':
        return [(8, 4, 4, 'gate'), (8, 4, 4, 'func'),
                (32, 8, 8, 'func'), (8, 3, 5, 'func')]
    return list(product([8, 32], [3, 8], [3, 4, 8, 11], ['gate', 'func', 'full']))


params = generate_test_params()


@pytest.mark.parametrize("data_width, age_width, depth, test_level", params)
def test_gaxi_age_fifo_sync(request, data_width, age_width, depth, test_level):
    """Parameterized gaxi_age_fifo_sync test."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
    })
    dut_name = "gaxi_age_fifo_sync"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, module=dut_name)

    w_str = TBBase.format_dec(data_width, 3)
    a_str = TBBase.format_dec(age_width, 2)
    d_str = TBBase.format_dec(depth, 3)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = (f"test_{worker_id}_{dut_name}_w{w_str}_a{a_str}"
                             f"_d{d_str}_{test_level}_{reg_level}")
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'AGE_WIDTH': str(age_width),
        'DEPTH': str(depth),
    }
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AGE_WIDTH': str(age_width),
        'TEST_DEPTH': str(depth),
    }
    compile_args = ["--trace", "--trace-depth", "99"]
    compile_args.extend(get_coverage_compile_args())
    sim_args = ["--trace", "--trace-depth", "99"]
    plus_args = ["--trace"]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}\nRunning {test_level.upper()} test: {dut_name} "
          f"depth={depth} width={data_width} age_width={age_width}\nLog: {log_path}\n{'='*80}")
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=bool(int(os.environ.get('WAVES', '0'))),
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
        print(f"{test_level.upper()} test PASSED: {dut_name}")
    except Exception as e:
        print(f"{test_level.upper()} test FAILED: {dut_name}: {e}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
