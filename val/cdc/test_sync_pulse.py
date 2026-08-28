# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: test_sync_pulse
# Purpose: Test runner for sync_pulse (CDC toggle pulse synchronizer)
# Subsystem: tests
#
# This module had no simulation test until 2026-08-07. It was found by the
# first line-coverage measurement of val/common: sync_pulse.sv produced no
# coverage rows, and unlike the other absentees it had no test to explain it.
#
# It is not a spare part: cdc_counter_display's cdc_counter_domain.sv
# instantiates it three times to move pulses across clock domains.

import os
import random

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.cdc.sync_pulse_tb import SyncPulseTB
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def sync_pulse_test(dut):
    """One destination pulse per source pulse, across clock ratios."""
    tb = SyncPulseTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_test()
    await tb.run_reset_mid_stream()


def generate_params():
    """REG_LEVEL grid: synchroniser depth x source/destination clock ratio.

    The ratios matter more than the depth here -- a toggle synchroniser has to
    deliver 1:1 whether the destination is faster, slower or equal, and the
    slow-destination case is the one that loses pulses if the design is wrong.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        combos = [(3, 10, 10)]
        levels = ['gate']
    elif reg_level == 'FUNC':
        combos = [(3, 10, 10), (2, 10, 27), (4, 27, 10)]
        levels = ['func']
    else:  # FULL
        combos = [(2, 10, 10), (3, 10, 10), (4, 10, 10),
                  (3, 10, 33), (3, 33, 10), (2, 7, 23), (4, 23, 7)]
        levels = ['full']

    return [(s, sp, dp, lv) for (s, sp, dp) in combos for lv in levels]


@pytest.mark.parametrize("sync_stages, src_period, dst_period, test_level",
                         generate_params())
def test_sync_pulse(request, sync_stages, src_period, dst_period, test_level):
    """Pytest wrapper for sync_pulse."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cdc': 'rtl/cdc'})

    dut_name = "sync_pulse"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/cdc/filelists/sync_pulse.f')

    s_str = TBBase.format_dec(sync_stages, 1)
    sp_str = TBBase.format_dec(src_period, 2)
    dp_str = TBBase.format_dec(dst_period, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = (f"test_{dut_name}_s{s_str}_sp{sp_str}_dp{dp_str}"
                             f"_{test_level}_{reg_level}")

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    parameters = {'SYNC_STAGES': sync_stages}

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'TEST_LEVEL': test_level,
        'PARAM_SYNC_STAGES': str(sync_stages),
        'TEST_SRC_PERIOD': str(src_period),
        'TEST_DST_PERIOD': str(dst_period),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    # Verilator --coverage flags when COVERAGE=1, else nothing.
    extra_args.extend(get_coverage_compile_args())

    sim_args = ['--trace'] if enable_waves else []
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module,
                                   test_name_plus_params)

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
        print(f"sync_pulse test failed: {e}")
        print(f"SYNC_STAGES={sync_stages}, src={src_period}ns, dst={dst_period}ns")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        raise
