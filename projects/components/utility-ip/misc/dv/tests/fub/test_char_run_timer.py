# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""char_run_timer: the characterization run timer and per-channel CRC verdict.

Every output is compared to CharRunTimerModel on every cycle over whole runs
(clean, corrupted on one channel, cleared mid-run, unarmed target). Swept over
the STREAM harness configuration (8 channels, settle 5), a single channel, and
a long settle window as a harness behind a snapshot CDC uses.
"""
import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

sys.path.insert(0, get_repo_root())

from projects.components.utility_ip.misc.dv.tbclasses.char_run_timer_tb import CharRunTimerTB

RUNS = {'gate': 12, 'func': 60, 'full': 300}


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_char_run_timer(dut):
    tb = CharRunTimerTB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    await tb.setup_clocks_and_reset()
    assert await tb.run_all(RUNS.get(level, RUNS['gate'])), \
        f"run_all failed; first error: {tb.errors[0] if tb.errors else '(verdict sweep)'}"
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    # A pass must have exercised both verdicts and compared real cycles.
    assert tb.stats['pass1'] > 0 and tb.stats['pass0'] > 0, tb.stats
    assert tb.stats['cycles_checked'] > 100 * tb.stats['runs'], tb.stats
    assert tb.stats['verdict_cases'] == 4 * tb.nc, tb.stats


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("num_channels, settle_cycles", [(8, 5), (1, 5), (8, 32)])
def test_char_run_timer(request, num_channels, settle_cycles, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = 'char_run_timer'
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/utility-ip/misc/rtl/filelists/char_run_timer.f')
    name = f"test_{dut_name}_nc{num_channels:02d}_st{settle_cycles:02d}_{test_level}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        name = f"{name}_{worker_id}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'NUM_CHANNELS': str(num_channels), 'SETTLE_CYCLES': str(settle_cycles),
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        **level_env(test_level),
    }
    compile_args = ["-Wno-TIMESCALEMOD"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_char_run_timer",
        parameters={'NUM_CHANNELS': num_channels, 'SETTLE_CYCLES': settle_cycles},
        sim_build=sim_build, extra_env=extra_env, waves=enable_waves, keep_files=True,
        compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
