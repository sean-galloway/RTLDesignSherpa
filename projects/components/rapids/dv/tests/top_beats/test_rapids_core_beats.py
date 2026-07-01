# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_core_beats
# Purpose: RAPIDS Core (beats) TOP-level integration test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_top_beats
#
# Author: sean galloway
# Created: 2026-06-30

"""
RAPIDS Core (beats) top-level integration test.

DUT: rapids_core_beats  (scheduler_group_array + sink_data_path + source_data_path)

Test types (dispatched by TEST_TYPE):
  smoke          : reset/config/one APB kick; verify descriptor fetch + system idle
  single_channel : one end-to-end DMA with source+sink data-integrity scoreboard
  multi_channel  : concurrent multi-channel DMA
  stress         : back-to-back transfers across all channels

The runner is a thin dispatcher; all stimulus/checking lives in
RapidsCoreBeatsTB. timing_profile sweeps the AXI memory-slave + GAXI fill/APB
timing (REG_LEVEL-gated).
"""

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.rapids.dv.tbclasses.rapids_core_beats_tb import RapidsCoreBeatsTB


# ===========================================================================
# COCOTB TEST FUNCTIONS - thin; logic lives in the TB
# ===========================================================================

@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_smoke(dut):
    """Bring-up: reset, config, one descriptor kick; system returns to idle."""
    tb = RapidsCoreBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    src, dst, patt = await tb._run_channel_transfer(channel=0, beats=4)
    idle = await tb.wait_system_idle(timeout_cycles=20000)
    tb.finalize_test()
    tb.log.info(f"smoke: system_idle={idle}, mon_packets={len(tb.mon_packets)}, "
                f"drained_ch0={len(tb.drained[0])}")
    assert not tb.test_errors, f"smoke errors: {tb.test_errors}"


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_single_channel(dut):
    """Single-channel end-to-end DMA with data-integrity scoreboard."""
    tb = RapidsCoreBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    ok, stats = await tb.test_single_channel(channel=0, beats=8)
    tb.finalize_test()
    assert ok, f"single-channel E2E failed: {stats.get('errors')}"


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_multi_channel(dut):
    """Concurrent multi-channel end-to-end DMA."""
    tb = RapidsCoreBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    ok, stats = await tb.test_multi_channel(num_channels=4, beats=4)
    tb.finalize_test()
    assert ok, f"multi-channel E2E failed: {stats.get('errors')}"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_stress(dut):
    """Back-to-back transfers across channels."""
    tb = RapidsCoreBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    ok, stats = await tb.stress_test(num_transfers=16, beats=4)
    tb.finalize_test()
    assert ok, f"stress E2E failed: {stats.get('errors')}"


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_params():
    """(test_type, data_width, timing_profile). REG_LEVEL gates the profile sweep."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        data_widths = [512]
        sweep_profiles = []
    elif reg_level == 'FUNC':
        data_widths = [512]
        sweep_profiles = ['slow_producer', 'gaxi_realistic']
    else:  # FULL
        data_widths = [256, 512]
        sweep_profiles = ['constrained', 'slow_producer', 'high_throughput', 'gaxi_stress']

    test_types = ['smoke', 'single_channel', 'multi_channel', 'stress']
    params = []
    for tt in test_types:
        for dw in data_widths:
            params.append((tt, dw, 'default'))
    # Profile sweep on the E2E types at 512-bit (skip smoke - it's a bring-up check).
    for tt in ['single_channel', 'multi_channel', 'stress']:
        for prof in sweep_profiles:
            params.append((tt, 512, prof))
    return params


params = generate_params()


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

@pytest.mark.top_beats
@pytest.mark.rapids_core_beats
@pytest.mark.parametrize("test_type, data_width, timing_profile", params)
def test_rapids_core_beats(request, test_type, data_width, timing_profile):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_macro_beats': '../../rtl/macro_beats',
    })
    dut_name = "rapids_core_beats"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/macro_beats/rapids_core_beats.f'
    )

    dw_str = TBBase.format_dec(data_width, 4)
    test_name = f"test_rapids_core_beats_{test_type}_dw{dw_str}_{timing_profile}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': 8,
        'ADDR_WIDTH': 64,
        'DATA_WIDTH': data_width,
        'AXI_ID_WIDTH': 8,
        'SRAM_DEPTH': 512,
    }

    extra_env = {
        'TEST_TYPE': test_type,
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(12345),
        'TEST_NUM_CHANNELS': '8',
        'TEST_ADDR_WIDTH': '64',
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AXI_ID_WIDTH': '8',
        'TEST_SRAM_DEPTH': '512',
    }
    if timing_profile != 'default':
        extra_env['TIMING_PROFILE'] = timing_profile
        extra_env['GAXI_TIMING_PROFILE'] = timing_profile

    testcase = f"cocotb_test_{test_type}"
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE"]
    if enable_waves:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir, os.path.join(repo_root, 'projects/components/rapids/dv/tbclasses')],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            results_xml=results_path,
            extra_env=extra_env,
            compile_args=compile_args,
            waves=enable_waves,
            keep_files=True,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View: {cmd_filename}")
        raise


if __name__ == "__main__":
    class MockRequest:
        pass
    test_rapids_core_beats(MockRequest(), test_type="smoke", data_width=512, timing_profile="default")
