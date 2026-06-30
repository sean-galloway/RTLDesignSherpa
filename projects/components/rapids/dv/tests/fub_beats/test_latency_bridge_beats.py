# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_beats_latency_bridge
# Purpose: RAPIDS Beats Latency Bridge FUB Validation Test - Phase 1
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-01-10
"""
Test runner for beats_latency_bridge module.

The runner is a thin dispatcher: it parametrizes (test_type, data_width,
timing_profile) and hands those to the testbench via env vars. ALL stimulus and
checking lives in LatencyBridgeBeatsTB (occupancy / streaming / backpressure),
which drives the s/m interfaces through GAXI BFMs.

Test Types:
- 'occupancy':    fill the skid buffer with the drain blocked, verify occupancy
                  reaches SKID_DEPTH and backpressure asserts, then drain.
- 'streaming':    continuous flow under the active GAXI timing profile.
- 'backpressure': verify s_ready de-/re-asserts around a full skid buffer.
"""

import os
import random
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import TB class from PROJECT AREA (not framework!)
from projects.components.rapids.dv.tbclasses.latency_bridge_beats_tb import LatencyBridgeBeatsTB


#===============================================================================
# COCOTB TEST FUNCTION - thin dispatcher; all test logic lives in the TB
#===============================================================================

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_beats_latency_bridge(dut):
    """Dispatch to the TB method named by TEST_TYPE. Timing comes from
    GAXI_TIMING_PROFILE (applied when the BFMs are created in setup)."""
    test_type = os.environ.get('TEST_TYPE', 'occupancy')
    tb = LatencyBridgeBeatsTB(dut)
    await tb.setup_clocks_and_reset()

    dispatch = {
        'occupancy': tb.test_occupancy,
        'streaming': tb.test_streaming,
        'backpressure': tb.test_backpressure,
    }
    if test_type not in dispatch:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await dispatch[test_type]()


#===============================================================================
# PARAMETER GENERATION
#===============================================================================

def generate_params():
    """
    Generate (test_type, data_width, timing_profile) tuples based on REG_LEVEL.

    GATE: 1 data width, default profile only
    FUNC: 2 data widths, default profile + a small profile sweep on 256-bit
    FULL: 3 data widths, default profile + a wider profile sweep on 256-bit
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_types = ['occupancy', 'streaming', 'backpressure']

    if reg_level == 'GATE':
        data_widths = [256]
        sweep_profiles = []
    elif reg_level == 'FUNC':
        data_widths = [256, 512]
        sweep_profiles = ['slow_producer', 'gaxi_backpressure', 'gaxi_realistic']
    else:  # FULL
        data_widths = [128, 256, 512]
        sweep_profiles = ['constrained', 'slow_producer', 'high_throughput',
                          'gaxi_backpressure', 'gaxi_stress', 'gaxi_realistic']

    params = []
    # Baseline: every test type x every data width at the default (back-to-back) profile.
    for test_type in test_types:
        for data_width in data_widths:
            params.append((test_type, data_width, 'default'))
    # Profile sweep: 256-bit only, to keep the matrix bounded.
    for test_type in test_types:
        for profile in sweep_profiles:
            params.append((test_type, 256, profile))

    return params


params = generate_params()


#===============================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
#===============================================================================

@pytest.mark.fub
@pytest.mark.beats_latency_bridge
@pytest.mark.parametrize("test_type, data_width, timing_profile", params)
def test_beats_latency_bridge(request, test_type, data_width, timing_profile):
    """Pytest wrapper for beats latency bridge tests - handles all test types."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub_beats': '../../rtl/fub_beats',
    })

    dut_name = "latency_bridge_beats"

    # Format parameters for unique test name (xdist compatibility)
    dw_str = f"{data_width:04d}"
    test_name = f"test_latency_bridge_{test_type}_dw{dw_str}_{timing_profile}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub_beats/latency_bridge_beats.f'
    )

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    parameters = {'DATA_WIDTH': str(data_width)}

    extra_env = {
        'TEST_TYPE': test_type,  # Pass test type to cocotb
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
    }
    if timing_profile != 'default':
        extra_env['GAXI_TIMING_PROFILE'] = timing_profile

    compile_args = ['-Wno-TIMESCALEMOD', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC']

    if coverage_enabled:
        compile_args.extend([
            "--coverage-line",
            "--coverage-toggle",
            "--coverage-underscore",
        ])

    # Enable VCD waveforms if WAVES=1 (not FST, which has Verilator bugs)
    waves_requested = bool(int(os.environ.get('WAVES', '0')))
    if waves_requested:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])
        waves_value = os.environ.pop('WAVES', None)

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir, os.path.join(repo_root, 'projects/components/rapids/dv/tbclasses')],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_beats_latency_bridge",  # Single cocotb test
            parameters=parameters,
            sim_build=sim_build,
            results_xml=results_path,
            simulator='verilator',
            compile_args=compile_args,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"Test completed! Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"  View command: {cmd_filename}")
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise

    # Restore WAVES if it was set
    if waves_requested and 'waves_value' in dir() and waves_value is not None:
        os.environ['WAVES'] = waves_value


if __name__ == "__main__":
    print("Running basic beats_latency_bridge test...")

    class MockRequest:
        pass

    request = MockRequest()
    test_beats_latency_bridge(request, test_type="occupancy", data_width=256, timing_profile="default")
