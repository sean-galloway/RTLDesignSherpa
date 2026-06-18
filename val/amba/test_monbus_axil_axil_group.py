# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_axil_axil_group
# Purpose: MonBus AXIL/AXIL Group integration test (AXIL slave-read +
#          AXIL master-write member of the monbus_<p1>_<p2>_group family).
#
# Documentation: rtl/amba/PRD.md
# Subsystem: amba (shared)
#
# Author: sean galloway
# Created: 2025-10-19 (originally test_monbus_axil_group.py); renamed
#          + retargeted 2026-06-10 for the family refactor.

"""
MonBus AXIL/AXIL Group Integration Test

Test suite for `rtl/amba/shared/monbus_axil_axil_group.sv` -- the
AXIL/AXIL member of the monbus_<p1>_<p2>_group family. Drives the
single-input monitor bus, drains the error FIFO via the AXIL slave-read
interface, and lets the master-write side flush into a synthetic sink
inside the TB (no master-write assertions in this minimal test; see the
dedicated AXIL/AXI4 burst test for master-write coverage).

Test Types:
- 'basic_flow': Basic packet flow tests
- 'error_fifo': Error FIFO functionality tests

The reusable TB class lives at
  bin/TBClasses/amba/monbus_axil_axil_group/monbus_axil_axil_group_tb.py

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import the shared TB from bin/TBClasses (colocated with the shared
# rtl/amba/shared/monbus_axil_axil_group.sv module the test targets).
from TBClasses.amba.monbus_axil_axil_group.monbus_axil_axil_group_tb import MonbusAxilAxilGroupTB

# Coverage integration - optional import. Lives in the STREAM project
# area because that's where its instrumentation/scoreboards are tuned;
# val/amba tests degrade gracefully when it's not importable.
try:
    from projects.components.stream.dv.stream_coverage import (
        CoverageHelper,
        get_coverage_compile_args,
        get_coverage_env
    )
    COVERAGE_AVAILABLE = True
except ImportError:
    COVERAGE_AVAILABLE = False

    def get_coverage_compile_args():
        """Stub when coverage not available."""
        return []

    def get_coverage_env(test_name, sim_build=None):
        """Stub when coverage not available."""
        return {}


# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_monbus_axil_axil_group(dut):
    """Unified MonBus AXIL/AXIL Group test -- handles all test types via TEST_TYPE env var.

    Test Types:
    - 'basic_flow': Test basic packet flow through monitor bus
    - 'error_fifo': Test error/interrupt FIFO via AXIL slave-read interface
    """
    test_type = os.environ.get('TEST_TYPE', 'basic_flow')
    tb = MonbusAxilAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.setup_interfaces()

    # Branch on test type
    if test_type == 'basic_flow':
        success, stats = await tb.test_basic_packet_flow(count=16)
        assert success, f"Basic packet flow test failed: {stats}"
        tb.log.info(f"✅ Basic flow: {stats['success_rate']:.1%} success rate")
    elif test_type == 'error_fifo':
        success, stats = await tb.test_error_fifo_functionality(count=8)
        assert success, f"Error FIFO test failed: {stats}"
        tb.log.info(f"✅ Error FIFO: {stats['packets_read']} packets read")
    elif test_type == 'error_decode':
        success, stats = await tb.test_error_fifo_decode(count=8)
        assert success, f"Error FIFO decode test failed: {stats}"
        tb.log.info(f"✅ Error decode: {stats['records']} records via "
                    f"{stats['drain_width']}-bit drain")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    # Flush monbus sniffer capture if enabled (no-op when MONBUS_CAPTURE unset).
    tb.finalize_monbus_capture()


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_monbus_axil_axil_test_params():
    """Generate test parameters for monbus_axil_axil_group tests.

    Notes on the new family:
    - Data width is locked at 64 bits in the family (no more
      S_AXIL_DATA_WIDTH / M_AXIL_DATA_WIDTH parameters).
    - FIFO_DEPTH_WRITE is in BEATS, not records (one queue entry =
      one 64-bit beat; the raw-mode expander pushes 3 beats/record).
    - NUM_PROTOCOLS is informational (3 = AXI, AXIS, CORE).

    Parameters:
        (test_type, fifo_depth_err, fifo_depth_write, addr_width,
         num_protocols, s_axil_data_width)

    The err-FIFO drain AXIL data width (S_AXIL_DATA_WIDTH) is swept: 64 (one
    beat per record slice) and 32 (the 2:1 read serializer, low/high halves,
    6 beats/record). The 'error_decode' type runs at both widths to prove the
    serializer preserves full packet content; the lighter flow/count types run
    at the default 64-bit width.
    """
    base = (64, 96, 32, 3)   # (fifo_depth_err, fifo_depth_write[beats], addr_width, num_protocols)

    params = []
    for test_type in ('basic_flow', 'error_fifo'):
        params.append((test_type,) + base + (64,))
    # Rigorous decode coverage at BOTH drain widths (32-bit is the config that
    # was never tested before -- stream_top_ch8 uses it).
    for sdw in (64, 32):
        params.append(('error_decode',) + base + (sdw,))

    return params


monbus_axil_axil_params = generate_monbus_axil_axil_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize("test_type, fifo_depth_err, fifo_depth_write, addr_width, num_protocols, s_axil_data_width",
                         monbus_axil_axil_params)
def test_monbus_axil_axil_group(request, test_type, fifo_depth_err, fifo_depth_write, addr_width, num_protocols, s_axil_data_width):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for MonBus AXIL/AXIL Group tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_shared':   'rtl/amba/shared',
        'rtl_axil4':    'rtl/amba/axil4',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "monbus_axil_axil_group"

    # Dependency tree for the AXIL/AXIL member of the
    # monbus_<p1>_<p2>_group family. Includes the optional compressor
    # so USE_COMPRESSION=1 builds also compile (raw-mode tests just
    # don't instantiate it).
    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'],   "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axil4'],    "axil4_slave_rd.sv"),
        os.path.join(rtl_dict['rtl_axil4'],    "axil4_master_wr.sv"),
        # Monbus group core family (cam/compressor/core + div-by-3 helper)
        # from the shared canonical filelist -- one place for new deps.
        *get_sources_from_filelist(repo_root, 'rtl/amba/filelists/monbus_group.f')[0],
        os.path.join(rtl_dict['rtl_shared'],   f"{dut_name}.sv"),
    ]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # Format parameters for unique test name
    fde_str = TBBase.format_dec(fifo_depth_err, 3)
    fdw_str = TBBase.format_dec(fifo_depth_write, 3)
    aw_str = TBBase.format_dec(addr_width, 2)
    np_str = TBBase.format_dec(num_protocols, 1)
    sdw_str = TBBase.format_dec(s_axil_data_width, 2)
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name_plus_params = f"test_{worker_id}_{dut_name}_{test_type}_fde{fde_str}_fdw{fdw_str}_aw{aw_str}_np{np_str}_sdw{sdw_str}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    includes = [rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build]

    # Family port surface: no more S_AXIL_DATA_WIDTH / M_AXIL_DATA_WIDTH
    # (data width is locked at 64). FIFO_DEPTH_WRITE is in beats.
    rtl_parameters = {
        'FIFO_DEPTH_ERR':    fifo_depth_err,
        'FIFO_DEPTH_WRITE':  fifo_depth_write,
        'ADDR_WIDTH':        addr_width,
        'NUM_PROTOCOLS':     num_protocols,
        'S_AXIL_DATA_WIDTH': s_axil_data_width,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TEST_TYPE': test_type,
        'TEST_FIFO_DEPTH_ERR':    str(fifo_depth_err),
        'TEST_FIFO_DEPTH_WRITE':  str(fifo_depth_write),
        'TEST_ADDR_WIDTH':        str(addr_width),
        'TEST_NUM_PROTOCOLS':     str(num_protocols),
        'TEST_S_AXIL_DATA_WIDTH': str(s_axil_data_width),
    }

    # Add coverage environment variables if coverage is enabled
    coverage_env = get_coverage_env(test_name_plus_params, sim_build=sim_build)
    extra_env.update(coverage_env)

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, 'test_monbus_axil_axil_group', test_name_plus_params)

    # Build args conditionally based on waves
    waves_enabled = False
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-SELRANGE", "-Wno-WIDTHEXPAND", "-Wno-WIDTH"]
    sim_args = []
    if waves_enabled:
        compile_args.extend(["--trace", "--trace-structs", "--trace-depth", "99"])
        sim_args.extend(["--trace", "--trace-structs", "--trace-depth", "99"])

    # Add coverage compile args if COVERAGE=1
    coverage_compile_args = get_coverage_compile_args()
    compile_args.extend(coverage_compile_args)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module='test_monbus_axil_axil_group',
            testcase="cocotb_test_monbus_axil_axil_group",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"✓ MonBus AXIL/AXIL {test_type} test PASSED! Logs: {log_path}")
    except Exception as e:
        print(f"✗ MonBus AXIL/AXIL {test_type} test FAILED: {str(e)}")
        print(f"Logs: {log_path}")
        raise
