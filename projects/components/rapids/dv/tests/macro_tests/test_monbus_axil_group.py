# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_axil_group
# Purpose: RAPIDS MonBus AXIL Group Integration Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS MonBus AXIL Group Integration Test

Comprehensive test suite for the monbus_axil_group module which aggregates
monitor bus streams from source and sink paths and provides:
- AXI-Lite slave read interface (error/interrupt FIFO)
- AXI-Lite master write interface (master write FIFO)
- Protocol-specific packet filtering (AXI, Network, CORE)
- Monitor bus arbitration

Test Organization:
- Basic packet flow tests (source/sink injection)
- Protocol filtering tests (AXI, Network, CORE)
- Error FIFO functionality tests (AXI-Lite slave read)
- Master write functionality tests (AXI-Lite master write)
- Concurrent stream tests
- Stress tests

This test file imports the reusable MonbusAxilGroupTB class from:
  bin/CocoTBFramework/tbclasses/rapids/monbus_axil_group_tb.py

STRUCTURE FOLLOWS RAPIDS FUB PATTERN:
  - CocoTB test functions at top (prefixed with cocotb_)
  - Parameter generation at bottom
  - Pytest wrappers at bottom with @pytest.mark.parametrize
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Add dv directory to path so we can import from tbclasses/
dv_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if dv_dir not in sys.path:
    sys.path.insert(0, dv_dir)

from tbclasses.monbus_axil_group_tb import MonbusAxilGroupTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_flow(dut):
    """Test basic packet flow through source and sink monitor bus."""
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    success, stats = await tb.test_basic_packet_flow(count=32)
    assert success, f"Basic packet flow test failed: {stats}"
    tb.log.info(f"✅ Basic flow: {stats['success_rate']:.1%} success rate")


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_error_fifo(dut):
    """Test error/interrupt FIFO via AXI-Lite slave read interface."""
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    success, stats = await tb.test_error_fifo_functionality(count=16)
    assert success, f"Error FIFO test failed: {stats}"
    tb.log.info(f"✅ Error FIFO: {stats['packets_read']}/{stats['packets_sent']} packets")


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_master_write(dut):
    """Test master write functionality via AXI-Lite master write interface."""
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    success, stats = await tb.test_master_write_functionality(count=8)
    assert success, f"Master write test failed: {stats}"
    tb.log.info(f"✅ Master write: {stats['completed_writes']}/{stats['expected_writes']} writes")


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_protocol_filtering(dut):
    """Test protocol-specific packet filtering (AXI, Network, CORE)."""
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    success, stats = await tb.test_protocol_filtering()
    assert success, f"Protocol filtering test failed: {stats}"
    tb.log.info(f"✅ Filtering: {len(stats)} protocols tested")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_concurrent_streams(dut):
    """Test concurrent packet streams from source and sink."""
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    success, stats = await tb.test_concurrent_packet_streams(duration_cycles=200)
    assert success, f"Concurrent streams test failed: {stats}"
    tb.log.info(f"✅ Concurrent: {stats['total_packets']} packets processed")


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_stress(dut):
    """Stress test with mixed operations."""
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    success, stats = await tb.stress_test(iterations=50)
    # Stress test allows some failures
    assert stats['success_rate'] > 0.7, f"Stress test failed: {stats['success_rate']:.1%} success rate too low"
    tb.log.info(f"✅ Stress: {stats['success_rate']:.1%} success rate")


# ===========================================================================
# PARAMETER GENERATION - at bottom of file
# ===========================================================================

def generate_monbus_axil_test_params():
    """Generate test parameters for monbus_axil_group tests.

    Note: DATA_WIDTH is fixed at 32 bits for FPGA implementation.
    64-bit support requires RTL fixes for proper width handling.
    """
    return [
        # (fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)
        (64, 32, 32, 32, 3),   # Standard configuration
        (128, 64, 32, 32, 3),  # Larger FIFOs, 32-bit data width
    ]

monbus_axil_params = generate_monbus_axil_test_params()


# ===========================================================================
# HELPER FUNCTION - Common test setup
# ===========================================================================

def run_monbus_axil_test(testcase_name, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """Helper function to run monbus_axil_group tests with common setup."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_macro': '../../rtl/rapids_macro',
    })

    dut_name = "monbus_axil_group"

    # Get Verilog sources and includes from hierarchical file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/macro/monbus_axil_group.f'
    )

    # Format parameters for unique test name
    fdepth_err_str = TBBase.format_dec(fifo_depth_err, 3)
    fdepth_wr_str = TBBase.format_dec(fifo_depth_write, 3)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    np_str = TBBase.format_dec(num_protocols, 1)
    test_name_plus_params = f"test_{dut_name}_{testcase_name}_fde{fdepth_err_str}_fdw{fdepth_wr_str}_aw{aw_str}_dw{dw_str}_np{np_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FIFO_DEPTH_ERR': fifo_depth_err,
        'FIFO_DEPTH_WRITE': fifo_depth_write,
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'NUM_PROTOCOLS': num_protocols,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TEST_FIFO_DEPTH_ERR': str(fifo_depth_err),
        'TEST_FIFO_DEPTH_WRITE': str(fifo_depth_write),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_NUM_PROTOCOLS': str(num_protocols),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, 'test_monbus_axil_group', test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module='test_monbus_axil_group',
            testcase=f"cocotb_{testcase_name}",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD"],
            sim_args=[],
            plusargs=[],
        )
        print(f"✓ {testcase_name} completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ {testcase_name} failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - at bottom of file
# ===========================================================================

@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_basic_flow(request, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """MonBus AXIL Group basic flow test."""
    run_monbus_axil_test("test_basic_flow", fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)


@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_error_fifo(request, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """MonBus AXIL Group error FIFO test."""
    run_monbus_axil_test("test_error_fifo", fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)


@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_master_write(request, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """MonBus AXIL Group master write test."""
    run_monbus_axil_test("test_master_write", fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)


@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_protocol_filtering(request, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """MonBus AXIL Group protocol filtering test."""
    run_monbus_axil_test("test_protocol_filtering", fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)


@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_concurrent_streams(request, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """MonBus AXIL Group concurrent streams test."""
    run_monbus_axil_test("test_concurrent_streams", fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)


@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_stress(request, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """MonBus AXIL Group stress test."""
    run_monbus_axil_test("test_stress", fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)
