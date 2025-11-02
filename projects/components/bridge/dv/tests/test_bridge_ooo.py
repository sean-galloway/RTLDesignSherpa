# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Test: Out-of-Order Bridge with CAM/FIFO Tracking
# Purpose: Validate OOO bridge transaction tracking and response routing
#
# Documentation: projects/components/bridge/docs/OOO_IMPLEMENTATION_STATUS.md
# Subsystem: bridge
#
# Author: sean galloway
# Created: 2025-10-27

"""
Test Suite for Out-of-Order (OOO) Bridge

Tests:
- Basic routing from masters to slaves
- In-order response handling (FIFO verification)
- Out-of-order response handling (CAM verification)
- CAM/FIFO internal signal monitoring
- Multi-master access to OOO slaves
"""

import os
import pytest
import cocotb
from cocotb_test.simulator import run

# Import testbench class from project area
import sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

# Add project root to path for importing TB class from PROJECT AREA
sys.path.insert(0, repo_root)

from projects.components.bridge.dv.tbclasses.bridge_ooo_tb import BridgeOOOTB
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


# ===========================================================================
# COCOTB TEST FUNCTIONS - Prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit='us')
async def cocotb_test_basic_routing(dut):
    """Test basic address routing from masters to slaves"""
    tb = BridgeOOOTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_basic_routing(num_transactions=10)
    assert result, "Basic routing test failed"


@cocotb.test(timeout_time=200, timeout_unit='us')
async def cocotb_test_in_order_responses(dut):
    """Test in-order response handling (FIFO verification)"""
    tb = BridgeOOOTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_in_order_responses(num_transactions=10)
    assert result, "In-order response test failed"


@cocotb.test(timeout_time=300, timeout_unit='us')
async def cocotb_test_out_of_order_responses(dut):
    """Test out-of-order response handling (CAM verification)"""
    tb = BridgeOOOTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_out_of_order_responses(num_transactions=10)
    assert result, "Out-of-order response test failed"


@cocotb.test(timeout_time=200, timeout_unit='us')
async def cocotb_test_cam_fifo_monitoring(dut):
    """Test CAM and FIFO internal signal monitoring"""
    tb = BridgeOOOTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_cam_fifo_monitoring()
    assert result, "CAM/FIFO monitoring test failed"


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - At bottom of file
# ===========================================================================

@pytest.mark.bridge
@pytest.mark.ooo
@pytest.mark.routing
def test_basic_routing(request):
    """Pytest wrapper for basic routing test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': 'projects/components/bridge/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    # Verilog sources - use repo_root for absolute paths
    verilog_sources = [
        # Bridge OOO module
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_ooo_with_arbiter.sv'),

        # Bridge CAM module
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_cam.sv'),

        # Internal crossbar
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_axi4_flat_5x3.sv'),

        # FIFO for in-order tracking
        os.path.join(repo_root, 'rtl/amba/gaxi/gaxi_fifo_sync.sv'),

        # Common modules
        os.path.join(repo_root, 'rtl/common/arbiter_round_robin.sv'),
        os.path.join(repo_root, 'rtl/common/arbiter_priority_encoder.sv'),
        os.path.join(repo_root, 'rtl/common/fifo_sync.sv'),
        os.path.join(repo_root, 'rtl/common/fifo_control.sv'),
        os.path.join(repo_root, 'rtl/common/cam_tag.sv'),
        os.path.join(repo_root, 'rtl/common/counter_bin.sv'),

        # AXI4 channel modules (for crossbar)
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_slave_wr.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_slave_rd.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_master_wr.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_master_rd.sv'),

        # Width converters
        os.path.join(repo_root, 'projects/components/converters/rtl/axi4_dwidth_converter_wr.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi4_dwidth_converter_rd.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi_data_upsize.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi_data_dnsize.sv'),

        # GAXI components
        os.path.join(repo_root, 'rtl/amba/gaxi/gaxi_skid_buffer.sv'),
    ]

    # Parameters
    rtl_parameters = {
        'NUM_MASTERS': 5,
        'NUM_SLAVES': 3,
        'XBAR_DATA_WIDTH': 512,
        'XBAR_ADDR_WIDTH': 64,
        'XBAR_ID_WIDTH': 8,
        'XBAR_STRB_WIDTH': 64,
    }

    # Simulation build directory
    sim_build = os.path.join(tests_dir, 'local_sim_build', 'bridge_ooo_basic_routing')

    # Include directories
    includes = [
        os.path.join(repo_root, 'rtl/amba/includes'),
    ]

    # Verilator compile args to tolerate width warnings (expected for converters)
    compile_args = [
        '-Wno-WIDTHEXPAND',  # Allow width expansion in converters
        '-Wno-WIDTHTRUNC',   # Allow width truncation (CPU master 4b ID -> 8b crossbar)
    ]

    # Run simulation
    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel='bridge_ooo_with_arbiter',
        module=module,
        testcase='cocotb_test_basic_routing',
        parameters=rtl_parameters,
        sim_build=sim_build,
        work_dir=log_dir,
        waves=False,  # Disabled due to Verilator FST tracing bug
        compile_args=compile_args,
    )


@pytest.mark.bridge
@pytest.mark.ooo
@pytest.mark.fifo
def test_in_order_responses(request):
    """Pytest wrapper for in-order response test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': 'projects/components/bridge/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    verilog_sources = [
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_ooo_with_arbiter.sv'),
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_cam.sv'),
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_axi4_flat_5x3.sv'),
        os.path.join(repo_root, 'rtl/amba/gaxi/gaxi_fifo_sync.sv'),
        os.path.join(repo_root, 'rtl/common/arbiter_round_robin.sv'),
        os.path.join(repo_root, 'rtl/common/arbiter_priority_encoder.sv'),
        os.path.join(repo_root, 'rtl/common/fifo_sync.sv'),
        os.path.join(repo_root, 'rtl/common/fifo_control.sv'),
        os.path.join(repo_root, 'rtl/common/cam_tag.sv'),
        os.path.join(repo_root, 'rtl/common/counter_bin.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_slave_wr.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_slave_rd.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_master_wr.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_master_rd.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi4_dwidth_converter_wr.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi4_dwidth_converter_rd.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi_data_upsize.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi_data_dnsize.sv'),
        os.path.join(repo_root, 'rtl/amba/gaxi/gaxi_skid_buffer.sv'),
    ]

    rtl_parameters = {
        'NUM_MASTERS': 5,
        'NUM_SLAVES': 3,
        'XBAR_DATA_WIDTH': 512,
        'XBAR_ADDR_WIDTH': 64,
        'XBAR_ID_WIDTH': 8,
        'XBAR_STRB_WIDTH': 64,
    }

    sim_build = os.path.join(tests_dir, 'local_sim_build', 'bridge_ooo_in_order')

    includes = [os.path.join(repo_root, 'rtl/amba/includes')]

    compile_args = ['-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC']

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel='bridge_ooo_with_arbiter',
        module=module,
        testcase='cocotb_test_in_order_responses',
        parameters=rtl_parameters,
        sim_build=sim_build,
        work_dir=log_dir,
        waves=False,  # Disabled due to Verilator FST tracing bug
        compile_args=compile_args,
    )


@pytest.mark.bridge
@pytest.mark.ooo
@pytest.mark.cam
def test_out_of_order_responses(request):
    """Pytest wrapper for out-of-order response test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': 'projects/components/bridge/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    verilog_sources = [
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_ooo_with_arbiter.sv'),
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_cam.sv'),
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_axi4_flat_5x3.sv'),
        os.path.join(repo_root, 'rtl/amba/gaxi/gaxi_fifo_sync.sv'),
        os.path.join(repo_root, 'rtl/common/arbiter_round_robin.sv'),
        os.path.join(repo_root, 'rtl/common/arbiter_priority_encoder.sv'),
        os.path.join(repo_root, 'rtl/common/fifo_sync.sv'),
        os.path.join(repo_root, 'rtl/common/fifo_control.sv'),
        os.path.join(repo_root, 'rtl/common/cam_tag.sv'),
        os.path.join(repo_root, 'rtl/common/counter_bin.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_slave_wr.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_slave_rd.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_master_wr.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_master_rd.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi4_dwidth_converter_wr.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi4_dwidth_converter_rd.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi_data_upsize.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi_data_dnsize.sv'),
        os.path.join(repo_root, 'rtl/amba/gaxi/gaxi_skid_buffer.sv'),
    ]

    rtl_parameters = {
        'NUM_MASTERS': 5,
        'NUM_SLAVES': 3,
        'XBAR_DATA_WIDTH': 512,
        'XBAR_ADDR_WIDTH': 64,
        'XBAR_ID_WIDTH': 8,
        'XBAR_STRB_WIDTH': 64,
    }

    sim_build = os.path.join(tests_dir, 'local_sim_build', 'bridge_ooo_out_of_order')

    includes = [os.path.join(repo_root, 'rtl/amba/includes')]

    compile_args = ['-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC']

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel='bridge_ooo_with_arbiter',
        module=module,
        testcase='cocotb_test_out_of_order_responses',
        parameters=rtl_parameters,
        sim_build=sim_build,
        work_dir=log_dir,
        waves=False,  # Disabled due to Verilator FST tracing bug
        compile_args=compile_args,
    )


@pytest.mark.bridge
@pytest.mark.ooo
@pytest.mark.monitoring
def test_cam_fifo_monitoring(request):
    """Pytest wrapper for CAM/FIFO monitoring test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': 'projects/components/bridge/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    verilog_sources = [
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_ooo_with_arbiter.sv'),
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_cam.sv'),
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_axi4_flat_5x3.sv'),
        os.path.join(repo_root, 'rtl/amba/gaxi/gaxi_fifo_sync.sv'),
        os.path.join(repo_root, 'rtl/common/arbiter_round_robin.sv'),
        os.path.join(repo_root, 'rtl/common/arbiter_priority_encoder.sv'),
        os.path.join(repo_root, 'rtl/common/fifo_sync.sv'),
        os.path.join(repo_root, 'rtl/common/fifo_control.sv'),
        os.path.join(repo_root, 'rtl/common/cam_tag.sv'),
        os.path.join(repo_root, 'rtl/common/counter_bin.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_slave_wr.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_slave_rd.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_master_wr.sv'),
        os.path.join(repo_root, 'rtl/amba/axi4/axi4_master_rd.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi4_dwidth_converter_wr.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi4_dwidth_converter_rd.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi_data_upsize.sv'),
        os.path.join(repo_root, 'projects/components/converters/rtl/axi_data_dnsize.sv'),
        os.path.join(repo_root, 'rtl/amba/gaxi/gaxi_skid_buffer.sv'),
    ]

    rtl_parameters = {
        'NUM_MASTERS': 5,
        'NUM_SLAVES': 3,
        'XBAR_DATA_WIDTH': 512,
        'XBAR_ADDR_WIDTH': 64,
        'XBAR_ID_WIDTH': 8,
        'XBAR_STRB_WIDTH': 64,
    }

    sim_build = os.path.join(tests_dir, 'local_sim_build', 'bridge_ooo_monitoring')

    includes = [os.path.join(repo_root, 'rtl/amba/includes')]

    compile_args = ['-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC']

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel='bridge_ooo_with_arbiter',
        module=module,
        testcase='cocotb_test_cam_fifo_monitoring',
        parameters=rtl_parameters,
        sim_build=sim_build,
        work_dir=log_dir,
        waves=False,  # Disabled due to Verilator FST tracing bug
        compile_args=compile_args,
    )
