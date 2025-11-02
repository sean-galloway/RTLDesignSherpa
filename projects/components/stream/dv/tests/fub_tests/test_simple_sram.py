"""
Simple SRAM Test Runner

Test runner for the simple_sram.sv module using the CocoTB framework.
Tests basic dual-port SRAM with 1-cycle read latency.

Test Levels:
- Basic: Simple write/read verification
- Dual-port: Simultaneous read/write operations

Author: RTL Design Sherpa
Created: 2025-10-19
"""

import os
import pytest
import cocotb
from cocotb_test.simulator import run

# Setup Python path BEFORE any other imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
stream_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))  # dv/ directory
import sys

# Remove if already in path
if stream_dv_path in sys.path:
    sys.path.remove(stream_dv_path)
if repo_root in sys.path:
    sys.path.remove(repo_root)

# Add to path (stream_dv_path FIRST so tbclasses is found)
sys.path.insert(0, stream_dv_path)
sys.path.insert(0, repo_root)

# Import REUSABLE testbench class from PROJECT AREA
from tbclasses.simple_sram_tb import SimpleSRAMTB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic(dut):
    """Test basic SRAM write/read operations"""
    tb = SimpleSRAMTB(dut)
    await tb.setup_clocks_and_reset()

    # Run basic test
    success = await tb.run_basic_test(num_locations=16)

    # Get report
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")

    assert success, "Basic SRAM test failed"

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_dual_port(dut):
    """Test simultaneous read/write (dual-port)"""
    tb = SimpleSRAMTB(dut)
    await tb.setup_clocks_and_reset()

    # Run dual-port test
    success = await tb.run_dual_port_test()

    assert success, "Dual-port test failed"

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_simple_sram_params():
    """
    Generate test parameters for simple SRAM tests

    Returns:
        List of tuples: (addr_width, data_width, num_chunks)
    """
    return [
        # (addr_width, data_width, num_chunks)
        (8, 32, 1),    # 256x32, no chunk enables
        (10, 64, 1),   # 1024x64, no chunk enables
        (12, 512, 1),  # 4096x512 (typical for STREAM), no chunk enables
    ]

simple_sram_params = generate_simple_sram_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("addr_width, data_width, num_chunks", simple_sram_params)
def test_basic(request, addr_width, data_width, num_chunks):
    """Simple SRAM basic test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "simple_sram"

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/simple_sram.f'
    )

    # Format parameters for unique test name
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 4)
    nc_str = TBBase.format_dec(num_chunks, 1)

    test_name_plus_params = f"test_{dut_name}_aw{aw_str}_dw{dw_str}_nc{nc_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    depth = 1 << addr_width
    rtl_parameters = {
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'DEPTH': depth,
        'NUM_CHUNKS': num_chunks,
    }

    extra_env = {
        'LOG_PATH': log_path,
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_basic",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
                "-Wno-TIMESCALEMOD",
            ],
            sim_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
            ],
            plusargs=[
                "--trace",
            ]
        )
        print(f"✓ Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"✗ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise

@pytest.mark.parametrize("addr_width, data_width, num_chunks", simple_sram_params)
def test_dual_port(request, addr_width, data_width, num_chunks):
    """Simple SRAM dual-port test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "simple_sram"

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/simple_sram.f'
    )

    # Format parameters for unique test name
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 4)
    nc_str = TBBase.format_dec(num_chunks, 1)

    test_name_plus_params = f"test_{dut_name}_dual_aw{aw_str}_dw{dw_str}_nc{nc_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    depth = 1 << addr_width
    rtl_parameters = {
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'DEPTH': depth,
        'NUM_CHUNKS': num_chunks,
    }

    extra_env = {
        'LOG_PATH': log_path,
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_dual_port",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
                "-Wno-TIMESCALEMOD",
            ],
            sim_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
            ],
            plusargs=[
                "--trace",
            ]
        )
        print(f"✓ Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"✗ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
