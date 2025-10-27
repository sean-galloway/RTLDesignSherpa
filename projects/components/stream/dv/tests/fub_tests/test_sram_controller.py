"""
SRAM Controller Test Runner

Test runner for the sram_controller.sv module using the CocoTB framework.
Tests multi-channel SRAM segmentation with pre-allocation and dual data paths.

Test Levels:
- Basic write: Pre-allocation and write path verification
- Basic read: Read path verification
- Multi-channel: Concurrent multi-channel operation

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
from tbclasses.sram_controller_tb import SRAMControllerTB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_basic_write(dut):
    """Test basic write path operation"""
    tb = SRAMControllerTB(dut)
    await tb.setup_clocks_and_reset()

    # Run basic write test
    success = await tb.run_basic_write_test(channel=0, num_beats=16)

    # Get report
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")

    assert success, "Basic write test failed"

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_basic_read(dut):
    """Test basic read path operation"""
    tb = SRAMControllerTB(dut)
    await tb.setup_clocks_and_reset()

    # Run basic read test (writes then reads)
    success = await tb.run_basic_read_test(channel=0, num_beats=16)

    # Get report
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")

    assert success, "Basic read test failed"

@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_multi_channel(dut):
    """Test multi-channel concurrent operation"""
    tb = SRAMControllerTB(dut)
    await tb.setup_clocks_and_reset()

    # Run multi-channel test
    success = await tb.run_multi_channel_test(num_channels_to_test=4, beats_per_channel=8)

    # Get report
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")

    assert success, "Multi-channel test failed"

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_sram_controller_params():
    """
    Generate test parameters for SRAM controller tests

    Returns:
        List of tuples: (num_channels, sram_depth, data_width, id_width)
    """
    return [
        # (num_channels, sram_depth, data_width, id_width)
        (8, 1024, 512, 8),     # Typical configuration
        (4, 512, 64, 4),       # Smaller configuration
        (8, 4096, 512, 8),     # Large SRAM
    ]

sram_controller_params = generate_sram_controller_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("num_channels, sram_depth, data_width, id_width", sram_controller_params)
def test_basic_write(request, num_channels, sram_depth, data_width, id_width):
    """SRAM controller basic write test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "sram_controller"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/sram_controller.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    sd_str = TBBase.format_dec(sram_depth, 4)
    dw_str = TBBase.format_dec(data_width, 4)
    iw_str = TBBase.format_dec(id_width, 2)

    test_name_plus_params = f"test_{dut_name}_write_nc{nc_str}_sd{sd_str}_dw{dw_str}_iw{iw_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    segment_size = sram_depth // num_channels
    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'SRAM_DEPTH': sram_depth,
        'DATA_WIDTH': data_width,
        'ID_WIDTH': id_width,
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
            testcase="cocotb_test_basic_write",
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

@pytest.mark.parametrize("num_channels, sram_depth, data_width, id_width", sram_controller_params)
def test_basic_read(request, num_channels, sram_depth, data_width, id_width):
    """SRAM controller basic read test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "sram_controller"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/sram_controller.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    sd_str = TBBase.format_dec(sram_depth, 4)
    dw_str = TBBase.format_dec(data_width, 4)
    iw_str = TBBase.format_dec(id_width, 2)

    test_name_plus_params = f"test_{dut_name}_read_nc{nc_str}_sd{sd_str}_dw{dw_str}_iw{iw_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'SRAM_DEPTH': sram_depth,
        'DATA_WIDTH': data_width,
        'ID_WIDTH': id_width,
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
            testcase="cocotb_test_basic_read",
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

@pytest.mark.parametrize("num_channels, sram_depth, data_width, id_width", sram_controller_params)
def test_multi_channel(request, num_channels, sram_depth, data_width, id_width):
    """SRAM controller multi-channel test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "sram_controller"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/sram_controller.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    sd_str = TBBase.format_dec(sram_depth, 4)
    dw_str = TBBase.format_dec(data_width, 4)
    iw_str = TBBase.format_dec(id_width, 2)

    test_name_plus_params = f"test_{dut_name}_multi_nc{nc_str}_sd{sd_str}_dw{dw_str}_iw{iw_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'SRAM_DEPTH': sram_depth,
        'DATA_WIDTH': data_width,
        'ID_WIDTH': id_width,
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
            testcase="cocotb_test_multi_channel",
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
