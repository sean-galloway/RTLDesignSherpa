"""
AXI Write Engine Test Runner

Test runner for the axi_write_engine.sv module using the CocoTB framework.
Tests streaming AXI4 write pipeline with SRAM sourcing.

The write engine is a high-performance streaming design with NO FSM - uses
continuous pipeline for maximum performance.

Test Levels:
- Basic: Single burst, no backpressure
- Medium: Multiple bursts, some backpressure
- Full: Comprehensive scenarios with error injection

Based on the RAPIDS/AMBA test runner pattern.

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

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from tbclasses.axi_write_engine_tb import AXIWriteEngineTB, TestScenario

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_basic_single_burst(dut):
    """Test basic single burst write operation"""
    tb = AXIWriteEngineTB(dut)
    await tb.setup_clocks_and_reset()

    # Run basic test
    success = await tb.run_basic_single_burst(addr=0x2000, burst_len=16)

    # Get report
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")

    assert success, "Basic single burst test failed"

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_axi_write_engine_params():
    """
    Generate test parameters for AXI write engine tests

    Returns:
        List of tuples: (addr_width, data_width, id_width, max_burst_len, sram_depth)
    """
    return [
        # (addr_width, data_width, id_width, max_burst_len, sram_depth)
        (64, 512, 8, 16, 4096),  # Standard configuration
    ]

axi_write_engine_params = generate_axi_write_engine_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("addr_width, data_width, id_width, max_burst_len, sram_depth", axi_write_engine_params)
def test_basic_single_burst(request, addr_width, data_width, id_width, max_burst_len, sram_depth):
    """AXI write engine basic single burst test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_stream_includes': '../../../../rtl/includes'
    })

    dut_name = "axi_write_engine"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/axi_write_engine.f'
    )

    # Format parameters for unique test name
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 4)
    iw_str = TBBase.format_dec(id_width, 2)
    mbl_str = TBBase.format_dec(max_burst_len, 2)
    sd_str = TBBase.format_dec(sram_depth, 4)

    test_name_plus_params = f"test_{dut_name}_aw{aw_str}_dw{dw_str}_iw{iw_str}_mbl{mbl_str}_sd{sd_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'ID_WIDTH': id_width,
        'MAX_BURST_LEN': max_burst_len,
        'SRAM_DEPTH': sram_depth,
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
            testcase="cocotb_test_basic_single_burst",
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
