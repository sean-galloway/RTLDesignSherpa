"""
Test runner for apbtodescr (APB-to-Descriptor Router)

Tests:
- Basic address decode to all 8 channels
- Back-pressure handling (descriptor engine busy)
- Out-of-range address error
- Read request error
"""

import pytest
import os
import sys

# Setup Python path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import filelist utility
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Pytest wrapper for running with parameters
@pytest.mark.parametrize("params", [
    {"ADDR_WIDTH": 32, "DATA_WIDTH": 32, "NUM_CHANNELS": 8},
])
def test_apbtodescr(params):
    """Pytest wrapper for apbtodescr tests

    Args:
        params: Dictionary of test parameters
    """
    # Set environment variables for testbench
    for key, value in params.items():
        os.environ[key] = str(value)

    # Verilator options
    extra_env = {
        'SIM': 'verilator',
        'WAVES': '0',  # Set to 1 for waveform dump
    }
    os.environ.update(extra_env)

    # Module and toplevel
    tests_dir = os.path.dirname(os.path.abspath(__file__))

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/macro/apbtodescr.f'
    )

    # Compile and run
    from cocotb_test.simulator import run

    # Add test directory to Python path for cocotb to find cocotb_tests.py
    sys.path.insert(0, tests_dir)

    run(
        verilog_sources=verilog_sources,
        includes=includes,  # From filelist via get_sources_from_filelist()
        toplevel="apbtodescr",
        module="cocotb_tests",  # Load cocotb tests from cocotb_tests.py
        simulator="verilator",
        pythonpath=[tests_dir],  # Tell cocotb where to find the test module
        work_dir=os.path.join(tests_dir, "local_sim_build",
                             f"test_apbtodescr_"
                             f"aw{params['ADDR_WIDTH']:03d}_"
                             f"dw{params['DATA_WIDTH']:03d}_"
                             f"nc{params['NUM_CHANNELS']:02d}"),
        parameters=params,
        extra_env=extra_env,
        waves=int(os.environ.get('WAVES', '0')) == 1,
    )


if __name__ == "__main__":
    # Run with pytest
    pytest.main([__file__, "-v", "-s"])
