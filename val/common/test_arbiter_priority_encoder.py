# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_priority_encoder
# Purpose: Test runner for arbiter_priority_encoder module
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test runner for arbiter_priority_encoder module

The arbiter_priority_encoder provides optimized priority encoding with specialized
implementations for common client counts (4, 8, 16, 32) and a generic loop version.

Test Configurations:
- clients=4: Optimized unrolled casez implementation
- clients=8: Optimized unrolled casez implementation
- clients=16: Optimized unrolled casez implementation
- clients=32: Optimized unrolled casez implementation
- clients=5: Generic loop-based implementation
- clients=12: Generic loop-based implementation

REG_LEVEL Control:
    GATE: 2 tests (~3 min) - smoke test (4 optimized, 5 generic)
    FUNC: 6 tests (~10 min) - functional coverage - DEFAULT
    FULL: 6 tests (~10 min) - same as FUNC (no depth parameter)

Author: RTL Design Sherpa Project
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.arbiter_priority_encoder_tb import ArbiterPriorityEncoderTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_arbiter_priority_encoder_test(dut):
    """Main arbiter_priority_encoder test function"""
    tb = ArbiterPriorityEncoderTB(dut)
    await tb.setup_clocks_and_reset()
    passed = await tb.run_all_tests()
    assert passed, "arbiter_priority_encoder test failed"

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (4 optimized, 5 generic)
    REG_LEVEL=FUNC: 6 tests (all configurations) - default
    REG_LEVEL=FULL: 6 tests (same as FUNC)

    Returns:
        List of tuples: (clients, test_mode)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # All available configurations
    all_configs = [
        # (CLIENTS, test_mode)
        (4, 'optimized'),    # Optimized unrolled casez
        (8, 'optimized'),    # Optimized unrolled casez
        (16, 'optimized'),   # Optimized unrolled casez
        (32, 'optimized'),   # Optimized unrolled casez
        (5, 'generic'),      # Generic loop-based
        (12, 'generic'),     # Generic loop-based
    ]

    if reg_level == 'GATE':
        # Quick smoke test: one optimized + one generic
        return [all_configs[0], all_configs[4]]  # 4 optimized, 5 generic

    else:  # FUNC or FULL (same for this test)
        # Full coverage: all configurations
        return all_configs

# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("clients, test_mode", generate_test_params())
def test_arbiter_priority_encoder(request, clients, test_mode):
    """
    Arbiter priority encoder test runner

    Tests priority encoding with masked/unmasked requests:
    - Priority order (client 0 = highest)
    - Masked vs unmasked selection
    - No-request handling
    - All client coverage
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common'
    })

    dut_name = "arbiter_priority_encoder"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/arbiter_priority_encoder.f'
    )

    # Format parameters for unique test name
    cl_str = TBBase.format_dec(clients, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_cl{cl_str}_{test_mode}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'CLIENTS': clients,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'PARAM_CLIENTS': str(clients),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_arbiter_priority_encoder_test",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD"],
            sim_args=[],
            plusargs=[],
        )
        print(f"✓ Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
