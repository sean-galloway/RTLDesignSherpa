# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil5_slave_rd_mon
# Purpose: AXIL5 Slave Read Monitor Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""

PORTED FROM the AXIL4 runner of the same name. The test LOGIC is not restated:
the TB class is the AXIL4 monitor TB with the factories swapped and the
AXI5-Lite optional groups enabled.

The monitor sees what it sees on AXI4-Lite -- handshakes, addresses, responses,
timing -- because axi_monitor_filtered has no ports for the optional groups.
So this runs the groups through the transport path with the monitor watching
underneath; it does not check the groups themselves.
AXIL5 Slave Read Monitor Integration Test

Thin wrapper that uses the reusable AXIL5SlaveMonitorTB testbench class.
All test logic is in bin/TBClasses/axil5/monitor/axil5_slave_monitor_tb.py
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.axil5.monitor.axil5_slave_monitor_tb import AXIL5SlaveMonitorTB
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axil5_slave_rd_mon_test(dut):
    """AXIL5 slave read monitor integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    # Create testbench (is_write=False for read slave)
    tb = AXIL5SlaveMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Run all integration tests
    await tb.run_integration_tests(test_level=test_level)


# ============================================================================
# PyTest Test Runner
# ============================================================================
def generate_axil5_monitor_params():
    """
    Generate AXIL5 monitor parameter combinations based on REG_LEVEL.

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test (basic)
        FUNC: 3 tests - Functional validation (basic, medium, full)
        FULL: 3 tests - Comprehensive testing (basic, medium, full)

    Returns:
        list: Test level values for pytest.mark.parametrize
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return ['gate']
    else:  # FUNC or FULL
        return ['gate', 'func', 'full']


@pytest.mark.parametrize("test_level", generate_axil5_monitor_params())
def test_axil5_slave_rd_mon(test_level):
    """
    Integration test runner.

    Controlled by REG_LEVEL environment variable:
        GATE: 1 test  - Quick smoke test
        FUNC: 3 tests - Functional validation (default)
        FULL: 3 tests - Comprehensive testing
    """

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil5': 'rtl/amba/axil5/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axil5_slave_rd_mon"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    # Transaction-table shaping, overridable from the environment. The READ
    # select is ID-matched, so banking should not disturb it -- but "should not"
    # is exactly the reasoning that left the WRITE path's banked double-count
    # unexercised until it was found by inspection. A parameter no test can
    # express is a parameter nobody is checking. Both go in the build directory
    # name: they change the elaborated design.
    num_banks = int(os.environ.get('NUM_BANKS', '1'))
    use_wq = int(os.environ.get('USE_WDATA_ORDER_Q', '0'))

    test_name = f"test_{worker_id}_{dut_name}_nb{num_banks}_wq{use_wq}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axil5_slave_rd_mon.f")

    # Check files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters (simplified for AXIL)
    rtl_parameters = {
        'AXIL_ADDR_WIDTH': '32',
        'AXIL_DATA_WIDTH': '32',
        'UNIT_ID': '2',
        'AGENT_ID': '20',
        'MAX_TRANSACTIONS': '8',  # Reduced for AXIL
        'NUM_BANKS': str(num_banks),
        'USE_WDATA_ORDER_Q': str(use_wq),
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AR': '2',
        'SKID_DEPTH_R': '4',
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'TEST_LEVEL': test_level,
        # Pin the cocotb seed. Unpinned, cocotb self-seeds from the clock and
        # the AXIL5 monitor TBs' fixed 20-cycle packet wait intermittently
        # races the MonbusSlave's randomized ready delay (which reaches 30
        # cycles) -- the same ~12% zero-packet race the AXI4 monitor TB
        # documents and fixed with a bounded poll. The real fix is porting
        # that poll to bin/TBClasses/axil5/monitor/* (framework repo); until
        # then the suite must at least be deterministic.
        'RANDOM_SEED': '12345',
        'COCOTB_RANDOM_SEED': '12345',
    }

    compile_args = ["--trace-fst",
        "--trace-structs",
        "-Wno-WIDTH",
            "-Wno-SELRANGE",
            "-Wno-CASEINCOMPLETE",
            "-Wno-BLKANDNBLK",
            "--timescale", "1ns/1ps",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend([])

    run(
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=module,
        simulator="verilator",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
        plus_args=(['--trace'] if enable_waves else []),
        timescale='1ns/1ps',
        verilator_trace=False,
        compile_args=compile_args,
        includes=includes
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
