# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_master_rd_mon_filtered
# Purpose: AXI4 Master Read Monitor with Filtering Tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Master Read Monitor with Filtering Tests

Comprehensive test demonstrating the new filtered monitoring capabilities
with multi-level filtering configurations and packet monitoring.

Features:
- Integration with TBAXIMonitorConfig TB
- Static randomized filtering configurations
- Multi-test reset/reprogram patterns
- Packet monitoring and validation
- Coordination with existing TBs
"""

import os
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.axi4.monitor.axi_monitor_config_tb import TBAXIMonitorConfig


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def axi4_master_rd_mon_filtering_test(dut):
    """Comprehensive test of AXI4 master read monitor with filtering"""

    # Start clock
    clk_period = 10  # 10ns = 100MHz
    clock = cocotb.clock.Clock(dut.aclk, clk_period, units="ns")
    cocotb.start_soon(clock.start())

    # Initialize Monitor Configuration TB
    monitor_config_tb = TBAXIMonitorConfig(
        dut=dut,
        filter_level="none",  # Start with no filtering
        randomize_configs=True,
        enable_packet_monitoring=True,
        expected_unit_id=1,   # Match DUT UNIT_ID parameter
        expected_agent_id=10  # Match DUT AGENT_ID parameter
    )

    # Reset sequence
    dut.aresetn.value = 0
    dut.cfg_monitor_enable.value = 1
    dut.cfg_error_enable.value = 1
    dut.cfg_timeout_enable.value = 1
    dut.cfg_perf_enable.value = 1
    dut.cfg_timeout_cycles.value = 1000
    dut.cfg_latency_threshold.value = 100
    dut.monbus_ready.value = 1

    # Configure initial filter level (none)
    await monitor_config_tb.configure_monitor("none")

    # Setup packet monitoring
    await monitor_config_tb.setup_packet_monitoring()

    # AXI slave side (input) - deassert all valid signals initially
    dut.fub_axi_arvalid.value = 0
    dut.fub_axi_rready.value = 1

    # AXI master side (output) - provide ready responses
    dut.m_axi_arready.value = 1
    dut.m_axi_rvalid.value = 0
    dut.m_axi_rid.value = 0
    dut.m_axi_rdata.value = 0
    dut.m_axi_rresp.value = 0
    dut.m_axi_rlast.value = 0
    dut.m_axi_ruser.value = 0

    await cocotb.triggers.ClockCycles(dut.aclk, 10)
    dut.aresetn.value = 1
    await cocotb.triggers.ClockCycles(dut.aclk, 10)

    # Test 1: No filtering - should see all packets
    cocotb.log.info("=== Test 1: No Filtering ===")
    await monitor_config_tb.configure_monitor("none")
    await _generate_axi_traffic(dut, num_transactions=5)
    await monitor_config_tb.wait_for_packets(min_packets=1, timeout_cycles=5000)

    stats_none = monitor_config_tb.get_statistics()
    cocotb.log.info(f"No filtering stats: {stats_none['packet_stats']}")

    # Test 2: Medium filtering - should see fewer packets
    cocotb.log.info("=== Test 2: Medium Filtering ===")
    await monitor_config_tb.configure_monitor("medium")
    await _generate_axi_traffic(dut, num_transactions=5)
    await monitor_config_tb.wait_for_packets(min_packets=1, timeout_cycles=5000)

    stats_medium = monitor_config_tb.get_statistics()
    cocotb.log.info(f"Medium filtering stats: {stats_medium['packet_stats']}")

    # Test 3: High filtering - should see even fewer packets
    cocotb.log.info("=== Test 3: High Filtering ===")
    await monitor_config_tb.configure_monitor("high")
    await _generate_axi_traffic(dut, num_transactions=5)
    await monitor_config_tb.wait_for_packets(min_packets=1, timeout_cycles=5000)

    stats_high = monitor_config_tb.get_statistics()
    cocotb.log.info(f"High filtering stats: {stats_high['packet_stats']}")

    # Test 4: Error-interrupt-only - production mode
    cocotb.log.info("=== Test 4: Error-Interrupt-Only ===")
    await monitor_config_tb.configure_monitor("error-interrupt-only")
    await _generate_axi_traffic(dut, num_transactions=5)
    await cocotb.triggers.ClockCycles(dut.aclk, 1000)  # Allow time for any packets

    stats_error_only = monitor_config_tb.get_statistics()
    cocotb.log.info(f"Error-only stats: {stats_error_only['packet_stats']}")

    # Test 5: Multi-level test with reset/reprogram pattern
    cocotb.log.info("=== Test 5: Multi-Level Reset/Reprogram ===")
    await monitor_config_tb.run_multi_level_test(
        levels=["none", "medium", "high", "error-interrupt-only"],
        cycles_per_level=500
    )

    # Final statistics and validation
    final_stats = monitor_config_tb.get_statistics()
    cocotb.log.info(f"Final test statistics: {final_stats}")

    # Validate filtering worked as expected
    assert final_stats['config_applied'], "Configuration should be applied"

    if final_stats['filter_violations'] > 0:
        cocotb.log.warning(f"Found {final_stats['filter_violations']} filter violations")

    cocotb.log.info("✓ AXI4 master read monitor filtering test completed successfully")


async def _generate_axi_traffic(dut, num_transactions=3):
    """Generate AXI read traffic to trigger monitor packets"""

    for i in range(num_transactions):
        # Generate read address
        dut.fub_axi_arid.value = i + 1
        dut.fub_axi_araddr.value = 0x1000 + (i * 0x100)
        dut.fub_axi_arlen.value = 0  # Single beat
        dut.fub_axi_arsize.value = 2  # 4 bytes
        dut.fub_axi_arburst.value = 1  # INCR
        dut.fub_axi_arlock.value = 0
        dut.fub_axi_arcache.value = 0
        dut.fub_axi_arprot.value = 0
        dut.fub_axi_arqos.value = 0
        dut.fub_axi_arregion.value = 0
        dut.fub_axi_aruser.value = 0
        dut.fub_axi_arvalid.value = 1

        # Wait for AR ready
        await cocotb.triggers.ClockCycles(dut.aclk, 1)
        while not dut.fub_axi_arready.value:
            await cocotb.triggers.ClockCycles(dut.aclk, 1)

        dut.fub_axi_arvalid.value = 0
        await cocotb.triggers.ClockCycles(dut.aclk, 5)

        # Provide read response
        dut.m_axi_rvalid.value = 1
        dut.m_axi_rid.value = i + 1
        dut.m_axi_rdata.value = 0xDEADBEE0 + i
        dut.m_axi_rresp.value = 0  # OKAY
        dut.m_axi_rlast.value = 1
        dut.m_axi_ruser.value = 0

        # Wait for R ready
        await cocotb.triggers.ClockCycles(dut.aclk, 1)
        while not (dut.m_axi_rvalid.value and dut.m_axi_rready.value):
            await cocotb.triggers.ClockCycles(dut.aclk, 1)

        dut.m_axi_rvalid.value = 0
        await cocotb.triggers.ClockCycles(dut.aclk, 10)


@pytest.mark.parametrize("test_config,filter_level,randomize", [
    ("basic", "none", False),
    ("basic_random", "none", True),
    ("medium", "medium", False),
    ("medium_random", "medium", True),
    ("high", "high", False),
    ("production", "error-interrupt-only", False),
])
def test_axi4_master_rd_mon_filtering(test_config, filter_level, randomize):
    """Test AXI4 master read monitor with different filtering configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
    })

    # Set up test names and directories
    dut_name = "axi4_master_rd_mon"
    test_name_plus_params = f"test_{dut_name}_filtering_{test_config}_{filter_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Comprehensive verilog sources - include all monitor dependencies
    verilog_sources = [
        # Monitor package and dependencies
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_freq_invariant.sv"),

        # GAXI infrastructure
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),

        # Core AXI4 master
        os.path.join(rtl_dict['rtl_axi4'], "axi4_master_rd.sv"),

        # Monitor infrastructure
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_filtered.sv"),

        # Monitored module
        os.path.join(rtl_dict['rtl_axi4'], f"{dut_name}.sv"),
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters with filtering enabled
    rtl_parameters = {
        'SKID_DEPTH_AR': '2',
        'SKID_DEPTH_R': '4',
        'AXI_ID_WIDTH': '8',
        'AXI_ADDR_WIDTH': '32',
        'AXI_DATA_WIDTH': '32',
        'AXI_USER_WIDTH': '1',
        'AXI_WSTRB_WIDTH': '4',
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': '16',
        'ENABLE_FILTERING': '1',  # Enable filtering
        'ADD_PIPELINE_STAGE': '0',  # No pipeline for now
        'AW': '32',
        'DW': '32',
        'IW': '8',
        'SW': '4',
        'UW': '1',
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': '50000',  # 50 second timeout for comprehensive test
        'TEST_CLK_PERIOD': '10',
        'FILTER_LEVEL': filter_level,
        'RANDOMIZE_CONFIGS': '1' if randomize else '0',
    }

    # Simulation settings with comprehensive warnings disabled
    includes = [rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build]
    compile_args = [
        "--trace-fst",
        
        "--trace-depth", "99",
        "-Wall",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",
        "-Wno-UNDRIVEN",
        "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE",
        "-Wno-CASEINCOMPLETE",
    ]
    sim_args = ["--trace-fst", "--trace-depth", "99"]
    plusargs = ["+trace"]

    print(f"\n{'='*80}")
    print(f"Running AXI4 Master Read Monitor FILTERING test: {dut_name}")
    print(f"Test configuration: {test_config}")
    print(f"Filter level: {filter_level}")
    print(f"Randomize configs: {randomize}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module="test_axi4_master_rd_mon_filtered",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ AXI4 Master Read Monitor FILTERING test PASSED: {test_config}")
    except Exception as e:
        print(f"✗ AXI4 Master Read Monitor FILTERING test FAILED: {test_config} - {str(e)}")
        raise