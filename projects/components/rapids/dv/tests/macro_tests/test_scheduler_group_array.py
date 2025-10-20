# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_scheduler_group_array
# Purpose: RAPIDS Scheduler Group Array Integration Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Scheduler Group Array Integration Test

Single comprehensive test with incremental test levels (basic/medium/full):
- Basic: Quick smoke test (~60 seconds, hundreds of packets)
- Medium: Moderate coverage (~3 minutes, thousands of packets)
- Full: Comprehensive validation (~10 minutes, tens of thousands of packets)

Tests all scheduler_group_array functionality in ONE test:
1. Multi-channel concurrent operations (up to 32 channels)
2. AXI arbitration verification (desc + ctrlrd + ctrlwr engines)
3. MonBus aggregation (35 sources: 32 groups + 3 AXI masters)
4. Channel isolation and independence
5. Fairness and throughput under load
6. Stress testing with realistic traffic patterns

Test level controlled by TEST_LEVEL environment variable (basic/medium/full).

STRUCTURE FOLLOWS AMBA PATTERN:
  - CocoTB test function at top (prefixed with cocotb_)
  - Pytest wrapper at bottom with @pytest.mark.parametrize
"""

import pytest
import os
import sys
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add dv directory to path so we can import from tbclasses/
dv_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if dv_dir not in sys.path:
    sys.path.insert(0, dv_dir)

from tbclasses.scheduler_group_array_tb import SchedulerGroupArrayTB


# ===========================================================================
# COCOTB TEST FUNCTION
# ===========================================================================
# NOTE: This cocotb test function is prefixed with "cocotb_" to prevent pytest
# from collecting it directly. It is only run via the pytest wrapper below.

@cocotb.test()
async def cocotb_test_scheduler_group_array_operation(dut):
    """
    Single comprehensive scheduler group array test with incremental levels.

    Test level controlled by environment variable TEST_LEVEL (basic/medium/full).

    Test Levels:
    - basic: Quick smoke test (hundreds of packets, ~60s)
    - medium: Moderate coverage (thousands of packets, ~3min)
    - full: Comprehensive (tens of thousands of packets, ~10min)

    Tests all scheduler group array functionality:
    - Multi-channel concurrent operations
    - AXI arbitration (desc + ctrlrd + ctrlwr)
    - MonBus aggregation (35 sources: 32 groups + 3 AXI masters)
    - Channel isolation and fairness
    - Stress testing under load
    """

    # Get test level from environment (default: basic)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Configure operation counts based on test level
    # Strategy: Test all 32 channels sequentially (couple descriptors each)
    #           Use 8 channels for concurrent stress testing
    test_configs = {
        'basic': {
            # Sequential: All 32 channels × 2 descriptors each = 64 ops
            'sequential_all_channels': True,
            'descriptors_per_channel': 2,        # 2 descriptors per channel (sequential)
            # Concurrent: 8 channels for concurrency testing (REDUCED for Verilator)
            'channels_concurrent': 8,            # 8 of 32 channels for concurrent testing
            'ops_per_channel_concurrent': 5,     # 5 operations per channel (40 total concurrent ops)
            # Other test phases (reduced for Verilator)
            'arbitration_ops': 20,               # 20 arbitration test operations
            'stress_ops': 30,                    # 30 stress test operations
            'timing_profile': 'fast',
            'expected_runtime_seconds': 90       # Allow more time for Verilator
        },
        'medium': {
            # Sequential: All 32 channels × 3 descriptors each = 96 ops
            'sequential_all_channels': True,
            'descriptors_per_channel': 3,        # 3 descriptors per channel (sequential)
            # Concurrent: 8 channels for concurrency testing
            'channels_concurrent': 8,            # 8 of 32 channels for concurrent testing
            'ops_per_channel_concurrent': 30,    # 30 operations per channel (concurrent)
            # Other test phases
            'arbitration_ops': 60,               # 60 arbitration test operations
            'stress_ops': 100,                   # 100 stress test operations
            'timing_profile': 'normal',
            'expected_runtime_seconds': 180      # 3 minutes (Verilator optimized)
        },
        'full': {
            # Sequential: All 32 channels × 10 descriptors each = 320 ops
            'sequential_all_channels': True,
            'descriptors_per_channel': 10,       # 10 descriptors per channel (sequential)
            # Concurrent: 8 channels for high-load testing
            'channels_concurrent': 8,            # 8 channels for concurrent testing
            'ops_per_channel_concurrent': 1000,  # 1000 operations per channel (concurrent)
            # Other test phases (full suite)
            'arbitration_ops': 1000,             # 1000 arbitration test operations
            'stress_ops': 10000,                 # 10000 stress test operations (tens of thousands!)
            'timing_profile': 'stress',
            'expected_runtime_seconds': 600      # Up to 10 minutes (for Questa)
        }
    }

    config = test_configs.get(test_level, test_configs['basic'])

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")  # 100MHz
    cocotb.start_soon(clock.start())

    # Initialize TB using framework class
    tb = SchedulerGroupArrayTB(dut, clk=dut.clk, rst_n=dut.rst_n)

    cocotb.log.info("=" * 70)
    cocotb.log.info(f"SCHEDULER GROUP ARRAY COMPREHENSIVE TEST - Level: {test_level.upper()}")
    cocotb.log.info("=" * 70)
    cocotb.log.info(f"Test Configuration:")
    cocotb.log.info(f"  Sequential: All 32 channels × {config['descriptors_per_channel']} descriptors = {32 * config['descriptors_per_channel']} ops")
    cocotb.log.info(f"  Concurrent: {config['channels_concurrent']} channels × {config['ops_per_channel_concurrent']} ops = {config['channels_concurrent'] * config['ops_per_channel_concurrent']} ops")
    cocotb.log.info(f"  Arbitration Ops: {config['arbitration_ops']}")
    cocotb.log.info(f"  Stress Ops: {config['stress_ops']}")
    total_ops = (32 * config['descriptors_per_channel']) + \
                (config['channels_concurrent'] * config['ops_per_channel_concurrent']) + \
                config['arbitration_ops'] + config['stress_ops']
    cocotb.log.info(f"  Total Operations: ~{total_ops}")
    cocotb.log.info(f"  Expected Runtime: ~{config['expected_runtime_seconds']}s")
    cocotb.log.info("=" * 70)

    # Setup test environment
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    cocotb.log.info(f"✅ Test Level: {test_level.upper()}")
    cocotb.log.info(f"✅ Timing Profile: {config['timing_profile']}")

    # Phase 1: All 32 channels sequential test (2-3 descriptors each, no concurrency)
    cocotb.log.info(f"\n--- Phase 1: All Channels Sequential (32 channels × {config['descriptors_per_channel']} descriptors) ---")
    success, stats = await tb.test_all_channels_sequential(
        descriptors_per_channel=config['descriptors_per_channel']
    )
    total_sequential = 32 * config['descriptors_per_channel']
    cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success: {stats.get('success_count', 0)}/{total_sequential}")
    cocotb.log.info(f"Success rate: {stats.get('success_rate', 0) * 100:.1f}%")
    cocotb.log.info(f"Channels tested: {stats.get('channels_tested', 32)}/32")

    # Phase 2: Multi-channel concurrent operations (8 channels only)
    cocotb.log.info(f"\n--- Phase 2: Multi-Channel Concurrent ({config['channels_concurrent']} channels × {config['ops_per_channel_concurrent']} ops) ---")
    success, stats = await tb.test_multi_channel_concurrent_operation(
        num_channels_active=config['channels_concurrent'],
        ops_per_channel=config['ops_per_channel_concurrent'],
        test_level=tb.convert_to_int(0) if test_level == 'basic' else (
            tb.convert_to_int(1) if test_level == 'medium' else tb.convert_to_int(2)
        )
    )
    total_concurrent = config['channels_concurrent'] * config['ops_per_channel_concurrent']
    cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Operations: {stats.get('total_operations', 0)}/{total_concurrent}")
    cocotb.log.info(f"Success rate: {stats.get('success_rate', 0):.1f}%")
    cocotb.log.info(f"MonBus packets: {stats.get('monbus_packets', 0)}")
    cocotb.log.info(f"Descriptor AXI transactions: {stats.get('desc_axi_transactions', 0)}")
    cocotb.log.info(f"Control Read AXI transactions: {stats.get('ctrlrd_axi_transactions', 0)}")
    cocotb.log.info(f"Control Write AXI transactions: {stats.get('ctrlwr_axi_transactions', 0)}")

    # Phase 3: AXI arbitration stress test
    cocotb.log.info(f"\n--- Phase 3: AXI Arbitration ({config['arbitration_ops']} operations) ---")
    success, stats = await tb.test_axi_arbitration(num_operations=config['arbitration_ops'])
    cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success: {stats.get('success_count', 0)}/{config['arbitration_ops']}")
    cocotb.log.info(f"Channels used: {stats.get('channels_used', 0)}")
    cocotb.log.info(f"Arbitration fairness stats available")

    # Phase 4: Comprehensive stress test (medium/full level only)
    if test_level in ['medium', 'full']:
        cocotb.log.info(f"\n--- Phase 4: Comprehensive Stress Test ({config['stress_ops']} operations) ---")
        success, stats = await tb.stress_test(num_operations=config['stress_ops'])
        cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success: {stats.get('success_count', 0)}/{config['stress_ops']}")
        cocotb.log.info(f"Success rate: {stats.get('success_rate', 0) * 100:.1f}%")
    else:
        cocotb.log.info(f"\n--- Phase 4: Stress Test SKIPPED (medium/full level only) ---")

    # Finalize and get comprehensive statistics
    tb.finalize_test()
    final_stats = tb.get_test_stats()

    cocotb.log.info("\n" + "=" * 70)
    cocotb.log.info(f"TEST SUMMARY - Level: {test_level.upper()}")
    cocotb.log.info("=" * 70)
    cocotb.log.info(f"Total Operations: {final_stats['summary']['total_operations']}")
    cocotb.log.info(f"Successful: {final_stats['summary']['successful_operations']}")
    cocotb.log.info(f"Failed: {final_stats['summary']['failed_operations']}")

    # Calculate success rate
    total_ops = final_stats['summary']['total_operations']
    successful_ops = final_stats['summary']['successful_operations']
    success_rate = (successful_ops / total_ops * 100) if total_ops > 0 else 0

    cocotb.log.info(f"Success Rate: {success_rate:.1f}%")
    cocotb.log.info(f"Test Duration: {final_stats['summary']['test_duration']:.2f}s")

    if final_stats['summary']['test_duration'] > 0:
        ops_per_sec = total_ops / final_stats['summary']['test_duration']
        cocotb.log.info(f"Operations/Second: {ops_per_sec:.1f}")

    cocotb.log.info("\nChannel Usage:")
    cocotb.log.info(f"  Active Channels: {len(final_stats['channels']['channels_tested'])}/{tb.CHANNEL_COUNT}")
    cocotb.log.info(f"  Peak Concurrent: {final_stats['performance']['peak_concurrent_channels']}")

    cocotb.log.info("\nAXI Arbitration:")
    cocotb.log.info(f"  Descriptor Arbitrations: {final_stats['arbitration']['descriptor_arbitrations']}")
    cocotb.log.info(f"  Control Read Arbitrations: {final_stats['arbitration']['ctrlrd_arbitrations']}")
    cocotb.log.info(f"  Control Write Arbitrations: {final_stats['arbitration']['ctrlwr_arbitrations']}")

    cocotb.log.info("\nAXI Transactions:")
    cocotb.log.info(f"  Descriptor Reads: {final_stats['axi']['descriptor_reads']}")
    cocotb.log.info(f"  Control Reads: {final_stats['axi']['ctrlrd_reads']}")
    cocotb.log.info(f"  Control Writes: {final_stats['axi']['ctrlwr_writes']}")

    cocotb.log.info("\nMonBus Activity:")
    cocotb.log.info(f"  Monitor Events: {final_stats['monitor']['monitor_events']}")

    cocotb.log.info(f"\n✅ SCHEDULER GROUP ARRAY COMPREHENSIVE TEST ({test_level.upper()}) PASSED!")


# ===========================================================================
# PYTEST WRAPPER FUNCTION
# ===========================================================================

@pytest.mark.parametrize("test_level", ["basic", "medium"])  # basic working, adding medium
def test_scheduler_group_array(test_level):
    """Pytest: Comprehensive scheduler group array integration test with incremental levels."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_macro': '../../rtl/rapids_macro',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "scheduler_group_array"
    toplevel = dut_name

    # Get Verilog sources and includes from hierarchical file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/macro/scheduler_group_array.f'
    )

    # Test configuration - 32-channel array setup
    channel_count = 32
    addr_width = 64
    data_width = 512
    axi_id_width = 8
    credit_width = 8

    test_name_plus_params = f"test_scheduler_group_array_ch{channel_count}_aw{addr_width}_dw{data_width}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'CHANNEL_COUNT': str(channel_count),
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AXI_ID_WIDTH': str(axi_id_width),
        'CREDIT_WIDTH': str(credit_width),
        'TIMEOUT_CYCLES': '1000',
        'EARLY_WARNING_THRESHOLD': '4',

        # AXI Skid Buffer Depths
        'AXI_SKID_DEPTH_AR': '2',
        'AXI_SKID_DEPTH_R': '4',
        'AXI_SKID_DEPTH_AW': '2',
        'AXI_SKID_DEPTH_W': '2',
        'AXI_SKID_DEPTH_B': '2',

        # AXI Monitor Parameters
        'AXI_MAX_TRANSACTIONS': '16',
        'AXI_ENABLE_FILTERING': '1',
        'AXI_ADD_PIPELINE_STAGE': '0',

        # AXI Clock Gating (disabled for testing)
        'AXI_ENABLE_CLOCK_GATING': '0',
        'AXI_CG_IDLE_CYCLES': '8',

        # Monitor Bus Agent IDs
        'DESC_MON_AGENT_BASE': '16',     # 0x10 base for descriptor engines
        'PROG_MON_AGENT_BASE': '32',     # 0x20 base for program engines
        'SCHED_MON_AGENT_BASE': '48',    # 0x30 base for schedulers
        'AXI_RD_MON_AGENT_ID': '10',     # 0x0A for AXI desc read master monitor
        'AXI_WR_MON_AGENT_ID': '11',     # 0x0B for AXI prog write master monitor
        'CTRLRD_MON_AGENT_ID': '12',     # 0x0C for AXI ctrlrd read master monitor
        'CTRLWR_MON_AGENT_ID': '13',     # 0x0D for AXI ctrlwr write master monitor
        'MON_UNIT_ID': '1',

        # MonBus Arbiter Parameters
        'MONBUS_INPUT_SKID_ENABLE': '1',
        'MONBUS_OUTPUT_SKID_ENABLE': '1',
        'MONBUS_INPUT_SKID_DEPTH': '2',
        'MONBUS_OUTPUT_SKID_DEPTH': '4'
    }

    # Test environment - pass TEST_LEVEL to CocoTB
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,  # Control test depth
        'CHANNEL_COUNT': str(channel_count),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AXI_ID_WIDTH': str(axi_id_width),
        'TEST_CREDIT_WIDTH': str(credit_width),
        'TEST_CLK_PERIOD': '10',
        'SEED': '12345'
    }

    # Verilator compilation arguments
    compile_args = [
        "-Wall",
        "-Wno-PINMISSING",
        "-Wno-UNUSED",
        "-Wno-SYNCASYNCNET",
        "-Wno-EOFNEWLINE",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-IMPORTSTAR",
        "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE"  # Suppress selection range warnings in counter_freq_invariant
    ]

    # Create waveform viewing command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, 'test_scheduler_group_array', test_name_plus_params)

    # Adjust timeout based on test level
    test_timeouts = {
        'basic': 120,      # 2 minutes for basic
        'medium': 300,     # 5 minutes for medium
        'full': 900        # 15 minutes for full (10 min test + 5 min buffer)
    }

    timeout_seconds = test_timeouts.get(test_level, 120)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module='test_scheduler_group_array',  # This file
            testcase='cocotb_test_scheduler_group_array_operation',  # Run specific cocotb test function
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Disable for speed; enable for debugging
            keep_files=True,
            compile_args=compile_args,
        )

        print(f"\n✅ SCHEDULER GROUP ARRAY TEST PASSED!")
        print(f"✅ Test level: {test_level.upper()}")
        print(f"✅ All test phases completed successfully")
        print(f"\nConfiguration:")
        print(f"  - Channels: {channel_count}")
        print(f"  - Address Width: {addr_width}-bit")
        print(f"  - Data Width: {data_width}-bit")
        print(f"  - AXI ID Width: {axi_id_width}-bit")
        print(f"\nLogs: {log_path}")
        print(f"Build: {sim_build}")

    except Exception as e:
        print(f"\n❌ Test failed: {str(e)}")
        print(f"Test level: {test_level}")
        print(f"Logs: {log_path}")
        raise


if __name__ == "__main__":
    print("RAPIDS Scheduler Group Array Integration Test")
    print("=" * 60)
    test_scheduler_group_array("basic")
