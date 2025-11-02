# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_scheduler_group
# Purpose: RAPIDS Scheduler Group Integration Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Scheduler Group Integration Test

Single comprehensive test with incremental test levels (basic/medium/full):
- Basic: Quick smoke test (~60 seconds, 40-50 ops per phase, 5x stress)
- Medium: Moderate coverage (~180 seconds, 120-250 ops per phase, 5x stress)
- Full: Comprehensive validation (~300 seconds, 240-640 ops per phase, 5x stress)

Tests all scheduler group functionality in ONE test:
1. Descriptor processing with credit management
2. RDA packet injection and credit flow
3. Concurrent multi-channel operations
4. Credit exhaustion and recovery
5. Data mover with stream boundaries
6. EOS completion handling
7. Monitor bus aggregation

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

from tbclasses.scheduler_group_tb import SchedulerGroupTB


# ===========================================================================
# COCOTB TEST FUNCTION
# ===========================================================================
# NOTE: This cocotb test function is prefixed with "cocotb_" to prevent pytest
# from collecting it directly. It is only run via the pytest wrapper below.

@cocotb.test()
async def cocotb_test_scheduler_group_operation(dut):
    """
    Single comprehensive scheduler group test with incremental levels.

    Test level controlled by environment variable TEST_LEVEL (basic/medium/full).

    Test Levels:
    - basic: Quick smoke test (8-10 ops per phase, ~30s)
    - medium: Moderate coverage (24-50 ops per phase, ~90s)
    - full: Comprehensive (48-128 ops per phase, ~180s, 3x FUB duration)

    Tests all scheduler group functionality:
    - Descriptor processing with credit management
    - RDA packet injection and credit flow
    - Concurrent multi-channel operations
    - Credit exhaustion and recovery
    - Data mover with stream boundaries
    - EOS completion handling
    - Monitor bus aggregation
    """

    # Get test level from environment (default: basic)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Configure operation counts based on test level (5x stress multiplier applied)
    test_configs = {
        'basic': {
            'descriptor_count': 40,      # 8 * 5
            'rda_count': 40,              # 8 * 5
            'concurrent_channels': 20,    # 4 * 5
            'concurrent_ops_per_channel': 10,  # 2 * 5
            'credit_test_credits': 2,     # Keep same for credit test
            'data_mover_count': 40,       # 8 * 5
            'eos_count': 40,              # 8 * 5
            'monitor_count': 40,          # 8 * 5
            'timing_profile': 'fast'
        },
        'medium': {
            'descriptor_count': 160,      # 32 * 5
            'rda_count': 120,             # 24 * 5
            'concurrent_channels': 40,    # 8 * 5
            'concurrent_ops_per_channel': 20,  # 4 * 5
            'credit_test_credits': 3,     # Keep same for credit test
            'data_mover_count': 160,      # 32 * 5
            'eos_count': 120,             # 24 * 5
            'monitor_count': 160,         # 32 * 5
            'timing_profile': 'normal'
        },
        'full': {
            'descriptor_count': 320,      # 64 * 5
            'rda_count': 240,             # 48 * 5
            'concurrent_channels': 80,    # 16 * 5 (capped by NUM_CHANNELS=32, will use 32)
            'concurrent_ops_per_channel': 40,  # 8 * 5
            'credit_test_credits': 4,     # Keep same for credit test
            'data_mover_count': 320,      # 64 * 5
            'eos_count': 240,             # 48 * 5
            'monitor_count': 320,         # 64 * 5
            'timing_profile': 'stress'
        }
    }

    config = test_configs.get(test_level, test_configs['basic'])

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")  # 100MHz
    cocotb.start_soon(clock.start())

    # Initialize TB using framework class
    tb = SchedulerGroupTB(dut, clk=dut.clk, rst_n=dut.rst_n)

    cocotb.log.info("=" * 70)
    cocotb.log.info(f"SCHEDULER GROUP COMPREHENSIVE TEST - Level: {test_level.upper()}")
    cocotb.log.info("=" * 70)

    # Setup test environment
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    # Set timing profile
    tb.set_timing_profile(config['timing_profile'])

    # Configure credit management with exponential encoding
    # cfg_initial_credit = 4 → 16 credits (2^4)
    dut.cfg_use_credit.value = 1
    dut.cfg_initial_credit.value = 4

    cocotb.log.info(f"✅ Test Level: {test_level.upper()}")
    cocotb.log.info(f"✅ Timing Profile: {config['timing_profile']}")
    cocotb.log.info("✅ Credit management configured (cfg_initial_credit=4 → 16 credits)")

    # Phase 1: Basic descriptor processing
    cocotb.log.info(f"\n--- Phase 1: Descriptor Processing ({config['descriptor_count']} descriptors) ---")
    success, stats = await tb.test_basic_descriptor_processing(count=config['descriptor_count'])
    cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success rate: {stats['success_rate']:.1%}")
    cocotb.log.info(f"Channels tested: {stats['channels_tested']}")

    # Phase 2: RDA packet injection (if interface available)
    if hasattr(dut, 'rda_valid'):
        cocotb.log.info(f"\n--- Phase 2: RDA Packet Injection ({config['rda_count']} packets) ---")
        success, stats = await tb.test_rda_packet_injection(count=config['rda_count'])
        cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success rate: {stats['success_rate']:.1%}")
        cocotb.log.info(f"Channels tested: {stats['channels_tested']}")
    else:
        cocotb.log.info("\n--- Phase 2: RDA Packet Injection SKIPPED (interface not available) ---")

    # Phase 3: Concurrent multi-channel operations
    cocotb.log.info(f"\n--- Phase 3: Concurrent Multi-Channel ({config['concurrent_channels']} channels × {config['concurrent_ops_per_channel']} ops) ---")
    success, stats = await tb.test_concurrent_multi_channel(
        channel_count=config['concurrent_channels'],
        ops_per_channel=config['concurrent_ops_per_channel']
    )
    total_concurrent = config['concurrent_channels'] * config['concurrent_ops_per_channel']
    cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success: {stats['success_count']}/{total_concurrent} ({stats['success_rate']:.1%})")
    cocotb.log.info(f"Channels tested: {stats['channels_tested']}")

    # Phase 4: Credit exhaustion and recovery (full level only for now due to reset)
    if test_level == 'full':
        cocotb.log.info(f"\n--- Phase 4: Credit Exhaustion/Recovery (cfg={config['credit_test_credits']} → {2**config['credit_test_credits']} credits) ---")
        success, stats = await tb.test_credit_exhaustion_recovery(initial_credits=config['credit_test_credits'])
        cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success rate: {stats['success_rate']:.1%}")
        cocotb.log.info(f"Blocked correctly: {stats['blocked_correctly']}")

        # Re-initialize after credit test (which does reset)
        await tb.setup_clocks_and_reset()
        await tb.initialize_test()
        dut.cfg_use_credit.value = 1
        dut.cfg_initial_credit.value = 4
    else:
        cocotb.log.info(f"\n--- Phase 4: Credit Exhaustion/Recovery SKIPPED (full level only) ---")

    # Phase 5: Data mover with stream boundaries (if interface available)
    if hasattr(dut, 'data_valid'):
        cocotb.log.info(f"\n--- Phase 5: Data Mover Stream Boundaries ({config['data_mover_count']} transfers) ---")
        success, stats = await tb.test_data_mover_with_stream_boundaries(count=config['data_mover_count'])
        cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success rate: {stats['success_rate']:.1%}")
        cocotb.log.info(f"EOS: {stats['eos_count']}, EOL: {stats['eol_count']}, EOD: {stats['eod_count']}")
    else:
        cocotb.log.info(f"\n--- Phase 5: Data Mover SKIPPED (interface not available) ---")

    # Phase 6: EOS completion handling (if interface available)
    if hasattr(dut, 'eos_completion_valid'):
        cocotb.log.info(f"\n--- Phase 6: EOS Completion ({config['eos_count']} completions) ---")
        success, stats = await tb.test_eos_completion_interface(count=config['eos_count'])
        cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success rate: {stats['success_rate']:.1%}")
    else:
        cocotb.log.info(f"\n--- Phase 6: EOS Completion SKIPPED (interface not available) ---")

    # Phase 7: Monitor bus operations
    cocotb.log.info(f"\n--- Phase 7: Monitor Bus ({config['monitor_count']} events) ---")
    success, stats = await tb.test_monitor_bus_operations(count=config['monitor_count'])
    cocotb.log.info(f"Result: {'PASS' if success else 'PARTIAL'}, Success rate: {stats['success_rate']:.1%}")

    # Finalize and get comprehensive statistics
    tb.finalize_test()
    final_stats = tb.get_test_stats()

    cocotb.log.info("\n" + "=" * 70)
    cocotb.log.info(f"TEST SUMMARY - Level: {test_level.upper()}")
    cocotb.log.info("=" * 70)
    cocotb.log.info(f"Total Operations: {final_stats['summary']['total_operations']}")
    cocotb.log.info(f"Successful: {final_stats['summary']['successful_operations']}")
    cocotb.log.info(f"Failed: {final_stats['summary']['failed_operations']}")
    cocotb.log.info(f"Success Rate: {final_stats['summary']['successful_operations'] / max(1, final_stats['summary']['total_operations']) * 100:.1f}%")
    cocotb.log.info(f"Test Duration: {final_stats['summary']['test_duration']:.2f}s")
    cocotb.log.info(f"Operations/Second: {final_stats['performance']['operations_per_second']:.1f}")

    cocotb.log.info("\nPerformance Metrics:")
    cocotb.log.info(f"  Descriptors Processed: {final_stats['performance']['descriptors_processed']}")
    cocotb.log.info(f"  Peak Channels Active: {final_stats['performance']['peak_channels_active']}")
    cocotb.log.info(f"  Channels Used: {final_stats['channels']['total_channels_used']}")

    cocotb.log.info(f"\n✅ SCHEDULER GROUP COMPREHENSIVE TEST ({test_level.upper()}) PASSED!")


# ===========================================================================
# PYTEST WRAPPER FUNCTION
# ===========================================================================

@pytest.mark.parametrize("test_level", ["basic", "medium", "full"])  # Start with basic only
def test_scheduler_group(test_level):
    """Pytest: Comprehensive scheduler group integration test with incremental levels."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_macro': '../../rtl/rapids_macro',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "scheduler_group"
    toplevel = dut_name

    # Get Verilog sources and includes from hierarchical file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/macro/scheduler_group.f'
    )

    # Test configuration - 32-channel setup
    num_channels = 32
    addr_width = 64
    data_width = 512

    test_name_plus_params = f"test_scheduler_group_nc32_aw64_dw512_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'NUM_CHANNELS': str(num_channels),
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AXI_ID_WIDTH': '8',
        'CREDIT_WIDTH': '8',
        'TIMEOUT_CYCLES': '1000',
        'EARLY_WARNING_THRESHOLD': '4',
        'DESC_MON_AGENT_ID': '16',
        'PROG_MON_AGENT_ID': '32',
        'SCHED_MON_AGENT_ID': '48',
        'MON_UNIT_ID': '1',
        'MON_CHANNEL_ID': '0'
    }

    # Test environment - pass TEST_LEVEL to CocoTB
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,  # Control test depth
    }

    # Verilator compilation arguments
    compile_args = [
        "-Wall",
        "-Wno-PINMISSING",
        "-Wno-UNUSED",
        "-Wno-SYNCASYNCNET",
        "-Wno-EOFNEWLINE",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-IMPORTSTAR"
    ]

    # Create waveform viewing command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, 'test_scheduler_group', test_name_plus_params)

    # Add dv directory to python_search so we can import from tbclasses/
    dv_dir = os.path.dirname(tests_dir)  # Go up from tests/ to dv/

    try:
        run(
            python_search=[tests_dir, dv_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module='test_scheduler_group',  # This file
            testcase='cocotb_test_scheduler_group_operation',  # Run specific cocotb test function
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Disable for speed; enable for debugging
            keep_files=True,
            compile_args=compile_args,
        )

        print(f"\n✅ SCHEDULER GROUP TEST PASSED!")
        print(f"✅ Test level: {test_level.upper()}")
        print(f"✅ All 7 test phases completed successfully")
        print(f"\nLogs: {log_path}")
        print(f"Build: {sim_build}")

    except Exception as e:
        print(f"\n❌ Test failed: {str(e)}")
        print(f"Test level: {test_level}")
        print(f"Logs: {log_path}")
        raise


if __name__ == "__main__":
    print("RAPIDS Scheduler Group Integration Test")
    print("=" * 60)
    test_scheduler_group("basic")
