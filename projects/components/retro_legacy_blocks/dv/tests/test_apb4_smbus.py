# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb4_smbus
# Purpose: SMBus 2.0 Controller Test Runner
#
# Documentation: projects/components/retro_legacy_blocks/rtl/smbus/README.md
# Subsystem: retro_legacy_blocks/smbus
#
# Created: 2025-11-29

"""
SMBus 2.0 Controller Test Runner

Test runner for the APB SMBus module with support for multiple configurations.
Follows the same methodology as HPET for consistency.

Features:
- Parametrized testing with pytest
- Support for CDC and non-CDC configurations
- Multiple test levels (basic, medium, full)
- Environment variable configuration
- Proper file and directory management
- Integration with CocoTB framework
- Modular test structure
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
import sys
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.retro_legacy_blocks.dv.tbclasses.smbus.smbus_tb import SMBusTB, SMBusRegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.smbus.smbus_tests_basic import SMBusBasicTests
# GH#58 RED regression tests (coordinator-directed, written against the
# unfixed RTL - see smbus_tests_medium.py's module docstring for the
# full per-item defect writeup). Registered at medium/full level below,
# alongside the existing (untouched) medium_test_methods.
from projects.components.retro_legacy_blocks.dv.tbclasses.smbus.smbus_tests_medium import SMBusMediumTests


@cocotb.test(timeout_time=20000, timeout_unit="us")
async def smbus_test(dut):
    """Main test function for SMBus module with modular test structure"""
    tb = SMBusTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'SMBus test with seed: {seed}')

    # Get test level from environment
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    valid_levels = ['gate', 'func', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'. Valid: {valid_levels}")
        test_level = 'gate'

    # Setup clocks and reset
    await tb.setup_clocks_and_reset()

    # Setup components after reset
    await tb.setup_components()

    tb.log.info(f"Starting {test_level.upper()} SMBus test...")
    tb.log.info("Configuration: SMBus 2.0 Master/Slave with PEC and FIFOs")

    # Create test suite
    basic_tests = SMBusBasicTests(tb)
    gh58_tests = SMBusMediumTests(tb)

    # Run all tests - test list varies by test level
    results = []

    # Basic tests (always run)
    basic_test_methods = [
        ('Register Access', basic_tests.test_register_access),
        ('Master Enable/Disable', basic_tests.test_master_enable_disable),
        ('Clock Configuration', basic_tests.test_clock_configuration),
        ('Timeout Configuration', basic_tests.test_timeout_configuration),
        ('Status Register', basic_tests.test_status_register),
        ('FIFO Status', basic_tests.test_fifo_status),
        ('FIFO Write', basic_tests.test_fifo_write),
        ('Interrupt Enable', basic_tests.test_interrupt_enable),
    ]

    # Medium tests (medium and full levels)
    medium_test_methods = [
        ('PEC Enable', basic_tests.test_pec_enable),
        ('Fast Mode Enable', basic_tests.test_fast_mode_enable),
        ('Slave Mode Config', basic_tests.test_slave_mode_config),
        ('Command Register', basic_tests.test_command_register),
        # GH#58 RED regression tests - written FIRST, against the unfixed
        # RTL, at the coordinator's direction. Each is expected to FAIL
        # (RED) for a specific, mechanism-traced reason documented in
        # smbus_tests_medium.py; they are not skipped/xfail because the
        # RED result itself is the deliverable finding for rds-rtl-design.
        ('RLB-011 Slave address match and write', gh58_tests.test_rlb011_slave_write_and_address_match),
        ('RLB-011 Slave read and clock stretching', gh58_tests.test_rlb011_slave_read_and_stretch),
        ('RLB-011 Slave PEC and engine ownership', gh58_tests.test_rlb011_slave_pec_and_ownership),
        ('GH58-1 (C4) SCL toggle / open-drain', gh58_tests.test_gh58_c4_scl_toggle_and_open_drain),
        ('GH58-2 (C3) Timeout via real SCL stretch / TIMEOUT=0 disables it', gh58_tests.test_gh58_c3_timeout_detection_dead),
        ('GH58-12 Short stretch (< TIMEOUT) completes without error', gh58_tests.test_gh58_12_short_stretch_completes_without_error),
        ('GH58-3 (H5) Read protocols missing repeated START', gh58_tests.test_gh58_h5_read_missing_repeated_start),
        ('GH58-4 (H6) TX FIFO pushes stale data', gh58_tests.test_gh58_h6_tx_fifo_stale_data),
        ('GH58-5 (H7) PEC generation garbage / checking absent', gh58_tests.test_gh58_h7_pec_generation_and_checking),
        ('GH58-6 (H8/qc4) DATA/PEC clobbered one cycle after SW write', gh58_tests.test_gh58_h8_data_pec_clobbered),
        ('GH58-7 (qc1) INT_STATUS never sticky / W1C ineffective', gh58_tests.test_gh58_qc1_int_status_not_sticky),
        ('GH58-8 (qc2) smb_interrupt bypasses INT_STATUS', gh58_tests.test_gh58_qc2_interrupt_bypasses_int_status),
        ('GH58-9 (qc5/round_3-1) Byte engine hang', gh58_tests.test_gh58_qc5_byte_engine_bounded_completion),
        ('GH58-10 (qc6) r_bytes_total always from block_count', gh58_tests.test_gh58_qc6_bytes_total_from_block_count_always),
        ('GH58-11 Strict decode of unmapped addresses', gh58_tests.test_gh58_strict_decode),
        ('GH58-13 soft_reset mid-transfer recovery (+M2)', gh58_tests.test_gh58_13_soft_reset_mid_transfer),
        ('GH58-14 fast_mode spec-minimum timing (+M1)', gh58_tests.test_gh58_14_fast_mode_scl_ratio),
        ('GH58-R2-H1 Write Word FIFO', gh58_tests.test_gh58_r2_h1_write_word_fifo),
        ('GH58-R2-H2 Block Write FIFO', gh58_tests.test_gh58_r2_h2_block_write_fifo),
        ('GH58-R2-H3a stop-alone mid-transfer abort', gh58_tests.test_gh58_r2_h3a_stop_alone_mid_transfer),
        ('GH58-R2-H4 slave stretches the final STOP', gh58_tests.test_gh58_r2_h4_stretch_through_stop_hangs),
        ('GH58-R2-H5 Block Read byte accounting', gh58_tests.test_gh58_r2_h5_block_read),
        ('GH58-R2-H6 Block Process Call write half', gh58_tests.test_gh58_r2_h6_block_process_call),
        ('GH58-R2-M3 spurious tx_thresh at reset', gh58_tests.test_gh58_r2_m3_spurious_tx_thresh_at_reset),
        ('GH58-R2-M4 SMBUS_PEC readback', gh58_tests.test_gh58_r2_m4_pec_register_readback),
        ('GH58-R2-M5 TX FIFO underrun contract', gh58_tests.test_gh58_r2_m5_fifo_underrun_overrun_contract),
        ('GH58-R2-M6 block-count clamp (0x40)', gh58_tests.test_gh58_r2_m6_block_count_clamp),
        ('GH58-R2-M8 bus-free check before START', gh58_tests.test_gh58_r2_m8_bus_free_before_start),
        ('GH58-R2-L3 (guard) master_en clear', gh58_tests.test_gh58_r2_l3_master_en_clear_guard),
        ('GH58-R2-L4 (guard) Quick Command R/W bit', gh58_tests.test_gh58_r2_l4_quick_cmd_rw_bit),
        ('GH58-R3-1 real STOP condition per transaction type', gh58_tests.test_gh58_r3_1_stop_condition_every_type),
        ('GH58-R3-2 busy=0 coincides with lines released', gh58_tests.test_gh58_r3_2_busy_zero_coincides_with_release),
        ('GH58-R3-3 RX FIFO full then Receive Byte', gh58_tests.test_gh58_r3_3_rx_fifo_full_receive_byte),
        ('GH58-R3-4 (guard) fast-mode tSU;STO/tBUF fixed', gh58_tests.test_gh58_r3_4_fast_mode_stop_buf_units_fixed),
        ('GH58-R3-5 (guard) strobe width behind the bridge', gh58_tests.test_gh58_r3_5_strobe_width_two_pclk),
        ('GH58-R3-6 slave never releases SDA', gh58_tests.test_gh58_r3_6_slave_never_releases_sda),
        ('GH58-R4-1 complete=1 after failed recovery', gh58_tests.test_gh58_r4_1_complete_after_failed_recovery),
        ('GH58-R4-2 stale idle-bus phy_timeout', gh58_tests.test_gh58_r4_2_stale_idle_timeout),
        ('GH58-R4-3 r_started guard stale after success', gh58_tests.test_gh58_r4_3_started_guard_stale_after_success),
        ('GH58-R4-4 recovery-clock tLOW/tHIGH', gh58_tests.test_gh58_r4_4_recovery_clock_timing),
        ('GH58-R4-9 (guard) recovery no same-edge drop', gh58_tests.test_gh58_r4_9_recovery_no_same_edge_drop),
        ('GH58-R4-8 (guard) full-density abort sweep', gh58_tests.test_gh58_r4_8_full_density_abort_sweep),
        ('GH58-R4-10 TX FIFO push honors PSTRB', gh58_tests.test_gh58_r4_10_tx_fifo_pstrb),
        ('GH58-R5-1 fifo_reset clears stale TX data', gh58_tests.test_gh58_r5_1_fifo_reset_clears_stale_tx_data),
        ('RLB-011 quick command read', gh58_tests.test_rlb011_quick_command_read),
        ('RLB-011 arbitration lost', gh58_tests.test_rlb011_arbitration_lost),
        ('GH58-R6-1 fifo_reset during receive keeps level consistent', gh58_tests.test_gh58_r6_1_fifo_reset_during_receive_keeps_level_consistent),
        ('GH58-R6-2 fifo_reset TX side + longer-window harmless', gh58_tests.test_gh58_r6_2_fifo_reset_tx_and_width_harmless),
    ]

    # Full tests (full level only)
    full_test_methods = [
        ('Full Register Sweep', basic_tests.test_full_register_sweep),
        ('FIFO Stress', basic_tests.test_fifo_stress),
        ('Config Stress', basic_tests.test_config_stress),
        # Protocol transaction type tests
        ('Transaction Type - Quick Command', basic_tests.test_transaction_type_quick_cmd),
        ('Transaction Type - Send Byte', basic_tests.test_transaction_type_send_byte),
        ('Transaction Type - Receive Byte', basic_tests.test_transaction_type_recv_byte),
        ('Transaction Type - Write Byte', basic_tests.test_transaction_type_write_byte),
        ('Transaction Type - Read Byte', basic_tests.test_transaction_type_read_byte),
        ('Transaction Type - Write Word', basic_tests.test_transaction_type_write_word),
        ('Transaction Type - Read Word', basic_tests.test_transaction_type_read_word),
        ('Transaction Type - Block Write', basic_tests.test_transaction_type_block_write),
        ('Transaction Type - Block Read', basic_tests.test_transaction_type_block_read),
        ('Transaction Type - Block Process Call', basic_tests.test_transaction_type_block_proc),
        # Additional protocol tests
        ('PEC Calculation', basic_tests.test_pec_calculation),
        ('Interrupt Status W1C', basic_tests.test_interrupt_status_w1c),
        ('All Transaction Types', basic_tests.test_all_transaction_types),
        ('FIFO Full Detection', basic_tests.test_fifo_full_detection),
        ('Clock Configuration Values', basic_tests.test_clock_configuration_values),
        ('Timeout Configuration Values', basic_tests.test_timeout_configuration_values),
        ('Slave Address Range', basic_tests.test_slave_address_range),
        ('Own Address Configuration', basic_tests.test_own_address_configuration),
    ]

    # Select test methods based on level
    if test_level == 'gate':
        test_methods = basic_test_methods
    elif test_level == 'func':
        test_methods = basic_test_methods + medium_test_methods
    else:  # full
        test_methods = basic_test_methods + medium_test_methods + full_test_methods

    for test_name, test_method in test_methods:
        tb.log.info(f"\n{'=' * 80}")
        tb.log.info(f"Running: {test_name}")
        tb.log.info(f"{'=' * 80}")
        result = await test_method()
        results.append((test_name, result))

    # Print summary
    tb.log.info("\n" + "=" * 80)
    tb.log.info("TEST SUMMARY")
    tb.log.info("=" * 80)

    passed_count = sum(1 for _, result in results if result)
    total_count = len(results)

    for test_name, result in results:
        status = "PASSED" if result else "FAILED"
        tb.log.info(f"{test_name:40s} {status}")

    tb.log.info(f"\nPassed: {passed_count}/{total_count}")

    # Overall result
    all_passed = all(result for _, result in results)

    if all_passed:
        tb.log.info("\nAll SMBus tests PASSED!")
    else:
        tb.log.error("\nSome SMBus tests FAILED")
        assert False, f"SMBus test failed: {passed_count}/{total_count} tests passed"


def generate_test_params():
    """Generate test parameter combinations for different SMBus configurations

    Note: SMBus RTL supports CDC_ENABLE parameter for clock domain crossing.
    """

    return [
        # (cdc_enable, test_level, description)
        # Standard configurations (no CDC)
        (0, 'gate', "SMBus standard gate"),
        (0, 'func', "SMBus standard func"),
        (0, 'full', "SMBus standard full"),

        # CDC configurations (async clock domains)
        (1, 'gate', "SMBus with CDC gate"),
        (1, 'func', "SMBus with CDC func"),
        (1, 'full', "SMBus with CDC full"),
    ]


@pytest.mark.parametrize("cdc_enable, test_level, description",
                        generate_test_params())
def test_smbus(request, cdc_enable, test_level, description):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Test SMBus 2.0 Controller with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb4_smbus"

    # Create human-readable test identifier
    cdc_str = "cdc" if cdc_enable else ""

    test_name_plus_params = (f"test_smbus_{test_level}"
                            f"{('_' + cdc_str) if cdc_str else ''}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/smbus/filelists/apb4_smbus.f'
    )

    # RTL parameters
    rtl_parameters = {
        'CDC_ENABLE': str(cdc_enable),
        'FIFO_DEPTH': '32',  # 32 bytes per SMBus 2.0 spec
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
    }

    # WAVES support
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    # Simulation settings
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--timescale", "1ns/1ps",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
        "-Wno-CASEINCOMPLETE",
        "-Wno-BLKANDNBLK",
        "-Wno-MULTIDRIVEN",
        "-Wno-TIMESCALEMOD",
    ]
    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    cdc_mode = "CDC enabled (async clocks)" if cdc_enable else "No CDC (same clock)"
    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} SMBus test: {description}")
    print(f"Configuration: 32-byte FIFOs, PEC support")
    print(f"Clock domain: {cdc_mode}")
    print(f"{'='*80}")

    try:
        run(
            simulator="verilator",
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"SMBus test PASSED: {description}")

    except Exception as e:
        print(f"SMBus test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for SMBus:")
        print("- Check that pclk is running")
        print("- Verify reset sequence")
        print("- Check master enable configuration")
        print("- Verify clock divider settings")
        print("- Check FIFO operations")
        print(f"- Configuration: CDC={cdc_enable}, FIFO_DEPTH=32")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple SMBus test...")
    pytest.main([__file__, "-v", "-s"])
