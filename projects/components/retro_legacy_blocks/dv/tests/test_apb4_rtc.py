# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb4_rtc
# Purpose: RTC Test Runner - Updated Scalable Version
#
# Documentation: projects/components/retro_legacy_blocks/rtl/rtc/README.md
# Subsystem: retro_legacy_blocks/rtc
#
# Created: 2025-11-15

"""
RTC Test Runner - Updated Scalable Version

Test runner for the APB RTC module with support for multiple test levels.
Follows the same methodology as HPET for consistency.

Features:
- Parametrized testing with pytest
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
from projects.components.retro_legacy_blocks.dv.tbclasses.rtc.rtc_tb import RTCTB, RTCRegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.rtc.rtc_tests_basic import RTCBasicTests
from projects.components.retro_legacy_blocks.dv.tbclasses.rtc.rtc_tests_medium import RTCMediumTests


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def rtc_test(dut):
    """Main test function for RTC module with modular test structure.

    timeout_time bumped from 800us to 3000us (GH#56 coordinator-direction
    test 4), then 5000us (tests 5/6), then 6000us (test 11), then 7000us
    (test 14), then 8000us (test 18, fifth review round), then 10000us
    (GH56-R6-E(a)/(b), sixth review round) - each of tests
    4/5/6/11/14/18/R6-E(a)/R6-E(b) deliberately waits past rtc_core.sv's
    COMMIT_TIMEOUT (65535 pclk cycles, ~0.66ms of sim time at this suite's
    10ns pclk period), so eight such waits plus the rest of the full suite
    (~300-1000us) needs headroom past ~6ms.
    """
    tb = RTCTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'RTC test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} RTC test...")
    tb.log.info("Configuration: Time-of-day tracking with alarm")

    # Create test suites
    basic_tests = RTCBasicTests(tb)
    gh56_tests = RTCMediumTests(tb)

    # Run all tests - test list varies by test level
    results = []

    # Basic tests (always run)
    basic_test_methods = [
        ('Register Access', basic_tests.test_register_access),
        ('RTC Enable/Disable', basic_tests.test_rtc_enable_disable),
        ('Time Setting', basic_tests.test_time_setting),
        ('Time Counting', basic_tests.test_time_counting),
        ('Alarm Basic', basic_tests.test_alarm_basic),
        ('Status Flags', basic_tests.test_status_flags),
    ]

    # Medium tests (medium and full levels)
    medium_test_methods = [
        ('BCD Mode', basic_tests.test_bcd_mode),
        ('12-Hour Mode', basic_tests.test_12_hour_mode),
        # GitHub #56 defect-regression: expected RED against current RTL
        # (production-mode clocking, cfg_clock_select=0 - see
        # rtc_tests_medium.py module docstring). Registered at medium/full
        # (func+full), gate stays basic-only/fast per the RLB convention.
        ('GH56-A Time-Set Production Mode', gh56_tests.test_gh56_time_set_production_mode),
        ('GH56-B Time-Set Atomicity', gh56_tests.test_gh56_time_set_atomicity),
        ('GH56-C Coherent Reads Across Rollover', gh56_tests.test_gh56_coherent_reads_across_rollover),
        ('GH56-D BCD Calendar Rollover', gh56_tests.test_gh56_bcd_calendar_rollover),
        ('GH56-E 12-Hour Mode Transitions', gh56_tests.test_gh56_12_hour_mode_transitions),
        ('GH56-F W1C Not Undone By Wide Tick', gh56_tests.test_gh56_w1c_not_undone_by_wide_tick),
        ('GH56-G Alarm Not During Time-Set', gh56_tests.test_gh56_alarm_not_during_time_set),
        ('GH56-H Address Decode PSLVERR', gh56_tests.test_gh56_address_decode_pslverr),
        ('GH56-I rtc_resetn Guard', gh56_tests.test_gh56_rtc_resetn_guard),
        # Coordinator direction 2026-09-09: four RED tests against the
        # landed (uncommitted) GH#56 RTL follow-up - see rtc_tests_medium.py
        # for the full defect writeup.
        ('GH56-1 One-Sided Reset No Phantom Commit',
         gh56_tests.test_gh56_one_sided_reset_no_phantom_commit),
        ('GH56-2 Polling RTC_SECONDS Sees Ticks', gh56_tests.test_gh56_polling_seconds_sees_ticks),
        ('GH56-3 Alarm Fires At Readable Time', gh56_tests.test_gh56_alarm_fires_at_readable_time),
        ('GH56-4 Commit Timeout Is Reported', gh56_tests.test_gh56_commit_timeout_is_reported),
        # Coordinator direction 2026-09-09 (re-review): four more RED tests
        # against a further re-review of the uncommitted GH#56 RTL follow-up
        # - see rtc_tests_medium.py for the full defect writeup.
        ('GH56-5 Timed-Out Commit Lands Intact', gh56_tests.test_gh56_timed_out_commit_lands_intact),
        ('GH56-6 Retry After Timeout Lands', gh56_tests.test_gh56_retry_after_timeout_lands),
        ('GH56-7 RTC_SECONDS Read Latches Same Instant',
         gh56_tests.test_gh56_seconds_read_latches_same_instant),
        ('GH56-8 No Tick During Time-Set Mode', gh56_tests.test_gh56_no_tick_during_time_set_mode),
        # Coordinator direction 2026-09-09 (third re-review): four more RED
        # tests against a third re-review of the uncommitted GH#56 RTL
        # follow-up - see rtc_tests_medium.py for the full defect writeup.
        ('GH56-9 Presetn With Commit In Flight Lands Intact',
         gh56_tests.test_gh56_presetn_with_commit_in_flight_lands_intact),
        ('GH56-10 Presetn After Ack No Stale Ack', gh56_tests.test_gh56_presetn_after_ack_no_stale_ack),
        ('GH56-11 Retry During Timed-Out Stall Keeps Staged',
         gh56_tests.test_gh56_retry_during_timed_out_stall_keeps_staged),
        ('GH56-12 First Second After Commit Is Exact',
         gh56_tests.test_gh56_first_second_after_commit_is_exact),
        # Coordinator direction 2026-09-09 (fourth review round): three more
        # RED tests (a fourth, GH56-16, needs a small-COMMIT_TIMEOUT_CYCLES
        # build and runs under the separate test_rtc_gh56_timeout_sweep
        # pytest wrapper below, not here) - see rtc_tests_medium.py for the
        # full defect writeup.
        ('GH56-13 Commit During rtc_resetn Stall Is Dropped',
         gh56_tests.test_gh56_commit_during_rtc_reset_is_dropped),
        ('GH56-14 No Spurious Timeout After Presetn',
         gh56_tests.test_gh56_no_spurious_timeout_after_presetn),
        ('GH56-15 No Back-To-Back Update At Commit',
         gh56_tests.test_gh56_no_back_to_back_update_at_commit),
        # Coordinator direction 2026-09-09 (fifth review round): five more
        # RED tests - see rtc_tests_medium.py for the full defect writeup.
        ('GH56-17 Presetn Over Commit-Load Edge, Both Parities',
         gh56_tests.test_gh56_presetn_over_load_parity),
        ('GH56-18 Stall With Queued Retry Still Reports Timeout',
         gh56_tests.test_gh56_stall_with_retry_still_reports_timeout),
        ('GH56-19 Presetn Does Not Stop The Clock',
         gh56_tests.test_gh56_presetn_does_not_stop_the_clock),
        ('GH56-20 Presetn Does Not Switch The Test-Mode Clock',
         gh56_tests.test_gh56_presetn_does_not_switch_clock),
        ('GH56-21 Presetn Release, No Spurious Flags',
         gh56_tests.test_gh56_presetn_release_no_spurious_flags),
        # Coordinator direction 2026-09-09 (sixth round: three more
        # sim-testable RTL defects found in the fifth round's own fix,
        # plus one structural ordering test) - see rtc_tests_medium.py for
        # the full defect writeup. MED-C (cfg_valid crossing in the same
        # synchronizer bundle as the data it qualifies) has no
        # sim-observable form and is deliberately not tested here.
        ('GH56-R6-A Presetn During Staging Does Not Permanently Stop The Clock',
         gh56_tests.test_gh56_r6a_presetn_during_staging_stops_clock_forever),
        ('GH56-R6-A2 Presetn During Staging, Minimal Recovery',
         gh56_tests.test_gh56_r6a2_presetn_during_staging_minimal_recovery),
        # Coordinator correction 2026-09-09: A/A2 both happen to include a
        # post-presetn RTC_CONFIG write, which re-arms cfg_valid and is
        # exactly why they are GREEN - this variant does NO write at all
        # after release, exercising the actual defect.
        ('GH56-R6-A3 Presetn During Staging Resumes Counting Without A Write',
         gh56_tests.test_gh56_r6a3_presetn_during_staging_resumes_counting_without_write),
        ('GH56-R6-B Busy Released By Data Coincidence, Not By The Load',
         gh56_tests.test_gh56_r6b_busy_released_by_data_coincidence),
        ('GH56-R6-E(a) commit_timeout Survives Presetn',
         gh56_tests.test_gh56_r6e_commit_timeout_survives_presetn),
        ('GH56-R6-E(b) commit_timeout Cleared By rtc_resetn',
         gh56_tests.test_gh56_r6e_commit_timeout_cleared_by_rtc_resetn),
        ('GH56-R6-D Reset-Release Ordering Vs Clock-Select Reload',
         gh56_tests.test_gh56_r6d_reset_release_ordering_vs_clock_select_reload),
    ]

    # Full tests (full level only)
    full_test_methods = [
        ('Date Rollover', basic_tests.test_date_rollover),
        ('Alarm Matching', basic_tests.test_alarm_matching),
        ('RTC Stress Test', basic_tests.test_rtc_stress),
        # Enhanced calendar edge cases
        ('Leap Year Feb 29', basic_tests.test_leap_year_feb29),
        ('Century Leap Year', basic_tests.test_century_leap_year),
        ('Month Day Limits', basic_tests.test_month_day_limits),
        ('Year Rollover 99 to 00', basic_tests.test_year_rollover_99_to_00),
        # Enhanced alarm and interrupt tests
        ('Alarm All Fields Match', basic_tests.test_alarm_all_fields_match),
        ('Periodic Second Interrupt', basic_tests.test_periodic_second_interrupt),
        ('Binary Time Format', basic_tests.test_time_format_binary),
        ('Update In Progress', basic_tests.test_update_in_progress),
        # Rollover tests
        ('Minute Rollover', basic_tests.test_minute_rollover),
        ('Hour Rollover', basic_tests.test_hour_rollover),
        ('Day of Week', basic_tests.test_day_of_week),
        ('Alarm Interrupt Output', basic_tests.test_alarm_interrupt_output),
        ('Time Registers Readback', basic_tests.test_time_registers_readback),
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
        tb.log.info("\nAll RTC tests PASSED!")
    else:
        tb.log.error("\nSome RTC tests FAILED")
        assert False, f"RTC test failed: {passed_count}/{total_count} tests passed"


def generate_test_params():
    """Generate test parameter combinations for RTC configurations"""

    return [
        # (test_level, description)
        # RTC has no RTL parameters to vary, so test levels provide coverage
        ('gate', "RTC gate test"),
        ('func', "RTC func test"),
        ('full', "RTC full test"),
    ]


@pytest.mark.parametrize("test_level, description",
                        generate_test_params())
def test_rtc(request, test_level, description):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Test RTC with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb4_rtc"

    # Create human-readable test identifier
    test_name_plus_params = f"test_rtc_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/rtc/filelists/apb4_rtc.f'
    )

    # No RTL parameters for RTC (fixed configuration)
    rtl_parameters = {}

    # Clock periods: pclk fixed at 10ns. rtc_clk runs at a real, non-unity
    # 10:1 ratio (100ns) so cfg_clock_select=0 (production mode) actually
    # crosses a clock-domain boundary - see rtc_tb.py's
    # setup_clocks_and_reset() docstring and rtc_tests_medium.py's module
    # docstring (GitHub #56). Every existing test (rtc_tests_basic.py) runs
    # exclusively at cfg_clock_select=1 (selected_clk=pclk), which never
    # reads rtc_clk's period at all, so this is safe to apply at every
    # REG_LEVEL rather than needing a second sim build.
    apb_clock_period_ns = 10
    rtc_clock_period_ns = 100

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
        'TEST_APB_CLOCK_PERIOD': str(apb_clock_period_ns),
        'TEST_RTC_CLOCK_PERIOD': str(rtc_clock_period_ns),
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

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} RTC test: {description}")
    print(f"Configuration: Time-of-day tracking with alarm")
    print(f"{'='*80}")

    try:
        run(
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
            # Restrict this build to ONLY rtc_test. Without this, cocotb
            # discovers every @cocotb.test() in the module and would also
            # silently run rtc_gh56_timeout_sweep_test here, at this
            # build's DEFAULT COMMIT_TIMEOUT_CYCLES (65535) - the wrong
            # value for what that test sweeps, and it would waste ~250us
            # and add a spurious extra entry to cocotb's own TESTS=
            # tally on every gate/func/full run.
            testcase="rtc_test",
        )
        print(f"RTC test PASSED: {description}")

    except Exception as e:
        print(f"RTC test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for RTC:")
        print("- Check that pclk is running")
        print("- Verify reset sequence")
        print("- Check RTC enable bit")
        print("- Verify time register programming")
        print("- Check alarm configuration")
        raise


# ============================================================================
# GH#56 coordinator direction 2026-09-09 (fourth review round), test
# GH56-16: needs a SMALL COMMIT_TIMEOUT_CYCLES to sweep the "timeout meets
# link-idle" race in a practical number of cycles - the main rtc_test()
# above (and every other GH56 test in this file) depends on the DEFAULT
# 65535-cycle value, so this gets its OWN elaboration and its own
# @cocotb.test()/pytest pair rather than reusing the shared build. Same
# pattern GPIO uses for CDC_ENABLE (test_apb4_gpio.py) - an RTL parameter
# swept via a separate pytest-parametrized build, not a runtime knob.
# ============================================================================

GH56_16_COMMIT_TIMEOUT_CYCLES = 200


@cocotb.test(timeout_time=3000, timeout_unit="us")
async def rtc_gh56_timeout_sweep_test(dut):
    """Runs GH56-16 (test_gh56_busy_holds_when_timeout_meets_idle) plus the
    round-8/round-9 review's GH56-R8-1/R8-2/R8-3/R9-1/R9-2/R9-3/R8-4
    (queued-commit watchdog, various orderings and same-edge races), all
    under a build elaborated with a small COMMIT_TIMEOUT_CYCLES so
    watchdog-window waits stay cheap - see the module-level comment above
    and rtc_tests_medium.py's docstrings on these tests. Each needs at
    least one full watchdog window (R9-1/2/3 sweep ~8 pclk points, each
    a fresh reset), only practical at this build's small
    COMMIT_TIMEOUT_CYCLES value, so they share this build rather than the
    default-65535 main suite. timeout_time bumped
    600->1200->1800->3000us as sweep-based sub-tests were added."""
    tb = RTCTB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'RTC GH56-16/R8/R9 timeout-sweep test with seed: {seed}')

    await tb.setup_clocks_and_reset()
    await tb.setup_components()

    gh56_tests = RTCMediumTests(tb)

    results = {}

    async def _fresh_reset():
        await tb.assert_reset()
        await tb.wait_clocks('pclk', 10)
        await tb.deassert_reset()
        await tb.wait_clocks('pclk', RTCMediumTests.COMMIT_SETTLE_CYCLES)

    results['GH56-16'] = await gh56_tests.test_gh56_busy_holds_when_timeout_meets_idle()

    # Fresh reset between sub-tests sharing this build - same isolation
    # discipline used for the sequential test list in the main suite.
    await _fresh_reset()
    results['GH56-R8-1'] = await gh56_tests.test_gh56_r8_queued_retry_behind_dead_clock_times_out()

    await _fresh_reset()
    results['GH56-R8-2'] = await gh56_tests.test_gh56_r8_new_bytes_without_commit_not_delivered()

    await _fresh_reset()
    results['GH56-R8-3'] = await gh56_tests.test_gh56_r8_commit_queued_before_first_timeout_times_out()

    await _fresh_reset()
    results['GH56-R9-1'] = await gh56_tests.test_gh56_r9_1_new_commit_same_edge_as_pending_expiry()

    await _fresh_reset()
    results['GH56-R9-2'] = await gh56_tests.test_gh56_r9_2_accept_same_edge_as_pending_expiry()

    await _fresh_reset()
    results['GH56-R9-3'] = await gh56_tests.test_gh56_r9_3_resolve_not_transfer_identified()

    await _fresh_reset()
    results['GH56-R8-4'] = await gh56_tests.test_gh56_r8_4_report_retires_on_replacement_commit_landing()

    for name, ok in results.items():
        tb.log.info(f"{name}: {'PASSED' if ok else 'FAILED'}")

    failed = [name for name, ok in results.items() if not ok]
    assert not failed, f"Failed sub-test(s): {failed}"


def test_rtc_gh56_timeout_sweep(request):
    """Pytest wrapper for GH56-16 - separate build, small
    COMMIT_TIMEOUT_CYCLES (see the module-level comment above)."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb4_rtc"
    test_name_plus_params = "test_rtc_gh56_timeout_sweep"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/rtc/filelists/apb4_rtc.f'
    )

    commit_timeout_cycles = int(os.environ.get('TEST_COMMIT_TIMEOUT_CYCLES',
                                                 str(GH56_16_COMMIT_TIMEOUT_CYCLES)))
    rtl_parameters = {'COMMIT_TIMEOUT_CYCLES': str(commit_timeout_cycles)}

    apb_clock_period_ns = 10
    rtc_clock_period_ns = 100

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_APB_CLOCK_PERIOD': str(apb_clock_period_ns),
        'TEST_RTC_CLOCK_PERIOD': str(rtc_clock_period_ns),
        'TEST_COMMIT_TIMEOUT_CYCLES': str(commit_timeout_cycles),
    }

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

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

    print(f"\n{'='*80}")
    print(f"Running RTC GH56-16 timeout-sweep test (COMMIT_TIMEOUT_CYCLES={commit_timeout_cycles})")
    print(f"{'='*80}")

    try:
        run(
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
            # Restrict this build to ONLY its own cocotb test. Without this,
            # cocotb discovers and runs every @cocotb.test() in the module
            # (including the ~7ms main-suite rtc_test), which is wasteful
            # AND wrong here: rtc_test's medium/basic tests were designed
            # against the DEFAULT COMMIT_TIMEOUT_CYCLES (65535), not this
            # build's small override, so letting it run here gives it a
            # watchdog value it was never validated against.
            testcase="rtc_gh56_timeout_sweep_test",
        )
        print("RTC GH56-16 timeout-sweep test PASSED")

    except Exception as e:
        print("RTC GH56-16 timeout-sweep test FAILED")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple RTC test...")
    pytest.main([__file__, "-v", "-s"])
