# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_buffer_multi_sigmap
# Purpose: Test suite for Gaxi Buffer Multi Sigmap
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_multi_sigmap import GaxiMultiSigMapBufferTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def skid_buffer_multi_sigmap_test(dut):
    '''Test the axi_skid_buffer_multi component with proper result checking'''
    tb = GaxiMultiSigMapBufferTB(dut, wr_clk=dut.axi_aclk, wr_rstn=dut.axi_aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    await tb.start_clock('axi_aclk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('axi_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('axi_aclk', 5)

    tb.log.info("Starting test with verification checking...")

    try:
        # Run legacy test for backward compatibility - CHECK RESULT
        tb.log.info("Running legacy simple_incremental_loops test...")
        result = await tb.simple_incremental_loops(count=10, delay_key='fixed', delay_clks_after=20)
        if not result:
            raise AssertionError("❌ Simple incremental loops test FAILED verification")
        tb.log.info("✅ Simple incremental loops test PASSED")

        # Run basic sequence test - CHECK RESULT
        tb.log.info("Running basic sequence test...")
        result = await tb.run_sequence_test(tb.basic_sequence, delay_key='fixed', delay_clks_after=5)
        if not result:
            raise AssertionError("❌ Basic sequence test FAILED verification")
        tb.log.info("✅ Basic sequence test PASSED")

        # Run walking ones pattern test - CHECK RESULT
        tb.log.info("Running walking ones pattern test...")
        result = await tb.run_sequence_test(tb.walking_ones_sequence, delay_key='constrained', delay_clks_after=5)
        if not result:
            raise AssertionError("❌ Walking ones pattern test FAILED verification")
        tb.log.info("✅ Walking ones pattern test PASSED")

        # Run alternating patterns test - CHECK RESULT
        tb.log.info("Running alternating patterns test...")
        result = await tb.run_sequence_test(tb.alternating_sequence, delay_key='fast', delay_clks_after=5)
        if not result:
            raise AssertionError("❌ Alternating patterns test FAILED verification")
        tb.log.info("✅ Alternating patterns test PASSED")

        # Run burst sequence test with back-to-back packets - CHECK RESULT
        tb.log.info("Running burst sequence test...")
        result = await tb.run_sequence_test(tb.burst_sequence, delay_key='backtoback', delay_clks_after=5)
        if not result:
            raise AssertionError("❌ Burst sequence test FAILED verification")
        tb.log.info("✅ Burst sequence test PASSED")

        # Run random data test - CHECK RESULT
        tb.log.info("Running random data test...")
        result = await tb.run_sequence_test(tb.random_sequence, delay_key='constrained', delay_clks_after=5)
        if not result:
            raise AssertionError("❌ Random data test FAILED verification")
        tb.log.info("✅ Random data test PASSED")

        # Run comprehensive test - CHECK RESULT
        tb.log.info("Running comprehensive test...")
        result = await tb.run_sequence_test(tb.comprehensive_sequence, delay_key='constrained', delay_clks_after=10)
        if not result:
            raise AssertionError("❌ Comprehensive test FAILED verification")
        tb.log.info("✅ Comprehensive test PASSED")

        # Run stress test with varied delays and patterns - CHECK RESULT
        tb.log.info("Running stress test...")
        result = await tb.run_sequence_test(tb.stress_sequence, delay_key='burst_pause', delay_clks_after=20)
        if not result:
            raise AssertionError("❌ Stress test FAILED verification")
        tb.log.info("✅ Stress test PASSED")

        # Test with different randomizer configurations
        tb.log.info("Testing with different randomizer configurations...")

        # Test with slow consumer - CHECK RESULT
        tb.log.info("Testing with slow consumer...")
        result = await tb.run_sequence_test(tb.basic_sequence, delay_key='slow_consumer', delay_clks_after=20)
        if not result:
            raise AssertionError("❌ Slow consumer test FAILED verification")
        tb.log.info("✅ Slow consumer test PASSED")

        # Test with slow producer - CHECK RESULT
        tb.log.info("Testing with slow producer...")
        result = await tb.run_sequence_test(tb.basic_sequence, delay_key='slow_producer', delay_clks_after=20)
        if not result:
            raise AssertionError("❌ Slow producer test FAILED verification")
        tb.log.info("✅ Slow producer test PASSED")

        # Final verification check - ensure no accumulated errors
        final_stats = tb.get_statistics()
        total_errors = final_stats.get('total_errors', 0)
        verification_errors = final_stats.get('verification_errors', 0)

        if total_errors > 0:
            tb.log.error(f"❌ FINAL CHECK FAILED: {total_errors} total errors detected")
            tb.log.error(f"   Verification errors: {verification_errors}")
            tb.log.error(f"   Final statistics: {final_stats}")
            raise AssertionError(f"❌ TEST SUITE FAILED: {total_errors} total errors, {verification_errors} verification errors")

        if final_stats.get('total_sent', 0) != final_stats.get('total_received', 0):
            sent = final_stats.get('total_sent', 0)
            received = final_stats.get('total_received', 0)
            tb.log.error(f"❌ PACKET COUNT MISMATCH: sent={sent}, received={received}")
            raise AssertionError(f"❌ Packet count mismatch: sent={sent}, received={received}")

        # Success summary
        tb.log.info("🎉 ALL TESTS COMPLETED SUCCESSFULLY! 🎉")
        tb.log.info(f"✅ Total packets verified: {final_stats.get('total_received', 0)}")
        tb.log.info(f"✅ Zero errors detected")
        tb.log.info(f"✅ All sequence tests passed verification")

    except AssertionError as e:
        # Re-raise assertion errors (test failures)
        tb.log.error(f"🚨 TEST FAILED: {e}")
        raise

    except Exception as e:
        # Handle unexpected errors
        tb.log.error(f"🚨 UNEXPECTED ERROR: {e}")

        # Get debug statistics
        try:
            debug_stats = tb.get_statistics()
            tb.log.error(f"Debug statistics: {debug_stats}")
        except:
            tb.log.error("Could not retrieve debug statistics")

        # Re-raise as test failure
        raise AssertionError(f"❌ Unexpected error during test: {e}")


def generate_params():
    addr_widths = [4, 6, 8]
    ctrl_widths = [3, 5, 7]
    data_widths = [8]
    depths = [2]
    modes = ['skid']

    return [(6, 3, 8, 2, 'skid')]
    # return list(product(addr_widths, ctrl_widths, data_widths, depths, modes))

params = generate_params()

@pytest.mark.parametrize("addr_width, ctrl_width, data_width, depth, mode", params)
def test_axi_skid_buffer_multi_sigmap(request, addr_width, ctrl_width, data_width, depth, mode):
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn':       'rtl/common',
            'rtl_amba':      'rtl/amba',
            'rtl_gaxi':      'rtl/amba/gaxi',
            'rtl_amba_test': 'rtl/amba/testcode',
            'rtl_amba_includes': 'rtl/amba/includes',
        })

    # Set up all of the test names
    dut_name = "gaxi_skid_buffer_multi_sigmap"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'],       "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba_test'], f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    cw_str = TBBase.format_dec(ctrl_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_{mode}_aw{aw_str}_cw{cw_str}_dw{dw_str}_d{d_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes=[rtl_dict['rtl_amba_includes']]

    # RTL parameters
    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'CTRL_WIDTH': str(ctrl_width),
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        # 'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add test parameters
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_CTRL_WIDTH'] = str(ctrl_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_MODE'] = 'skid'  # Always 'skid' mode for skid buffer

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace",  # Tell Verilator to use VCD
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
