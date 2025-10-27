# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_buffer_field
# Purpose: Generate comprehensive field-based parameter combinations
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
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_field import GaxiFieldBufferTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def skid_buffer_field_test(dut):
    '''Test the gaxi_fifo_sync_field component'''
    tb = GaxiFieldBufferTB(dut, wr_clk=dut.axi_aclk, wr_rstn=dut.axi_aresetn)

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

    tb.log.info("Starting test...")

    # Run legacy test for backward compatibility
    tb.log.info("Running legacy simple_incremental_loops test...")
    await tb.simple_incremental_loops(count=10, delay_key='fixed', delay_clks_after=20)

    # Run basic sequence test
    tb.log.info("Running basic sequence test...")
    await tb.run_sequence_test(tb.basic_sequence, delay_key='fixed', delay_clks_after=5)

    # Run walking ones pattern test
    tb.log.info("Running walking ones pattern test...")
    await tb.run_sequence_test(tb.walking_ones_sequence, delay_key='constrained', delay_clks_after=5)

    # Run alternating patterns test
    tb.log.info("Running alternating patterns test...")
    await tb.run_sequence_test(tb.alternating_sequence, delay_key='fast', delay_clks_after=5)

    # Run burst sequence test with back-to-back packets
    tb.log.info("Running burst sequence test...")
    await tb.run_sequence_test(tb.burst_sequence, delay_key='backtoback', delay_clks_after=5)

    # Run random data test
    tb.log.info("Running random data test...")
    await tb.run_sequence_test(tb.random_sequence, delay_key='constrained', delay_clks_after=5)

    # Run comprehensive test
    tb.log.info("Running comprehensive test...")
    await tb.run_sequence_test(tb.comprehensive_sequence, delay_key='constrained', delay_clks_after=10)

    # Run stress test with varied delays and patterns
    tb.log.info("Running stress test...")
    await tb.run_sequence_test(tb.stress_sequence, delay_key='burst_pause', delay_clks_after=20)

    # Test with different randomizer configurations
    tb.log.info("Testing with different randomizer configurations...")

    # Test with slow consumer
    tb.log.info("Testing with slow consumer...")
    await tb.run_sequence_test(tb.basic_sequence, delay_key='slow_consumer', delay_clks_after=20)

    # Test with slow producer
    tb.log.info("Testing with slow producer...")
    await tb.run_sequence_test(tb.basic_sequence, delay_key='slow_producer', delay_clks_after=20)

    tb.log.info("All tests completed successfully!")


def generate_field_params():
    """Generate comprehensive field-based parameter combinations"""
    addr_widths = [4, 6, 8, 12]
    ctrl_widths = [3, 4, 5, 6]  
    data_widths = [8, 16, 24, 32]
    depths = [2, 4, 6, 8]
    modes = ['skid', 'fifo_mux', 'fifo_flop']
    test_levels = ['full'] # ['basic', 'medium', 'full']
    
    # For debugging/quick testing, return a smaller subset:
    debug_mode = True
    if debug_mode:
        return [
            ( 4, 3,  8, 2, 'skid',      'full'),
            ( 8, 5, 16, 4, 'fifo_mux',  'full'),
            (12, 6,  8, 4, 'fifo_flop', 'full'),
        ]
    
    # Full parameter sweep for comprehensive testing:
    return list(product(addr_widths, ctrl_widths, data_widths, depths, modes, test_levels))


@pytest.mark.parametrize("addr_width, ctrl_width, data_width, depth, mode, test_level", generate_field_params())
def test_gaxi_buffer_field(request, addr_width, ctrl_width, data_width, depth, mode, test_level):
    """Test GAXI buffer in field-only mode"""
    
    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    # Set up test names and directories  
    dut_name = "gaxi_skid_buffer" if mode == 'skid' else "gaxi_fifo_sync"
    aw_str = TBBase.format_dec(addr_width, 2)
    cw_str = TBBase.format_dec(ctrl_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    d_str = TBBase.format_dec(depth, 2)
    
    test_name_plus_params = f"test_gaxi_field_only_{mode}_a{aw_str}_c{cw_str}_d{dw_str}_dep{d_str}_{test_level}"
    
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources based on mode (NON-STRUCT VERSIONS)
    if mode == 'skid':
        verilog_sources = [os.path.join(rtl_dict['rtl_gaxi'], f"{dut_name}.sv")]
    else:
        verilog_sources = [
            os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
            os.path.join(rtl_dict['rtl_gaxi'], f"{dut_name}.sv"),
        ]

    # RTL parameters
    total_width = addr_width + ctrl_width + data_width + data_width
    rtl_parameters = {
        'DATA_WIDTH': str(total_width),
        'DEPTH': str(depth),
        'INSTANCE_NAME': f'"FIELD_{mode.upper()}_{test_level.upper()}"',
    }
    if 'fifo' in mode:
        rtl_parameters['REGISTERED'] = str(1) if mode == 'fifo_flop' else str(0)

    # Calculate timeout based on field complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    field_complexity = (addr_width + ctrl_width + data_width) / 30.0  # Normalize complexity
    timeout_ms = int(2500 * timeout_multipliers.get(test_level, 1) * max(1.0, field_complexity))

    # Environment variables - FIELD-ONLY MODE (explicitly no struct variables)
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        
        # Field mode parameters
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_CTRL_WIDTH': str(ctrl_width), 
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_MODE': mode,
        'TEST_KIND': 'field_only',
        
        # Explicitly ensure no struct variables are set
        'TEST_STRUCT_NAME': '',  # Empty to ensure field mode
        'TEST_TYPEDEF_NAME': '',
        'TEST_STRUCT_FILE': '',
        'TEST_STRUCT_HELPERS': '',
        'TEST_STRUCT_CONTENT': '',
    }

    # Simulation settings
    includes=[sim_build, rtl_dict['rtl_amba_includes']]
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99", "-Wall", "-Wno-UNUSED", "-Wno-DECLFILENAME", "-Wno-SYNCASYNCNET"]
    sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    plusargs = ["--trace"]

    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} FIELD-ONLY test: {dut_name}")
    print(f"Fields: addr({addr_width}), ctrl({ctrl_width}), data({data_width}), depth({depth})")
    print(f"Mode: {mode}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
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
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} FIELD-ONLY test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} FIELD-ONLY test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Quick validation of field parameters
    field_params = generate_field_params()
    print(f"Field-only test runner configured with {len(field_params)} parameter combinations")
    for i, params in enumerate(field_params[:5]):  # Show first 5
        addr_w, ctrl_w, data_w, depth, mode, level = params
        total_width = addr_w + ctrl_w + data_w + data_w
        print(f"  {i+1}: addr={addr_w}, ctrl={ctrl_w}, data={data_w}, depth={depth}, mode={mode}, level={level} (total_width={total_width})")
    if len(field_params) > 5:
        print(f"  ... and {len(field_params) - 5} more combinations")
