# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBSlaveCDCTB
# Purpose: Enhanced APB-GAXI CDC testbench with comprehensive testing and debug capabilitie
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction, APBPacket
from CocoTBFramework.components.apb.apb_sequence import APBSequence
from CocoTBFramework.components.apb.apb_factories import create_apb4_master, create_apb4_monitor
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from CocoTBFramework.components.gaxi.gaxi_command_handler import GAXICommandHandler
from TBClasses.apb.apbgaxiconfig import APBGAXIConfig
from TBClasses.amba.apb4_slave_cdc_tb import APBSlaveCDCTB
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import (
    APB_MASTER_RANDOMIZER_CONFIGS,
    APB_SLAVE_RANDOMIZER_CONFIGS,
    AXI_RANDOMIZER_CONFIGS
)
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# WaveDrom support
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver,
    TemporalConstraint,
    TemporalEvent,
    SignalTransition,
    TemporalRelation
)
from TBClasses.wavedrom_user.apb import (
    get_apb_field_config,
    create_apb4_wavejson_generator,
    setup_apb_constraints_with_boundaries
)
from TBClasses.wavedrom_user.gaxi import (
    get_gaxi_field_config,
    create_gaxi_wavejson_generator
)




@cocotb.test(timeout_time=10, timeout_unit="sec")
async def apb4_slave_cdc_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for APB slave CDC.

    When enabled, would generate 7 comprehensive APB scenarios plus 3 CDC-specific scenarios:

    APB scenarios (using comprehensive preset):
    1. Basic write transaction
    2. Basic read transaction
    3. Back-to-back writes
    4. Back-to-back reads
    5. Write-to-read transition
    6. Read-to-write transition
    7. Error response (if supported)

    CDC-specific scenarios (custom constraints):
    8. Write CDC timing (APB domain → GAXI domain)
    9. Read CDC timing (GAXI domain → APB domain)
    10. Back-to-back CDC (showing async operation)

    All waveforms would include clock (both pclk and aclk) and reset signals.

    Enable with ENABLE_WAVEDROM=1 environment variable.

    NOTE: Multi-clock domain support is enabled in WaveDrom framework.
    This test generates waveforms showing both APB and GAXI domains with CDC timing.
    """
    # Setup testbench
    tb = APBSlaveCDCTB(dut)

    # Start both clocks for CDC (5:1 ratio for actual timing)
    await tb.start_clock('pclk', 10, 'ns')  # APB clock - 100MHz
    await tb.start_clock('aclk',  2, 'ns')  # AXI clock - 500MHz (5x faster, but will display as 2x with period=0.4)

    await tb.reset_dut()

    # Setup WaveDrom solver with BOTH APB and GAXI signals
    apb_field_config = get_apb_field_config(tb.ADDR_WIDTH, tb.DATA_WIDTH)
    gaxi_field_config = get_gaxi_field_config(tb.DATA_WIDTH)

    # Create generator that can handle both protocols
    wave_generator = create_apb4_wavejson_generator(apb_field_config)

    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=apb_field_config
    )

    # Add both clock groups (APB and AXI domains)
    # Use 'default' for APB domain as expected by comprehensive preset
    wave_solver.add_clock_group('default', dut.pclk)
    wave_solver.add_clock_group('axi_domain', dut.aclk)

    # WAVEDROM REQUIREMENT v1.2: ALL waveforms MUST include clock and reset
    # Bind APB slave signals (s_apb_* prefix) with clock and reset
    apb_signals = {
        'pclk': 'pclk',
        'presetn': 'presetn',
        'psel': 's_apb_PSEL',
        'penable': 's_apb_PENABLE',
        'pready': 's_apb_PREADY',
        'pwrite': 's_apb_PWRITE',
        'paddr': 's_apb_PADDR',
        'pwdata': 's_apb_PWDATA',
        'prdata': 's_apb_PRDATA',
        'pstrb': 's_apb_PSTRB',
        'pprot': 's_apb_PPROT',
        'pslverr': 's_apb_PSLVERR'
    }
    wave_solver.add_interface("apb", apb_signals, field_config=apb_field_config)

    # Bind CMD/RSP signals for CDC visualization
    # Note: The apb4_slave_cdc module uses cmd_*/rsp_* naming (not gaxi_cmd_*)
    cmd_signals = {
        'aclk': 'aclk',
        'aresetn': 'aresetn',
        'valid': 'cmd_valid',
        'ready': 'cmd_ready',
        'pwrite': 'cmd_pwrite',
        'paddr': 'cmd_paddr',
        'pwdata': 'cmd_pwdata'
    }
    wave_solver.add_interface("cmd", cmd_signals, field_config=gaxi_field_config)

    rsp_signals = {
        'valid': 'rsp_valid',
        'ready': 'rsp_ready',
        'prdata': 'rsp_prdata',
        'pslverr': 'rsp_pslverr'
    }
    wave_solver.add_interface("rsp", rsp_signals, field_config=gaxi_field_config)

    # Create CDC-aware signal list (APB + CMD + RSP interfaces)
    cdc_signals_to_show = [
        'apb_pclk', 'cmd_aclk', '|',  # Both clocks (period will be added post-generation)
        'apb_presetn', 'cmd_aresetn', '|',  # Both resets
        ['APB', 'apb_psel', 'apb_penable', 'apb_pready', 'apb_pwrite', 'apb_paddr', 'apb_pwdata', 'apb_prdata', 'apb_pslverr'], '|',
        ['CMD', 'cmd_valid', 'cmd_ready', 'cmd_pwrite', 'cmd_paddr', 'cmd_pwdata'], '|',
        ['RSP', 'rsp_valid', 'rsp_ready', 'rsp_prdata', 'rsp_pslverr']
    ]

    # Clock period configuration for VISUAL 1:2 ratio (pclk:aclk)
    # Actual hardware is 5:1 (10ns:2ns), but we display as 1:2 for readability
    # This will be applied to generated WaveJSON to make aclk visually compact
    clock_periods = {
        'apb_pclk': 1.0,   # Base period (full width)
        'cmd_aclk': 0.4    # 40% period (visually compact, appears ~2x faster)
    }

    # Manually create comprehensive constraints with CDC-aware signal lists
    from TBClasses.wavedrom_user.apb import (
        create_apb4_write_sequence_constraint,
        create_apb4_read_sequence_constraint,
        APBConstraints
    )

    # 1. Basic write - with CDC signals
    constraint_write = create_apb4_write_sequence_constraint(
        max_window=50, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_write.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_write)

    # 2. Basic read - with CDC signals
    constraint_read = create_apb4_read_sequence_constraint(
        max_window=50, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_read.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_read)

    # 3. Back-to-back writes - with CDC signals
    constraint_b2b_wr = APBConstraints.back_to_back_writes(
        max_cycles=60, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_b2b_wr.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_b2b_wr)

    # 4. Back-to-back reads - with CDC signals
    constraint_b2b_rd = APBConstraints.back_to_back_reads(
        max_cycles=60, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_b2b_rd.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_b2b_rd)

    # 5. Write-to-read - with CDC signals
    constraint_wr2rd = APBConstraints.write_to_read(
        max_cycles=60, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_wr2rd.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_wr2rd)

    # 6. Read-to-write - with CDC signals
    constraint_rd2wr = APBConstraints.read_to_write(
        max_cycles=60, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_rd2wr.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_rd2wr)

    # 7. Error - with CDC signals (optional)
    constraint_err = APBConstraints.error_transaction(
        max_cycles=50, required=False, clock_group="default",
        field_config=apb_field_config
    )
    constraint_err.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_err)

    dut._log.info(f"WaveDrom configured with 7 CDC-aware APB constraints (APB + CMD + RSP interfaces)")

    # Start command handler
    await tb.cmd_handler.start()

    # Start sampling for all scenarios
    await wave_solver.start_sampling()

    # Generate all 7 APB transaction scenarios (comprehensive preset)
    dut._log.info("=== Generating All APB Slave CDC WaveDrom Scenarios ===")

    # Scenarios 1-2: Basic write and read
    dut._log.info("Generating: Basic write and read with CDC")
    await tb.send_apb_transaction(is_write=True, addr=0x1000, data=0xDEADBEEF)
    await tb.wait_clocks('pclk', 10)  # Extra time for CDC
    await tb.send_apb_transaction(is_write=False, addr=0x1000)
    await tb.wait_clocks('pclk', 10)

    # Scenario 3: Back-to-back writes
    dut._log.info("Generating: Back-to-back writes with CDC")
    await tb.send_apb_transaction(is_write=True, addr=0x2000, data=0xAAAAAAAA)
    await tb.send_apb_transaction(is_write=True, addr=0x2004, data=0xBBBBBBBB)
    await tb.wait_clocks('pclk', 10)

    # Scenario 4: Back-to-back reads
    dut._log.info("Generating: Back-to-back reads with CDC")
    await tb.send_apb_transaction(is_write=False, addr=0x3000)
    await tb.send_apb_transaction(is_write=False, addr=0x3004)
    await tb.wait_clocks('pclk', 10)

    # Scenario 5: Write-to-read transition
    dut._log.info("Generating: Write-to-read transition with CDC")
    await tb.send_apb_transaction(is_write=True, addr=0x4000, data=0x12345678)
    await tb.send_apb_transaction(is_write=False, addr=0x4000)
    await tb.wait_clocks('pclk', 10)

    # Scenario 6: Read-to-write transition
    dut._log.info("Generating: Read-to-write transition with CDC")
    await tb.send_apb_transaction(is_write=False, addr=0x5000)
    await tb.send_apb_transaction(is_write=True, addr=0x5000, data=0x87654321)
    await tb.wait_clocks('pclk', 10)

    # Scenario 7: Error transaction (if supported by slave)
    dut._log.info("Generating: Error scenario (if slave supports)")
    await tb.wait_clocks('pclk', 5)

    # Stop sampling and generate all waveforms
    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    results = wave_solver.get_results()

    # Post-process WaveJSON files to add period attributes for visual 1:2 clock ratio
    import json
    import os
    import glob

    # WaveJSON files are written to current directory (where cocotb test runs)
    sim_build = os.getcwd()

    # Find all generated JSON files
    json_files = glob.glob(os.path.join(sim_build, "apb_*.json"))
    dut._log.info(f"Searching in: {sim_build}")
    dut._log.info(f"Found {len(json_files)} waveform JSON files to post-process")

    for json_file in json_files:
        try:
            with open(json_file, 'r') as f:
                wavejson = json.load(f)

            # Add period attribute to clock signals for visual 1:2 ratio display
            modified = False
            for sig in wavejson.get('signal', []):
                if isinstance(sig, dict) and sig.get('name') in clock_periods:
                    sig['period'] = clock_periods[sig['name']]
                    modified = True

            if modified:
                # Write back updated WaveJSON
                with open(json_file, 'w') as f:
                    json.dump(wavejson, f, indent=2)

                dut._log.info(f"✓ Added clock periods to {os.path.basename(json_file)}")
        except Exception as e:
            dut._log.warning(f"Could not update {os.path.basename(json_file)}: {e}")

    # Check if all required waveforms were generated
    if not results['all_required_satisfied']:
        dut._log.error(f"❌ NOT ALL REQUIRED WAVEFORMS GENERATED ❌")
        dut._log.error(f"Failed constraints: {results['failed_constraints']}")
        raise AssertionError(f"Required waveforms not generated: {results['failed_constraints']}")

    # Cleanup
    tb.done = True
    await tb.cmd_handler.stop()
    await tb.wait_clocks('pclk', 10)

    dut._log.info("=" * 80)
    dut._log.info(f"✅ APB Slave CDC WaveDrom Complete: {len(results['solutions'])} scenarios generated")
    dut._log.info("   Clock ratio: pclk (period=1.0) : aclk (period=0.5) = 1:2")
    dut._log.info("=" * 80)


@cocotb.test(timeout_time=60, timeout_unit="ms")  # Longer timeout for CDC tests
async def comprehensive_apb_cdc_test(dut):
    """Comprehensive APB-GAXI CDC test with cross-domain validation."""

    tb = APBSlaveCDCTB(dut)

    # Set seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using CDC test seed: {seed}")

    # Start both clocks for CDC testing
    await tb.start_clock('aclk',  1, 'ns')  # Fast AXI clock - 1GHz
    await tb.start_clock('pclk', 10, 'ns')  # Slower APB clock - 100MHz

    # Reset DUT with CDC-specific reset sequence
    await tb.reset_dut()

    # Start command handler
    await tb.cmd_handler.start()

    try:
        # First run the basic CDC comprehensive test
        result = await tb.run_cdc_comprehensive_test()

        if result:
            tb.log.info("🎉 APB-GAXI CDC BASIC TEST PASSED! 🎉")
        else:
            tb.log.error("❌ APB-GAXI CDC BASIC TEST FAILED ❌")
            tb.log.error("Check the detailed CDC analysis above to identify cross-domain issues")
            assert False, "APB-GAXI CDC basic test failed"

        # Run comprehensive test suite
        await tb.run_comprehensive_cdc_test_suite()

        # Final verification with CDC timing
        final_result = await tb.verify_scoreboard(timeout=5000)

        if final_result and tb.test_stats['failed_tests'] == 0:
            tb.log.info("🎉 COMPREHENSIVE CDC TEST SUITE PASSED! 🎉")
        else:
            tb.log.error("❌ COMPREHENSIVE CDC TEST SUITE FAILED ❌")
            assert False, f"CDC test suite failed: {tb.test_stats['failed_tests']} failed tests"

    finally:
        # Clean shutdown
        tb.done = True
        await tb.cmd_handler.stop()
        # Final CDC synchronization wait
        await tb.wait_clocks('aclk', 20)
        await tb.wait_clocks('pclk', 20)


@pytest.mark.parametrize("addr_width, data_width, depth", [(32, 32, 2)])
def test_apb4_slave_cdc_robust(request, addr_width, data_width, depth):
    """Robust APB-GAXI CDC test with comprehensive validation."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_amba': 'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_apb':  'rtl/amba/apb4',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb4_slave_cdc"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb4_slave_cdc.f")

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth"]
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(42),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend([])


    sim_args = [
        "--trace",
        
        "--trace-depth", "99",
    ]

    plus_args = ["--trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )

        print(f"✓ APB-GAXI CDC robust test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")

    except Exception as e:
        print(f"❌ APB-GAXI CDC robust test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed CDC analysis.")
        raise


# ===============================================================================
# WaveDrom Test
# ===============================================================================

def generate_apb4_slave_cdc_wavedrom_params():
    """Generate test parameters for APB slave CDC WaveDrom test."""
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Robust APB-GAXI CDC test with comprehensive validation."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_amba': 'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_apb':  'rtl/amba/apb4',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb4_slave_cdc"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb4_slave_cdc.f")

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth"]
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(42),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend([])


    sim_args = [
        "--trace",
        
        "--trace-depth", "99",
    ]

    plus_args = ["--trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )

        print(f"✓ APB-GAXI CDC robust test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")

    except Exception as e:
        print(f"❌ APB-GAXI CDC robust test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed CDC analysis.")
        raise


# ===============================================================================
# WaveDrom Test
# ===============================================================================

def generate_apb4_slave_cdc_wavedrom_params():
    """Generate test parameters for APB slave CDC WaveDrom test."""
    return [
        # (addr_width, data_width, rsp_depth, cmd_depth)
        (32, 32, 2, 2),  # Standard CDC configuration
    ]


wavedrom_params = generate_apb4_slave_cdc_wavedrom_params()


@pytest.mark.parametrize("addr_width, data_width, rsp_depth, cmd_depth", wavedrom_params)
def test_apb4_slave_cdc_wavedrom(request, addr_width, data_width, rsp_depth, cmd_depth):
    """
    APB slave CDC WaveDrom test - generates timing diagrams with APB and CMD/RSP interfaces.

    Run with: ENABLE_WAVEDROM=1 pytest val/amba/test_apb4_slave_cdc.py::test_apb4_slave_cdc_wavedrom -v
    """
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_amba': 'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_apb':  'rtl/amba/apb4',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb4_slave_cdc"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb4_slave_cdc.f")

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    rd_str = TBBase.format_dec(rsp_depth, 3)
    cd_str = TBBase.format_dec(cmd_depth, 3)
    test_name_plus_params = f"test_{worker_id}_apb4_slave_cdc_aw{aw_str}_dw{dw_str}_rd{rd_str}_cd{cd_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'DEPTH': rsp_depth,  # apb4_slave_cdc uses single DEPTH parameter
    }

    extra_env = {
        'ENABLE_WAVEDROM': '1',  # ← Enable WaveDrom!
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_RSP_DEPTH': str(rsp_depth),
        'TEST_CMD_DEPTH': str(cmd_depth),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend([])


    sim_args = []

    plus_args = []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            testcase="apb4_slave_cdc_wavedrom_test",  # ← Run wavedrom test specifically!
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,  # Disable FST - using WaveDrom instead
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )

        print(f"✓ APB Slave CDC WaveDrom test completed!")
        print(f"Logs: {log_path}")
        print(f"WaveJSON files: val/amba/WaveJSON/test_apb4_slave_cdc_*.json")
        print(f"Note: Waveforms show BOTH APB and CMD/RSP (GAXI) interfaces across clock domains")

    except Exception as e:
        print(f"❌ APB Slave CDC WaveDrom test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        raise
