# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_slave_wr_mon
# Purpose: AXI4 Slave Write Monitor Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Slave Write Monitor Integration Test

Thin wrapper that uses the reusable AXI4SlaveMonitorTB testbench class.
All test logic is in bin/CocoTBFramework/tbclasses/axi4/monitor/axi4_slave_monitor_tb.py
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.axi4.monitor.axi4_slave_monitor_tb import AXI4SlaveMonitorTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4_slave_wr_mon_test(dut):
    """AXI4 slave write monitor integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Create testbench (is_write=True for write slave)
    tb = AXI4SlaveMonitorTB(dut, is_write=True, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Run all integration tests
    await tb.run_integration_tests(test_level=test_level)


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4_slave_wr_mon_wavedrom_test(dut):
    """
    AXI4 slave write monitor WaveDrom timing diagram generation.

    Generates waveforms showing:
    - AW Channel: awvalid, awready, awid, awaddr, awlen
    - W Channel: wvalid, wready, wdata, wlast, wstrb
    - B Channel: bvalid, bready, bid, bresp
    - Monitor Bus: monbus_valid, monbus_ready
    """
    from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
    from CocoTBFramework.components.wavedrom.constraint_solver import (
        TemporalConstraintSolver, TemporalConstraint, TemporalEvent,
        SignalTransition, TemporalRelation
    )

    dut._log.info("=" * 80)
    dut._log.info("WaveDrom timing diagram generation for AXI4 slave write monitor.")
    dut._log.info("Enable with ENABLE_WAVEDROM=1 environment variable.")
    dut._log.info("=" * 80)

    # Create testbench
    tb = AXI4SlaveMonitorTB(dut, is_write=True, aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()

    # Setup WaveDrom with constraint solver (manual signal bindings)
    wave_generator = WaveJSONGenerator()
    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator
    )
    wave_solver.add_clock_group('default', dut.aclk)

    # Manually bind all AXI slave write channel signals (s_axi_* not m_axi_*)
    wave_solver.add_signal_binding('aclk', 'aclk')
    wave_solver.add_signal_binding('aresetn', 'aresetn')
    # AW channel
    wave_solver.add_signal_binding('s_axi_awvalid', 's_axi_awvalid')
    wave_solver.add_signal_binding('s_axi_awready', 's_axi_awready')
    wave_solver.add_signal_binding('s_axi_awid', 's_axi_awid')
    wave_solver.add_signal_binding('s_axi_awaddr', 's_axi_awaddr')
    wave_solver.add_signal_binding('s_axi_awlen', 's_axi_awlen')
    # W channel
    wave_solver.add_signal_binding('s_axi_wvalid', 's_axi_wvalid')
    wave_solver.add_signal_binding('s_axi_wready', 's_axi_wready')
    wave_solver.add_signal_binding('s_axi_wdata', 's_axi_wdata')
    wave_solver.add_signal_binding('s_axi_wlast', 's_axi_wlast')
    wave_solver.add_signal_binding('s_axi_wstrb', 's_axi_wstrb')
    # B channel
    wave_solver.add_signal_binding('s_axi_bvalid', 's_axi_bvalid')
    wave_solver.add_signal_binding('s_axi_bready', 's_axi_bready')
    wave_solver.add_signal_binding('s_axi_bid', 's_axi_bid')
    wave_solver.add_signal_binding('s_axi_bresp', 's_axi_bresp')
    # MonBus
    wave_solver.add_signal_binding('monbus_valid', 'monbus_valid')
    wave_solver.add_signal_binding('monbus_ready', 'monbus_ready')

    # Complete write transaction showing all channels together
    complete_signals = [
        'aclk', 'aresetn', '|',
        ['AW Channel', 's_axi_awvalid', 's_axi_awready', 's_axi_awid', 's_axi_awaddr', 's_axi_awlen'],
        '|',
        ['W Channel', 's_axi_wvalid', 's_axi_wready', 's_axi_wdata', 's_axi_wlast', 's_axi_wstrb'],
        '|',
        ['B Channel', 's_axi_bvalid', 's_axi_bready', 's_axi_bid', 's_axi_bresp'],
        '|',
        ['Monitor Bus', 'monbus_valid', 'monbus_ready']
    ]

    # Constraint 1: Single-beat write: AW handshake -> W data -> B response -> MonBus packet
    single_write_constraint = TemporalConstraint(
        name="single_beat_write",
        events=[
            TemporalEvent("aw_handshake", SignalTransition("s_axi_awvalid", 0, 1))
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=80,
        required=True,
        clock_group="default",
        signals_to_show=complete_signals,
        min_sequence_duration=1,
        max_sequence_duration=75
    )
    single_write_constraint.post_match_cycles = 20  # Capture through monbus packet
    single_write_constraint.skip_boundary_detection = True

    wave_solver.add_constraint(single_write_constraint)

    # Constraint 2: Second write transaction
    second_write_constraint = TemporalConstraint(
        name="single_beat_write_002",
        events=[
            TemporalEvent("aw_handshake_2", SignalTransition("s_axi_awvalid", 0, 1))
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=80,
        required=False,
        clock_group="default",
        signals_to_show=complete_signals,
        min_sequence_duration=1,
        max_sequence_duration=75
    )
    second_write_constraint.post_match_cycles = 20
    second_write_constraint.skip_boundary_detection = True

    wave_solver.add_constraint(second_write_constraint)

    dut._log.info(f"WaveDrom configured with {len(wave_solver.constraints)} AXI4 slave write constraints")

    # Get current sim time
    import cocotb
    start_time = cocotb.utils.get_sim_time('ns')
    dut._log.info(f"=== STARTING SAMPLING at {start_time}ns ===")

    # Start sampling BEFORE the transactions
    await wave_solver.start_sampling()

    # Scenario 1: Single-beat write transaction
    dut._log.info("=== Scenario 1: Single-Beat Write Transaction ===")
    success, info = await tb.base_tb.single_write_response_test(address=0x1000, data=0xDEADBEEF)
    if success:
        dut._log.info(f"✓ Single-beat write completed: address=0x1000, data=0xDEADBEEF")

    await tb.base_tb.wait_clocks('aclk', 30)

    # Scenario 2: Another single-beat write (different address)
    dut._log.info("=== Scenario 2: Single-Beat Write (address 0x2000) ===")
    success, info = await tb.base_tb.single_write_response_test(address=0x2000, data=0xCAFEBABE)
    if success:
        dut._log.info(f"✓ Single-beat write completed: address=0x2000, data=0xCAFEBABE")

    await tb.base_tb.wait_clocks('aclk', 30)

    # Stop sampling and generate waveforms
    await wave_solver.stop_sampling()

    await wave_solver.solve_and_generate()
    results = wave_solver.get_results()

    # Check results - MUST pass for regression testing
    dut._log.info("=" * 80)
    if not results['all_required_satisfied']:
        dut._log.error(f"❌ REQUIRED WAVEFORMS NOT GENERATED ❌")
        dut._log.error(f"Failed constraints: {results['failed_constraints']}")
        raise AssertionError(f"Required waveforms not generated: {results['failed_constraints']}")

    dut._log.info(f"✅ AXI4 Slave Write Monitor WaveDrom Complete: {len(results['solutions'])} waveforms generated")
    dut._log.info("=" * 80)


# ============================================================================
# PyTest Test Runner
# ============================================================================
@pytest.mark.parametrize("test_level", [
    "full",
])
def test_axi4_slave_wr_mon(test_level):
    """Integration test runner for AXI4 slave write monitor"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
    })

    dut_name = "axi4_slave_wr_mon"
    test_name = f"test_{dut_name}_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources
    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi4'], "axi4_slave_wr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict['rtl_axi4'], f"{dut_name}.sv"),
    ]

    # Check files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters
    rtl_parameters = {
        'AXI_ID_WIDTH': '8',
        'AXI_ADDR_WIDTH': '32',
        'AXI_DATA_WIDTH': '32',
        'AXI_USER_WIDTH': '1',
        'AXI_WSTRB_WIDTH': '4',
        'UNIT_ID': '1',
        'AGENT_ID': '21',
        'MAX_TRANSACTIONS': '16',
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AW': '2',
        'SKID_DEPTH_W': '4',
        'SKID_DEPTH_B': '2',
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_ID_WIDTH': '8',
        'TEST_ADDR_WIDTH': '32',
        'TEST_DATA_WIDTH': '32',
        'TEST_STUB': '0',  # Not stub - real RTL
        'SEED': str(random.randint(0, 100000)),
        'TEST_CLK_PERIOD': '10',
    }

    compile_args = [
        "-Wall", "-Wno-UNUSED", "-Wno-DECLFILENAME", "-Wno-PINMISSING",
        "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
    ]

    print(f"\n{'='*80}")
    print(f"AXI4 Slave Write Monitor Integration Test")
    print(f"Test Level: {test_level}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module="test_axi4_slave_wr_mon",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ PASSED: {test_name}")
    except Exception as e:
        print(f"✗ FAILED: {test_name}")
        print(f"Error: {str(e)}")
        raise
