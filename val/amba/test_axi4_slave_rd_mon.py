# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_slave_rd_mon
# Purpose: AXI4 Slave Read Monitor Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Slave Read Monitor Integration Test

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


def validate_addr_width(addr_width):
    """
    Validate address width meets AXI4 specification constraints.

    Args:
        addr_width: Address width value (int or str)

    Raises:
        ValueError: If address width exceeds 64-bits
    """
    addr_w = int(addr_width)
    if addr_w > 64:
        raise ValueError(
            f"Invalid AXI4 configuration: AXI_ADDR_WIDTH={addr_w} exceeds maximum of 64-bits. "
            f"AXI4 specification limits address width to 64-bits."
        )


def generate_axi4_monitor_params():
    """
    Generate AXI4 monitor parameter combinations based on REG_LEVEL.

    Parameter tuple: (id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level)

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test
        FUNC: 3 tests - Functional validation with variations
        FULL: 9 tests - Comprehensive testing

    Returns:
        list: Parameter tuples for pytest.mark.parametrize

    Raises:
        ValueError: If generated parameters violate AXI4 constraints
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Quick smoke test - basic configuration
        params = [
            (8, 32, 32, 1, 16, 2, 4, 'basic'),
        ]

    elif reg_level == 'FUNC':
        # Functional validation - variations in depth and test_level
        params = [
            (8, 32, 32, 1, 16, 2, 4, 'basic'),   # Standard config
            (8, 32, 32, 1, 16, 4, 8, 'medium'),  # Deeper skid buffers
            (8, 32, 32, 1, 32, 2, 4, 'medium'),  # More transactions
        ]

    else:  # FULL
        # Comprehensive testing - all test_levels × configurations
        test_levels = ['basic', 'medium', 'full']
        configs = [
            (8, 32, 32, 1, 16, 2, 4),  # Standard
            (8, 32, 32, 1, 16, 4, 8),  # Deep skid
            (8, 32, 32, 1, 32, 2, 4),  # Many transactions
        ]
        params = [
            (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r, level)
            for (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r) in configs
            for level in test_levels
        ]

    # Validate all parameters
    for param in params:
        _, addr_w, _, _, _, _, _, _ = param
        if addr_w > 64:
            raise ValueError(
                f"Invalid AXI4 configuration: addr_width={addr_w} exceeds maximum of 64-bits. "
                f"Full parameter set: {param}"
            )

    return params


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4_slave_rd_mon_test(dut):
    """AXI4 slave read monitor integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Create testbench (is_write=False for read slave)
    tb = AXI4SlaveMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Run all integration tests
    await tb.run_integration_tests(test_level=test_level)


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4_slave_rd_mon_wavedrom_test(dut):
    """
    AXI4 slave read monitor WaveDrom timing diagram generation.

    Generates waveforms showing:
    - AR Channel: arvalid, arready, arid, araddr, arlen
    - R Channel: rvalid, rready, rid, rdata, rlast, rresp
    - Monitor Bus: monbus_valid, monbus_ready
    """
    from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
    from CocoTBFramework.components.wavedrom.constraint_solver import (
        TemporalConstraintSolver, TemporalConstraint, TemporalEvent,
        SignalTransition, TemporalRelation
    )

    dut._log.info("=" * 80)
    dut._log.info("WaveDrom timing diagram generation for AXI4 slave read monitor.")
    dut._log.info("Enable with ENABLE_WAVEDROM=1 environment variable.")
    dut._log.info("=" * 80)

    # Create testbench
    tb = AXI4SlaveMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()

    # Setup WaveDrom with constraint solver (manual signal bindings)
    wave_generator = WaveJSONGenerator()
    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator
    )
    wave_solver.add_clock_group('default', dut.aclk)

    # Manually bind all AXI slave read channel signals (s_axi_* not m_axi_*)
    wave_solver.add_signal_binding('aclk', 'aclk')
    wave_solver.add_signal_binding('aresetn', 'aresetn')
    # AR channel
    wave_solver.add_signal_binding('s_axi_arvalid', 's_axi_arvalid')
    wave_solver.add_signal_binding('s_axi_arready', 's_axi_arready')
    wave_solver.add_signal_binding('s_axi_arid', 's_axi_arid')
    wave_solver.add_signal_binding('s_axi_araddr', 's_axi_araddr')
    wave_solver.add_signal_binding('s_axi_arlen', 's_axi_arlen')
    # R channel
    wave_solver.add_signal_binding('s_axi_rvalid', 's_axi_rvalid')
    wave_solver.add_signal_binding('s_axi_rready', 's_axi_rready')
    wave_solver.add_signal_binding('s_axi_rid', 's_axi_rid')
    wave_solver.add_signal_binding('s_axi_rdata', 's_axi_rdata')
    wave_solver.add_signal_binding('s_axi_rlast', 's_axi_rlast')
    wave_solver.add_signal_binding('s_axi_rresp', 's_axi_rresp')
    # MonBus
    wave_solver.add_signal_binding('monbus_valid', 'monbus_valid')
    wave_solver.add_signal_binding('monbus_ready', 'monbus_ready')

    # Complete read transaction showing all channels together
    complete_signals = [
        'aclk', 'aresetn', '|',
        ['AR Channel', 's_axi_arvalid', 's_axi_arready', 's_axi_arid', 's_axi_araddr', 's_axi_arlen'],
        '|',
        ['R Channel', 's_axi_rvalid', 's_axi_rready', 's_axi_rid', 's_axi_rdata', 's_axi_rlast', 's_axi_rresp'],
        '|',
        ['Monitor Bus', 'monbus_valid', 'monbus_ready']
    ]

    # Constraint 1: Single-beat read: AR handshake -> R response -> MonBus packet
    single_read_constraint = TemporalConstraint(
        name="single_beat_read",
        events=[
            TemporalEvent("ar_handshake", SignalTransition("s_axi_arvalid", 0, 1))
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=80,
        required=True,
        clock_group="default",
        signals_to_show=complete_signals,
        min_sequence_duration=1,
        max_sequence_duration=75
    )
    single_read_constraint.post_match_cycles = 20  # Capture through monbus packet
    single_read_constraint.skip_boundary_detection = True

    wave_solver.add_constraint(single_read_constraint)

    # Constraint 2: Second read transaction
    second_read_constraint = TemporalConstraint(
        name="single_beat_read_002",
        events=[
            TemporalEvent("ar_handshake_2", SignalTransition("s_axi_arvalid", 0, 1))
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=80,
        required=False,
        clock_group="default",
        signals_to_show=complete_signals,
        min_sequence_duration=1,
        max_sequence_duration=75
    )
    second_read_constraint.post_match_cycles = 20
    second_read_constraint.skip_boundary_detection = True

    wave_solver.add_constraint(second_read_constraint)

    dut._log.info(f"WaveDrom configured with {len(wave_solver.constraints)} AXI4 slave read constraints")

    # Get current sim time
    import cocotb
    start_time = cocotb.utils.get_sim_time('ns')
    dut._log.info(f"=== STARTING SAMPLING at {start_time}ns ===")

    # Start sampling BEFORE the transactions
    await wave_solver.start_sampling()

    # Scenario 1: Single-beat read transaction
    dut._log.info("=== Scenario 1: Single-Beat Read Transaction ===")
    success, data, info = await tb.base_tb.single_read_response_test(addr=0x1000)
    if success:
        dut._log.info(f"✓ Single-beat read completed: addr=0x1000, data=0x{data:08X}")

    await tb.base_tb.wait_clocks('aclk', 30)

    # Scenario 2: Another single-beat read (different address)
    dut._log.info("=== Scenario 2: Single-Beat Read (addr 0x2000) ===")
    success, data, info = await tb.base_tb.single_read_response_test(addr=0x2000)
    if success:
        dut._log.info(f"✓ Single-beat read completed: addr=0x2000, data=0x{data:08X}")

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

    dut._log.info(f"✅ AXI4 Slave Read Monitor WaveDrom Complete: {len(results['solutions'])} waveforms generated")
    dut._log.info("=" * 80)


# ============================================================================
# PyTest Test Runner
# ============================================================================
@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level",
    generate_axi4_monitor_params()
)
def test_axi4_slave_rd_mon(id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level):
    """
    Integration test runner for AXI4 slave read monitor.

    Controlled by REG_LEVEL environment variable:
        GATE: 1 test  - Quick smoke test
        FUNC: 3 tests - Functional validation (default)
        FULL: 9 tests - Comprehensive testing
    """

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi4_slave_rd_mon"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{worker_id}_{worker_id}_{dut_name}_iw{id_width}_aw{addr_width}_dw{data_width}_mt{max_trans}_sk{skid_ar}x{skid_r}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources
    verilog_sources = [
        # Monitor packages (must be compiled in order)
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba5_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi4'], "axi4_slave_rd.sv"),
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

    # RTL parameters (from test parameters)
    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'UNIT_ID': '1',
        'AGENT_ID': '20',
        'MAX_TRANSACTIONS': str(max_trans),
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AR': str(skid_ar),
        'SKID_DEPTH_R': str(skid_r),
    }

    # Validate address width meets AXI4 specification
    validate_addr_width(rtl_parameters['AXI_ADDR_WIDTH'])

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_STUB': '0',  # Not stub - real RTL
        'SEED': str(random.randint(0, 100000)),
        'TEST_CLK_PERIOD': '10',
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME", "-Wno-PINMISSING",
        "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
    ]

    print(f"\n{'='*80}")
    print(f"AXI4 Slave Read Monitor Integration Test")
    print(f"Test Level: {test_level}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module="test_axi4_slave_rd_mon",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ PASSED: {test_name}")
    except Exception as e:
        print(f"✗ FAILED: {test_name}")
        print(f"Error: {str(e)}")
        raise
