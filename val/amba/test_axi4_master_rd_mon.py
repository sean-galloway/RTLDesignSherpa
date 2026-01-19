# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_master_rd_mon
# Purpose: AXI4 Master Read Monitor Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Master Read Monitor Integration Test

Thin wrapper that uses the reusable AXI4MasterMonitorTB testbench class.
All test logic is in bin/CocoTBFramework/tbclasses/axi4/monitor/axi4_master_monitor_tb.py
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.tbclasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4_master_rd_mon_test(dut):
    """AXI4 master read monitor integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Create testbench (is_write=False for read master)
    tb = AXI4MasterMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Run all integration tests
    await tb.run_integration_tests(test_level=test_level)


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


# ============================================================================
# PyTest Test Runner
# ============================================================================
@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level",
    generate_axi4_monitor_params()
)
def test_axi4_master_rd_mon(id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level):
    """
    Integration test runner for AXI4 master read monitor.

    Controlled by REG_LEVEL environment variable:
        GATE: 1 test  - Quick smoke test
        FUNC: 3 tests - Functional validation (default)
        FULL: 9 tests - Comprehensive testing
    """

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi4_master_rd_mon"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{dut_name}_iw{id_width}_aw{addr_width}_dw{data_width}_mt{max_trans}_sk{skid_ar}x{skid_r}_{test_level}_{reg_level}"

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
        os.path.join(rtl_dict['rtl_axi4'], "axi4_master_rd.sv"),
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
        'AGENT_ID': '10',
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

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    print(f"\n{'='*80}")
    print(f"AXI4 Master Read Monitor Integration Test")
    print(f"Test Level: {test_level}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module="test_axi4_master_rd_mon",
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


# ==============================================================================
# WaveDrom Test - Proof of Concept
# ==============================================================================

@cocotb.test(timeout_time=10, timeout_unit="sec")
async def axi4_master_rd_mon_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for AXI4 master read monitor.

    Generates basic AXI4 read transaction waveforms showing:
    - Clock and reset
    - AR channel (arvalid, arready, araddr, arid, arlen)
    - R channel (rvalid, rready, rdata, rlast, rresp)
    - Monitor bus output (monbus_valid, monbus_ready, monbus_packet)

    Enable with ENABLE_WAVEDROM=1 environment variable.
    """
    import os

    enable_wavedrom = int(os.environ.get('ENABLE_WAVEDROM', '0'))
    if not enable_wavedrom:
        dut._log.info("⏭️  WaveDrom disabled (ENABLE_WAVEDROM=0), skipping wavedrom test")
        return

    from CocoTBFramework.components.wavedrom.constraint_solver import TemporalConstraintSolver
    from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
    from CocoTBFramework.tbclasses.wavedrom_user.axi4 import (
        create_axi4_ar_handshake_constraint,
        create_axi4_r_handshake_constraint,
        get_axi4_channel_field_config
    )

    # Create testbench (is_write=False for read monitor)
    tb = AXI4MasterMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()

    dut._log.info("=== Setting up AXI4 Read Monitor WaveDrom ===")

    # Create field configs for AR and R channels
    ar_config = get_axi4_channel_field_config('AR', id_width=8, addr_width=32, data_width=32)
    r_config = get_axi4_channel_field_config('R', id_width=8, addr_width=32, data_width=32)

    # Setup WaveDrom with constraint solver (matching GAXI pattern exactly)
    wave_generator = WaveJSONGenerator()
    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=ar_config
    )
    wave_solver.add_clock_group('default', dut.aclk)

    # Use signal_map to explicitly specify AR channel signals
    # This avoids conflict with R channel signals that have same field names
    ar_signal_map = {
        'arvalid': 'fub_axi_arvalid',
        'arready': 'fub_axi_arready',
        'rvalid': 'fub_axi_rvalid',
        'rready': 'fub_axi_rready',
        # AR channel fields
        'addr': 'fub_axi_araddr',
        'id': 'fub_axi_arid',
        'len': 'fub_axi_arlen',
        'size': 'fub_axi_arsize',
        'burst': 'fub_axi_arburst',
        'lock': 'fub_axi_arlock',
        'cache': 'fub_axi_arcache',
        'prot': 'fub_axi_arprot',
        'qos': 'fub_axi_arqos',
        'region': 'fub_axi_arregion',
    }
    wave_solver.auto_bind_signals('axi4_read', signal_map=ar_signal_map, field_config=ar_config)

    # Manual bindings for clock and reset (not part of axi4_read protocol)
    wave_solver.add_signal_binding('aclk', 'aclk')
    wave_solver.add_signal_binding('aresetn', 'aresetn')

    # Bind the ACTUAL AXI interface signals (m_axi_*) and monbus
    wave_solver.add_signal_binding('m_axi_arvalid', 'm_axi_arvalid')
    wave_solver.add_signal_binding('m_axi_arready', 'm_axi_arready')
    wave_solver.add_signal_binding('m_axi_arid', 'm_axi_arid')
    wave_solver.add_signal_binding('m_axi_araddr', 'm_axi_araddr')
    wave_solver.add_signal_binding('m_axi_arlen', 'm_axi_arlen')
    wave_solver.add_signal_binding('m_axi_rvalid', 'm_axi_rvalid')
    wave_solver.add_signal_binding('m_axi_rready', 'm_axi_rready')
    wave_solver.add_signal_binding('m_axi_rid', 'm_axi_rid')
    wave_solver.add_signal_binding('m_axi_rdata', 'm_axi_rdata')
    wave_solver.add_signal_binding('m_axi_rlast', 'm_axi_rlast')
    wave_solver.add_signal_binding('m_axi_rresp', 'm_axi_rresp')
    wave_solver.add_signal_binding('monbus_valid', 'monbus_valid')
    wave_solver.add_signal_binding('monbus_ready', 'monbus_ready')

    # Use GAXI's pattern with SignalTransition directly
    from CocoTBFramework.components.wavedrom.constraint_solver import (
        TemporalConstraint, TemporalEvent, SignalTransition, TemporalRelation
    )

    # Complete read transaction showing all channels together
    complete_signals = [
        'aclk', 'aresetn', '|',
        ['AR Channel', 'm_axi_arvalid', 'm_axi_arready', 'm_axi_arid', 'm_axi_araddr', 'm_axi_arlen'],
        '|',
        ['R Channel', 'm_axi_rvalid', 'm_axi_rready', 'm_axi_rid', 'm_axi_rdata', 'm_axi_rlast', 'm_axi_rresp'],
        '|',
        ['Monitor Bus', 'monbus_valid', 'monbus_ready']
    ]

    # Constraint 1: Single-beat read: AR handshake -> R response -> MonBus packet
    single_read_constraint = TemporalConstraint(
        name="single_beat_read",
        events=[
            TemporalEvent("ar_handshake", SignalTransition("m_axi_arvalid", 0, 1))
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

    # Constraint 2: Second read transaction (different address)
    second_read_constraint = TemporalConstraint(
        name="single_beat_read_002",
        events=[
            TemporalEvent("ar_handshake_2", SignalTransition("m_axi_arvalid", 0, 1))
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=80,
        required=False,  # Optional - captures second transaction if it occurs
        clock_group="default",
        signals_to_show=complete_signals,
        min_sequence_duration=1,
        max_sequence_duration=75
    )
    second_read_constraint.post_match_cycles = 20
    second_read_constraint.skip_boundary_detection = True

    wave_solver.add_constraint(second_read_constraint)

    dut._log.info(f"WaveDrom configured with {len(wave_solver.constraints)} AXI4 constraints")

    # Get current sim time
    import cocotb
    start_time = cocotb.utils.get_sim_time('ns')
    dut._log.info(f"=== STARTING SAMPLING at {start_time}ns ===")

    # Start sampling BEFORE the transactions
    await wave_solver.start_sampling()

    # Scenario 1: Single-beat read transaction
    dut._log.info("=== Scenario 1: Single-Beat Read Transaction ===")
    success, data, info = await tb.base_tb.single_read_test(addr=0x1000)
    if success:
        dut._log.info(f"✓ Single-beat read completed: addr=0x1000, data=0x{data:08X}")

    await tb.base_tb.wait_clocks('aclk', 30)

    # Scenario 2: Another single-beat read (different address)
    dut._log.info("=== Scenario 2: Single-Beat Read (addr 0x2000) ===")
    success, data, info = await tb.base_tb.single_read_test(addr=0x2000)
    if success:
        dut._log.info(f"✓ Single-beat read completed: addr=0x2000, data=0x{data:08X}")

    await tb.base_tb.wait_clocks('aclk', 30)

    # Stop sampling and generate waveforms
    await wave_solver.stop_sampling()

    # DEBUG: Print constraint details before solving
    dut._log.info(f"=== DEBUG: Constraint Details ===")
    if hasattr(wave_solver, 'constraints'):
        for name, constraint in wave_solver.constraints.items():
            dut._log.info(f"Constraint: {name}")
            dut._log.info(f"  Events: {len(constraint.events)}")
            for event in constraint.events:
                dut._log.info(f"    - {event.name}: {event.pattern}")
            dut._log.info(f"  Relation: {constraint.temporal_relation}")
            dut._log.info(f"  Clock group: {constraint.clock_group}")

    # DEBUG: Check what signals are registered
    dut._log.info(f"=== DEBUG: Registered Interfaces ===")
    if hasattr(wave_solver, '_signal_map'):
        for sig_name, dut_handle in wave_solver._signal_map.items():
            dut._log.info(f"  {sig_name} -> {dut_handle}")

    await wave_solver.solve_and_generate()
    results = wave_solver.get_results()

    # Check results - MUST pass for regression testing
    dut._log.info("=" * 80)
    if not results['all_required_satisfied']:
        dut._log.error(f"❌ REQUIRED WAVEFORMS NOT GENERATED ❌")
        dut._log.error(f"Failed constraints: {results['failed_constraints']}")
        raise AssertionError(f"Required waveforms not generated: {results['failed_constraints']}")

    dut._log.info(f"✅ AXI4 Read Monitor WaveDrom Complete: {len(results['solutions'])} waveforms generated")
    dut._log.info("=" * 80)


@pytest.mark.parametrize("id_width, addr_width, data_width", [(8, 32, 32)])
def test_axi4_master_rd_mon_wavedrom(id_width, addr_width, data_width):
    """
    AXI4 master read monitor WaveDrom test runner.

    Run with: ENABLE_WAVEDROM=1 pytest val/amba/test_axi4_master_rd_mon.py::test_axi4_master_rd_mon_wavedrom -v
    """

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi4_master_rd_mon"
    test_name_plus_params = f"test_{worker_id}_axi4_master_rd_mon_iw{id_width:03d}_aw{addr_width:03d}_dw{data_width:03d}_wd"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources (same as main test)
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
        os.path.join(rtl_dict['rtl_axi4'], "axi4_master_rd.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict['rtl_axi4'], f"{dut_name}.sv"),
    ]

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': '1',
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': '16',
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AR': '2',
        'SKID_DEPTH_R': '4',
    }

    extra_env = {
        'ENABLE_WAVEDROM': '1',  # ← Enable WaveDrom!
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
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
    print(f"AXI4 Master Read Monitor WaveDrom Test")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module="test_axi4_master_rd_mon",
            testcase="axi4_master_rd_mon_wavedrom_test",  # ← Run wavedrom test specifically!
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ AXI4 Master Read Monitor WaveDrom test completed!")
        print(f"Logs: {log_path}")
        print(f"WaveJSON files: {sim_build}/axi4_*.json")
    except Exception as e:
        print(f"❌ AXI4 Master Read Monitor WaveDrom test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        raise
