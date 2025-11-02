# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_drop_fifo_wavedrom
# Purpose: GAXI Drop FIFO WaveDrom Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
GAXI Drop FIFO WaveDrom Test

Demonstrates GAXI drop FIFO timing diagrams showcasing:

1. **Normal FIFO Operations:**
   - Write operations (fill FIFO)
   - Read operations (drain FIFO)
   - Simultaneous read/write

2. **Drop Operations:**
   - Drop by count (removing N oldest entries)
   - Drop all (clearing entire FIFO)
   - I/O blocking during drop

3. **Visualization:**
   - Clock and reset included
   - Drop interface signals (drop_valid, drop_ready, drop_count, drop_all)
   - FIFO state (count, wr_ready, rd_valid)
   - Data flow (wr_data, rd_data)
   - Separate scenarios for each behavior
"""

import os
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
import pytest
from cocotb_test.simulator import run

# Import GAXI wavedrom support
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import (
    get_gaxi_field_config,
    create_gaxi_wavejson_generator,
)
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver,
    TemporalConstraint,
    TemporalEvent,
    SignalTransition,
    TemporalRelation
)
from CocoTBFramework.tbclasses.shared.utilities import get_paths


@cocotb.test(timeout_time=10, timeout_unit="sec")
async def gaxi_drop_fifo_wavedrom_cocotb(dut):
    """
    GAXI Drop FIFO waveform generation with segmented scenario capture.

    Scenarios:
    1. Fill FIFO - write several entries until approaching full
    2. Drop by count - drop 2 oldest entries, showing count decrease
    3. Drop all - clear entire FIFO
    4. Simultaneous write/drop - show I/O blocking during drop operation

    Each waveform includes:
    - Clock & Reset signals
    - Write interface (wr_valid, wr_ready, wr_data)
    - Read interface (rd_valid, rd_ready, rd_data)
    - Drop interface (drop_valid, drop_ready, drop_count, drop_all)
    - FIFO state (count)

    Environment Variables:
        TRIM_MODE: Waveform trimming (minimal/moderate/default)
        ENABLE_WAVEDROM: Enable waveform generation (1/0, default: 1)
    """
    # Start clock
    clock = Clock(dut.axi_aclk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.axi_aresetn.value = 0
    await Timer(20, units="ns")
    dut.axi_aresetn.value = 1
    await RisingEdge(dut.axi_aclk)

    # Get test parameters
    trim_mode = os.environ.get('TRIM_MODE', 'default')
    context_before = {'minimal': 3, 'moderate': 4, 'default': 5}[trim_mode]
    context_after = {'minimal': 1, 'moderate': 3, 'default': None}[trim_mode]

    # Check if waveforms are enabled
    enable_wavedrom = int(os.environ.get('ENABLE_WAVEDROM', '1'))
    if not enable_wavedrom:
        dut._log.info("⏭️  WaveDrom disabled, running basic test")
        # Run basic test without wavedrom
        await run_basic_test(dut)
        return

    # === Setup WaveDrom Infrastructure ===
    field_config = get_gaxi_field_config(data_width=8)  # 8-bit for readability
    wave_generator = create_gaxi_wavejson_generator(field_config, signal_prefix="")

    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=field_config,
        debug_level=1
    )

    wave_solver.add_clock_group('default', dut.axi_aclk)

    # === Bind Signals ===
    # Auto-bind GAXI write/read interfaces
    wave_solver.auto_bind_signals('gaxi', signal_prefix='wr_', field_config=field_config)
    wave_solver.auto_bind_signals('gaxi', signal_prefix='rd_', field_config=field_config)

    # Manual bindings for clock, reset
    wave_solver.add_signal_binding('clk', 'axi_aclk')
    wave_solver.add_signal_binding('rst_n', 'axi_aresetn')

    # Manually bind drop interface signals
    wave_solver.add_signal_binding('drop_valid', 'drop_valid')
    wave_solver.add_signal_binding('drop_ready', 'drop_ready')

    from CocoTBFramework.components.shared.field_config import FieldDefinition
    drop_count_field = FieldDefinition('drop_count', 8, format='dec', description='Drop count')
    wave_solver.add_signal_binding('drop_count', 'drop_count', drop_count_field)
    wave_solver.add_signal_binding('drop_all', 'drop_all')

    # Bind state signals
    count_field = FieldDefinition('count', 4, format='dec', description='FIFO count')
    wave_solver.add_signal_binding('count', 'count', count_field)
    wave_solver.add_signal_binding('wr_xfer', 'w_write')
    wave_solver.add_signal_binding('rd_xfer', 'w_read')

    # Define interface groups
    wave_generator.add_interface_group("Clock & Reset", ['clk', 'rst_n'])
    wave_generator.add_interface_group("Write", ['wr_valid', 'wr_ready', 'wr_data'])
    wave_generator.add_interface_group("Read", ['rd_valid', 'rd_ready', 'rd_data'])
    wave_generator.add_interface_group("Drop", ['drop_valid', 'drop_ready', 'drop_count', 'drop_all'])
    wave_generator.add_interface_group("State", ['count', 'wr_xfer', 'rd_xfer'])

    # === Define Constraints (upfront) ===
    # Scenario 1: Fill FIFO
    c1 = TemporalConstraint(
        name="fill_fifo",
        events=[
            TemporalEvent("first_write", SignalTransition("wr_xfer", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=15,
        context_cycles_before=context_before,
        context_cycles_after=context_after,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Drop', 'drop_valid', 'drop_ready', 'drop_count', 'drop_all'], '|',
            ['State', 'count', 'wr_xfer', 'rd_xfer']
        ]
    )
    wave_solver.add_constraint(c1)

    # Scenario 2: Drop by count
    c2 = TemporalConstraint(
        name="drop_by_count",
        events=[
            TemporalEvent("drop_start", SignalTransition("drop_valid", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=15,
        context_cycles_before=context_before,
        context_cycles_after=context_after,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Drop', 'drop_valid', 'drop_ready', 'drop_count', 'drop_all'], '|',
            ['State', 'count', 'wr_xfer', 'rd_xfer']
        ]
    )
    wave_solver.add_constraint(c2)

    # Scenario 3: Drop all
    c3 = TemporalConstraint(
        name="drop_all",
        events=[
            TemporalEvent("drop_all_start", SignalTransition("drop_all", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=15,
        context_cycles_before=context_before,
        context_cycles_after=context_after,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Drop', 'drop_valid', 'drop_ready', 'drop_count', 'drop_all'], '|',
            ['State', 'count', 'wr_xfer', 'rd_xfer']
        ]
    )
    wave_solver.add_constraint(c3)

    # Scenario 4: Comprehensive (read + drop)
    c4 = TemporalConstraint(
        name="comprehensive",
        events=[
            TemporalEvent("read_start", SignalTransition("rd_xfer", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=20,
        context_cycles_before=context_before,
        context_cycles_after=context_after,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Drop', 'drop_valid', 'drop_ready', 'drop_count', 'drop_all'], '|',
            ['State', 'count', 'wr_xfer', 'rd_xfer']
        ]
    )
    wave_solver.add_constraint(c4)

    # Initialize signals
    dut.wr_valid.value = 0
    dut.wr_data.value = 0
    dut.rd_ready.value = 0
    dut.drop_valid.value = 0
    dut.drop_count.value = 0
    dut.drop_all.value = 0

    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    # ===================================================================
    # Scenario 1: Fill FIFO
    # ===================================================================
    dut._log.info("=== Scenario 1: Fill FIFO ===")
    await wave_solver.start_sampling()

    # Write 4 entries
    for i in range(4):
        dut.wr_valid.value = 1
        dut.wr_data.value = 0xA0 + i
        await RisingEdge(dut.axi_aclk)
        while int(dut.wr_ready.value) == 0:
            await RisingEdge(dut.axi_aclk)

    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 1 captured: fill FIFO")

    # ===================================================================
    # Scenario 2: Drop by Count
    # ===================================================================
    dut._log.info("=== Scenario 2: Drop by Count ===")
    await wave_solver.start_sampling()

    # Drop 2 entries
    dut.drop_valid.value = 1
    dut.drop_count.value = 2
    dut.drop_all.value = 0
    await RisingEdge(dut.axi_aclk)

    # Wait for drop_ready
    while int(dut.drop_ready.value) == 0:
        await RisingEdge(dut.axi_aclk)

    dut.drop_valid.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 2 captured: drop by count")

    # ===================================================================
    # Scenario 3: Drop All
    # ===================================================================
    dut._log.info("=== Scenario 3: Drop All ===")
    await wave_solver.start_sampling()

    # Drop all
    dut.drop_valid.value = 1
    dut.drop_count.value = 0
    dut.drop_all.value = 1
    await RisingEdge(dut.axi_aclk)

    while int(dut.drop_ready.value) == 0:
        await RisingEdge(dut.axi_aclk)

    dut.drop_valid.value = 0
    dut.drop_all.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 3 captured: drop all")

    # ===================================================================
    # Scenario 4: Write with Fill + Read + Drop (comprehensive)
    # ===================================================================
    dut._log.info("=== Scenario 4: Comprehensive (Write, Read, Drop) ===")

    # Refill FIFO first
    for i in range(4):
        dut.wr_valid.value = 1
        dut.wr_data.value = 0xD0 + i
        await RisingEdge(dut.axi_aclk)
        while int(dut.wr_ready.value) == 0:
            await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.start_sampling()

    # Read 1 entry
    dut.rd_ready.value = 1
    await RisingEdge(dut.axi_aclk)
    if int(dut.rd_valid.value) == 1:
        await RisingEdge(dut.axi_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)

    # Drop remaining
    dut.drop_valid.value = 1
    dut.drop_all.value = 1
    await RisingEdge(dut.axi_aclk)
    while int(dut.drop_ready.value) == 0:
        await RisingEdge(dut.axi_aclk)
    dut.drop_valid.value = 0
    dut.drop_all.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 4 captured: comprehensive")

    dut._log.info("✅ WaveDrom generation complete - check docs/markdown/assets/WAVES/")


async def run_basic_test(dut):
    """Basic functional test without waveforms"""
    dut.wr_valid.value = 0
    dut.rd_ready.value = 0
    dut.drop_valid.value = 0
    dut.drop_count.value = 0
    dut.drop_all.value = 0

    await RisingEdge(dut.axi_aclk)

    # Write
    dut.wr_valid.value = 1
    dut.wr_data.value = 0xAA
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0

    await RisingEdge(dut.axi_aclk)

    # Read
    dut.rd_ready.value = 1
    await RisingEdge(dut.axi_aclk)
    assert dut.rd_data.value == 0xAA
    dut.rd_ready.value = 0

    dut._log.info("✓ Basic test passed")


def test_gaxi_drop_fifo_wavedrom():
    """Pytest runner for WaveDrom test"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    # Test parameters - small FIFO for clear waveforms
    data_width = 8
    depth = 8
    registered = 0  # Mux mode for simpler waveforms

    dut_name = "gaxi_drop_fifo_sync"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_includes'], "fifo_defs.svh"),
        os.path.join(rtl_dict['rtl_amba'], 'gaxi/gaxi_drop_fifo_sync.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin_load.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'fifo_control.sv'),
    ]

    test_name = f"test_{worker_id}_gaxi_drop_fifo_wavedrom_dw{data_width}_d{depth}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    includes=[rtl_dict['rtl_amba_includes']]

    parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'REGISTERED': str(registered),
        'ALMOST_WR_MARGIN': '1',
        'ALMOST_RD_MARGIN': '1',
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'WAVES': '1',
        'ENABLE_WAVEDROM': '1',  # Enable WaveDrom generation
        'TRIM_MODE': 'default',
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--Wno-UNOPTFLAT",
    ]

    print(f"\n{'='*60}")
    print(f"Testing GAXI Drop FIFO WaveDrom")
    print(f"Log: {log_path}")
    print(f"Waveforms: docs/markdown/assets/WAVES/")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Use VCD
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ WaveDrom test PASSED")
    except Exception as e:
        print(f"✗ WaveDrom test FAILED: {str(e)}")
        print(f"View waveform: gtkwave {sim_build}/dump.vcd")
        raise


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
