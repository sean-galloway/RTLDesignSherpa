# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_group_core_1wr
# Purpose: runner for monbus_group_core_1wr -- the bare single-write-port group core at its AXI4-shaped FUB
#
# Author: sean galloway
# Created: 2026-10-23

"""
monbus_group_core_1wr driven at its own pins: the AXI4-shaped master-write
FUB is the slave side, no protocol leaf in the way.

The bench is bin/TBClasses/amba/monbus_group_1wr/monbus_group_1wr_tb.py,
shared by the bare core and both protocol wrappers; this file only picks the
write-port shape, the REG_LEVEL grid and the RTL parameters.

Cells: TEST_TYPE in (errors_only, trace_only, mixed) x MAX_BURST_BEATS (1 = the AXIL leaf shape, every record three sub-bursts; 16/64 = AXI4 bursts).
REG_LEVEL widens the grid; TEST_LEVEL (derived from it unless set) deepens
each cell (records, ingress profile, slave ready distribution).
"""

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.monbus_group_1wr.monbus_group_1wr_tb import MonbusGroup1wrTB


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_monbus_group_core_1wr(dut):
    tb = MonbusGroup1wrTB(dut, trace_proto="axi4", trace_prefix="fub_m_")
    await tb.setup_clocks_and_reset()
    await tb.setup_interfaces()
    await tb.run()


def generate_monbus_group_core_1wr_params():
    """(test_type, max_burst_beats) per REG_LEVEL: gate one cell, func the three
    stream types, full the three types over every burst shape."""
    reg = os.environ.get('REG_LEVEL', 'GATE').upper()
    if reg == 'GATE':
        return [('mixed', 16)]
    types = ['errors_only', 'trace_only', 'mixed']
    grid = [1, 16] if reg == 'FUNC' else [1, 16, 64]
    return [(t, g) for g in grid for t in types]


@pytest.mark.parametrize("test_type, max_burst_beats", generate_monbus_group_core_1wr_params())
def test_monbus_group_core_1wr(request, test_type, max_burst_beats):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_monitor':  'rtl/amba/ocelus',
    })

    dut_name = "monbus_group_core_1wr"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_{test_type}_mbb{max_burst_beats}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, module=dut_name)
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    reg = os.environ.get('REG_LEVEL', 'GATE').upper()
    test_level = os.environ.get(
        'TEST_LEVEL', {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}.get(reg, 'gate')).lower()

    parameters = {
        'ADDR_WIDTH':               32,
        'FLUSH_TIMEOUT_CYCLES':     200,
        'ERR_FLUSH_TIMEOUT_CYCLES': 32,
        'USE_COMPRESSION':          0,
        'MAX_BURST_BEATS':          max_burst_beats,
    }

    extra_env = {
        'DUT':                 dut_name,
        'LOG_PATH':            log_path,
        'COCOTB_LOG_LEVEL':    'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':                os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL':          test_level,
        'TEST_TYPE':           test_type,
    }

    compile_args = [
        '+define+SIMULATION',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-UNUSEDSIGNAL', '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [sim_build],
            toplevel=dut_name,
            module='test_monbus_group_core_1wr',
            testcase='cocotb_test_monbus_group_core_1wr',
            sim_build=sim_build,
            extra_env=extra_env,
            parameters=parameters,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"{dut_name} {test_type} max_burst_beats={max_burst_beats} PASSED! Logs: {log_path}")
    except Exception as e:
        print(f"{dut_name} {test_type} max_burst_beats={max_burst_beats} FAILED: {e}")
        print(f"Logs: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
