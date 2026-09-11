# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi4_cdc
# Purpose: axi4_cdc_wr / axi4_cdc_rd across three clock ratios
#
# Author: sean galloway
# Created: 2026-09-11

"""AXI4 channels across a clock-domain boundary (BRIDGE-017 CDC slave ports).
Requester on s_aclk, completer on m_aclk, at equal, requester-fast and
requester-slow periods. See bin/TBClasses/amba/axi4_cdc_tb.py."""

import os
import random

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.axi4_cdc_tb import AXI4CdcTB


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def axi4_cdc_test(dut):
    tb = AXI4CdcTB(dut)
    seed = int(os.environ.get('SEED', '42'))
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if level not in ('gate', 'func', 'full'):
        level = 'gate'
    await tb.setup_clocks_and_reset()
    ok = await tb.run_suite(level, seed)
    assert ok, f"{len(tb.errors)} violation(s):\n  " + "\n  ".join(tb.errors[:20])


def generate_test_params():
    """(channel, data_width, s_period, m_period, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    ratios = [(10, 10), (10, 3), (3, 10)]
    if reg == 'GATE':
        return [(ch, 32, 10, 3, 'gate') for ch in ('wr', 'rd')]
    if reg == 'FUNC':
        return [(ch, 32, s, m, 'func') for ch in ('wr', 'rd') for (s, m) in ratios]
    return [(ch, dw, s, m, 'full') for ch in ('wr', 'rd') for dw in (32, 64) for (s, m) in ratios + [(7, 10)]]


@pytest.mark.parametrize("channel, data_width, s_period, m_period, test_level", generate_test_params())
def test_axi4_cdc(request, channel, data_width, s_period, m_period, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_cdc': 'rtl/cdc', 'rtl_amba_includes': 'rtl/amba/includes',
    })
    dut_name = f"axi4_cdc_{channel}"
    test_name_plus_params = f"test_{dut_name}_dw{data_width}_s{s_period}_m{m_period}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'rtl/amba/filelists/{dut_name}.f')
    rtl_parameters = {'AXI_ID_WIDTH': '4', 'AXI_ADDR_WIDTH': '32', 'AXI_DATA_WIDTH': str(data_width),
                      'AXI_USER_WIDTH': '1', 'CDC_DEPTH': '8', 'USE_JOHNSON': '0', 'N_FLOP_CROSS': '2'}
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1', 'DUT': dut_name,
        'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': test_level, 'CDC_CHANNEL': channel,
        'AXI_DATA_WIDTH': str(data_width), 'AXI_ADDR_WIDTH': '32', 'AXI_ID_WIDTH': '4',
        'S_PERIOD': str(s_period), 'M_PERIOD': str(m_period),
    }
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    print(f"\n{'='*80}\n{dut_name}: {test_level.upper()} DW={data_width} s={s_period}ns m={m_period}ns\n{'='*80}")
    try:
        run(python_search=[tests_dir, repo_root], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, parameters=rtl_parameters, simulator='verilator',
            sim_build=sim_build, extra_env=extra_env, waves=False, keep_files=True,
            compile_args=["--trace", "--trace-structs", "--trace-depth", "99"],
            sim_args=["--trace", "--trace-structs", "--trace-depth", "99"])
        print(f"PASSED {test_level.upper()}")
    except Exception as e:
        print(f"FAILED {test_level.upper()}: {e}\n   Logs: {log_path}\n   Waveforms: {cmd_filename}")
        raise
