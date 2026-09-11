# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_wb4_to_axi4
# Purpose: wb4_to_axi4 converter test runner (BRIDGE-019)
#
# Author: sean galloway
# Created: 2026-09-11

"""wb4_to_axi4: see dv/tbclasses/wb4_to_axi4_tb.py for what is checked.
Levels: gate = the round trip and error folding; func = more, with a
stalling completer; full = the width and classic-mode sweep."""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, get_paths, create_view_cmd, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.converters.dv.tbclasses.wb4_to_axi4_tb import WB4ToAXI4TB
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def wb4_to_axi4_test(dut):
    tb = WB4ToAXI4TB(dut)
    seed = int(os.environ.get('SEED', '42'))
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        test_level = 'gate'
    tb.log.info(f"seed={seed} level={test_level}")
    await tb.setup_clocks_and_reset()
    if hasattr(tb, 'axi_monitor'):
        cocotb.start_soon(tb.axi_monitor())
    ok = await tb.run_suite(test_level, seed)
    assert ok, (f"{len(tb.errors)} violation(s):\n  " + "\n  ".join(tb.errors[:20]))


def generate_test_params():
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    all_params = [
        {'data_width': 32, 'classic': 0, 'test_level': 'gate'},
        {'data_width': 32, 'classic': 0, 'test_level': 'func'},
        {'data_width': 32, 'classic': 1, 'test_level': 'func'},
        {'data_width': 32, 'classic': 0, 'test_level': 'full'},
        {'data_width': 64, 'classic': 0, 'test_level': 'full'},
        {'data_width': 32, 'classic': 1, 'test_level': 'full'},
    ]
    if reg_level == 'GATE':
        return [p for p in all_params if p['test_level'] == 'gate']
    if reg_level == 'FUNC':
        return [p for p in all_params if p['test_level'] in ('gate', 'func')]
    return all_params


@pytest.mark.parametrize("params", generate_test_params())
def test_wb4_to_axi4(request, params):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes',
    })
    dut_name = "wb4_to_axi4"
    data_width, classic, test_level = params['data_width'], params['classic'], params['test_level']
    addr_width, id_width = 32, 4

    test_name_plus_params = f"test_{dut_name}_dw{data_width}_{'classic' if classic else 'pipe'}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/converters/rtl/filelists/{dut_name}.f')

    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width), 'AXI_ID_WIDTH': str(id_width), 'AXI_USER_WIDTH': '1', 'CLASSIC': str(classic)}
    timeout_ms = {'gate': 30000, 'func': 90000, 'full': 300000}[test_level]
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1', 'DUT': dut_name,
        'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width), 'AXI_ID_WIDTH': str(id_width), 'CLASSIC': str(classic),
    }
    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}\n{dut_name}: {test_level.upper()} DW={data_width} classic={classic}\n{'='*80}")
    try:
        run(python_search=[tests_dir, repo_root], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, parameters=rtl_parameters, simulator='verilator',
            sim_build=sim_build, extra_env=extra_env, waves=enable_waves, keep_files=True,
            compile_args=compile_args, sim_args=sim_args, plus_args=['--trace'] if enable_waves else [])
        print(f"PASSED {test_level.upper()} (DW={data_width}, classic={classic})")
    except Exception as e:
        print(f"FAILED {test_level.upper()}: {e}\n   Logs: {log_path}\n   Waveforms: {cmd_filename}")
        raise
