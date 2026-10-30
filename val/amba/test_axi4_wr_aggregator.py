# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi4_wr_aggregator
# Purpose: axi4_wr_aggregator test runner (Pattern A)
#
# Author: sean galloway
# Created: 2026-10-28

"""axi4_wr_aggregator: AW/W/B write aggregator.
All checking lives in bin/TBClasses/axi_aggregator/axi4_aggregator_tb.py."""

import os
import random
from itertools import product

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi_aggregator.axi4_aggregator_tb import Axi4AggregatorTB


@cocotb.test(timeout_time=60, timeout_unit="sec")
async def axi4_wr_aggregator_test(dut):
    tb = Axi4AggregatorTB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    await tb.setup_clocks_and_reset()
    ok = await tb.run_suite(level)
    assert ok, f"{len(tb.errors)} violation(s):\n  " + "\n  ".join(tb.errors[:20])


def generate_test_params():
    """(data_width, hold_cycles, fifo_depth, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return [(32, 4, 4, 'gate')]
    if reg == 'FUNC':
        return [(32, 4, 4, 'func'), (32, 0, 4, 'func'), (64, 4, 4, 'func'), (32, 4, 2, 'func')]
    return list(product((32, 64), (0, 4), (2, 4), ('gate', 'func', 'full')))


@pytest.mark.parametrize("data_width, hold_cycles, fifo_depth, test_level", generate_test_params())
def test_axi4_wr_aggregator(request, data_width, hold_cycles, fifo_depth, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared': 'rtl/amba/shared', 'rtl_amba_includes': 'rtl/amba/includes',
    })
    dut_name = "axi4_wr_aggregator"
    test_name_plus_params = f"test_{dut_name}_dw{data_width}_h{hold_cycles}_d{fifo_depth}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, module=dut_name)
    rtl_parameters = {'AXI_ID_WIDTH': '4', 'AXI_ADDR_WIDTH': '32', 'AXI_DATA_WIDTH': str(data_width),
                      'AXI_USER_WIDTH': '1', 'HOLD_CYCLES': str(hold_cycles),
                      'AGG_FIFO_DEPTH': str(fifo_depth)}
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1', 'DUT': dut_name,
        'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': test_level, 'AGG_KIND': 'wr',
        'TEST_DATA_WIDTH': str(data_width), 'TEST_HOLD_CYCLES': str(hold_cycles),
        'TEST_AGG_FIFO_DEPTH': str(fifo_depth), 'TEST_ID_WIDTH': '4', 'TEST_ADDR_WIDTH': '32',
        'TEST_USER_WIDTH': '1',
    }
    for k in ('AGG_TB_MUTATE',):
        if k in os.environ:
            extra_env[k] = os.environ[k]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    print(f"\n{'='*80}\n{dut_name}: {test_level.upper()} DW={data_width} HOLD={hold_cycles} "
          f"DEPTH={fifo_depth}\n{'='*80}")
    try:
        run(python_search=[tests_dir, repo_root], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, parameters=rtl_parameters, simulator='verilator',
            sim_build=sim_build, extra_env=extra_env, waves=False, keep_files=True,
            compile_args=["--trace", "--trace-structs", "--trace-depth", "99"],
            sim_args=["--trace", "--trace-structs", "--trace-depth", "99"],
            plus_args=["--trace"])
        print(f"PASSED {test_level.upper()}")
    except Exception as e:
        print(f"FAILED {test_level.upper()}: {e}\n   Logs: {log_path}\n   Waveforms: {cmd_filename}")
        raise
