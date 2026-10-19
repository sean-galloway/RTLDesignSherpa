# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_tile_injectors
# Purpose: Unit tests for the rapids tile harness's cell model: tile_cell_tx
#          and tile_credit_rx (rapids TASK-032)
#
# Subsystem: fpga-systems/Genesys2/rapids tile harness
# Author: sean galloway
# Created: 2026-10-19

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from tile_injectors_tb import TileInjectorsTB  # noqa: E402

_FLOW = 'projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids-tile'


async def _bring_up(dut) -> TileInjectorsTB:
    tb = TileInjectorsTB(dut)
    await tb.setup_clocks_and_reset()
    return tb


def _finish(ok, stats, what):
    assert ok, f"{what} failed: {stats.get('errors')}"


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_stream(dut):
    """Two cells stream past their straps on RAPIDS's returns."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_stream()
    _finish(ok, stats, "cell stream")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_stream_ordered(dut):
    """The same stream with the O4 ordering rule on."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_stream(ordered=True)
    _finish(ok, stats, "ordered cell stream")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_ordered(dut):
    """O4: the next packet waits for every flit of the last one back."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_ordered()
    _finish(ok, stats, "ordered packets")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_strap_gate(dut):
    """With no returns a cell sends only what its strap covers."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_strap_gate()
    _finish(ok, stats, "strap gate")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_bad_returns(dut):
    """Malformed and excess returns are flagged and not applied."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_bad_returns()
    _finish(ok, stats, "bad returns")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_too_big(dut):
    """A packet larger than the strap is refused."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_too_big()
    _finish(ok, stats, "oversized packet")


@pytest.mark.parametrize("testcase", ["stream", "stream_ordered", "ordered", "strap_gate", "bad_returns", "too_big"])
@pytest.mark.parametrize("land", [16, 8])
def test_tile_injectors(request, testcase, land):
    module, repo_root_local, tests_dir, log_dir, _ = get_paths({})
    dut_name = 'tb_tile_cell_loop'
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local, filelist_path=f'{_FLOW}/filelists/tile_injectors.f')
    verilog_sources.append(os.path.join(repo_root_local, _FLOW, 'dv', 'tb_tile_cell_loop.sv'))

    test_name = f"test_tile_injectors_{testcase}_land{land}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'TEST_DATA_WIDTH': '512',
        'TEST_LAND_FLITS': str(land),
    }
    compile_args = ['-Wno-fatal', '-Wno-TIMESCALEMOD', '-Wno-WIDTH', '-Wno-UNUSEDSIGNAL',
                    '-Wno-DECLFILENAME', '-Wno-PINCONNECTEMPTY', '-Wno-UNUSEDPARAM']
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, testcase=f"cocotb_test_{testcase}",
            parameters={'DW': 512, 'LAND_FLITS': land}, simulator='verilator',
            sim_build=sim_build, results_xml=results_path, extra_env=extra_env,
            compile_args=compile_args, keep_files=True)
    except Exception as e:
        print(f'Test failed: {e}\nLogs: {log_path}')
        if os.path.exists(cmd_filename):
            print(f'View: {cmd_filename}')
        raise
