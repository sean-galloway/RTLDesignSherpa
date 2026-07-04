# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_core_beats
# Purpose: RAPIDS Core (beats) SPLIT-core integration test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_top_beats
#
# Author: sean galloway
# Created: 2026-06-30

"""
RAPIDS Core (beats) SPLIT-core integration test.

DUT: rapids_core_beats  (thin wrapper over independent rapids_src_beats +
rapids_snk_beats halves; AXIS-fronted data paths).

Basic directional tests (dispatched by testcase):
  source : SOURCE half - memory -> AXIS. Preload memory, kick a src descriptor,
           capture m_axis egress, compare to the preloaded pattern.
  sink   : SINK   half - AXIS -> memory. Kick a snk descriptor, stream s_axis
           ingress, verify the data landed in memory via m_axi_wr.
"""

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.rapids.dv.tbclasses.rapids_core_beats_tb import RapidsCoreBeatsTB


# ===========================================================================
# COCOTB TEST FUNCTIONS - thin; logic lives in the TB
# ===========================================================================

@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_source_path(dut):
    """SOURCE half: memory -> AXIS, single channel, data-integrity check."""
    tb = RapidsCoreBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    ok, stats = await tb.test_source_path(channel=0, beats=4)
    tb.finalize_test()
    assert ok, f"source-path failed: {stats.get('errors')}"


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_sink_path(dut):
    """SINK half: AXIS -> memory, single channel, data-integrity check."""
    tb = RapidsCoreBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    ok, stats = await tb.test_sink_path(channel=0, beats=4)
    tb.finalize_test()
    assert ok, f"sink-path failed: {stats.get('errors')}"


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_params():
    """(test_type, data_width). Basic directional tests at 512-bit."""
    return [('source', 512), ('sink', 512)]


params = generate_params()


# ===========================================================================
# PYTEST WRAPPERS
# ===========================================================================

def _run_core_beats(request, test_type, data_width):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_macro_beats': '../../rtl/macro_beats',
    })
    dut_name = "rapids_core_beats"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/macro_beats/rapids_core_beats.f'
    )

    dw_str = TBBase.format_dec(data_width, 4)
    test_name = f"test_rapids_core_beats_{test_type}_dw{dw_str}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': 8,
        'ADDR_WIDTH': 64,
        'DATA_WIDTH': data_width,
        'AXI_ID_WIDTH': 8,
        'SRAM_DEPTH': 512,
    }

    extra_env = {
        'TEST_TYPE': test_type,
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(12345),
        'TEST_NUM_CHANNELS': '8',
        'TEST_ADDR_WIDTH': '64',
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AXI_ID_WIDTH': '8',
        'TEST_SRAM_DEPTH': '512',
    }

    testcase = f"cocotb_test_{test_type}_path"
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE"]
    if enable_waves:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir, os.path.join(repo_root, 'projects/components/rapids/dv/tbclasses')],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            results_xml=results_path,
            extra_env=extra_env,
            compile_args=compile_args,
            waves=enable_waves,
            keep_files=True,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View: {cmd_filename}")
        raise


@pytest.mark.top_beats
@pytest.mark.rapids_core_beats
@pytest.mark.parametrize("data_width", [512])
def test_rapids_core_beats_source(request, data_width):
    _run_core_beats(request, 'source', data_width)


@pytest.mark.top_beats
@pytest.mark.rapids_core_beats
@pytest.mark.parametrize("data_width", [512])
def test_rapids_core_beats_sink(request, data_width):
    _run_core_beats(request, 'sink', data_width)


if __name__ == "__main__":
    class MockRequest:
        pass
    _run_core_beats(MockRequest(), test_type="source", data_width=512)
