# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_beats_top
# Purpose: rapids_beats_top (SPLIT core) AXIS datapath test (Pattern B)
#
# Documentation: projects/components/dmas/rapids/PRD.md
# Subsystem: rapids_beats_top
#
# Author: sean galloway
# Created: 2026-07-03

"""
Datapath tests for rapids_beats_top (SPLIT core).

Config is programmed BY NAME over the 13-bit APB register chain (two RegisterMap
instances, SRC @ 0x0000 / SNK @ 0x1000); descriptors are kicked off through the
per-half apb4todescr kick windows (SRC 0x000-0x03F, SNK 0x1000-0x103F). The
merged MonBus stream is consumed by the always-present monbus_axil_axil_group,
whose bulk-capture master (m_axil_mon_*) is backed by a trivial always-accept
write responder in the TB.

  cocotb_test_source_path : memory -> AXIS. Preload m_axi_rd memory, put a SOURCE
    descriptor in src_m_axi_desc memory, APB-kick SRC, capture m_axis, assert the
    egress beats == preloaded pattern.
  cocotb_test_sink_path   : AXIS -> memory. Put a SINK descriptor in snk_m_axi_desc
    memory, drive s_axis beats (tid=channel), APB-kick SNK, wait for m_axi_wr
    drain, assert m_axi_wr memory == pattern.
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

from projects.components.dmas.rapids.dv.tbclasses.rapids_beats_top_tb import RapidsBeatsTopTB


# ===========================================================================
# COCOTB TEST FUNCTIONS - thin; logic lives in the TB
# ===========================================================================

@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_source_path(dut):
    """SOURCE datapath (memory -> AXIS), configured + kicked over APB by name."""
    tb = RapidsBeatsTopTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    ok, stats = await tb.test_source_path(channel=0, beats=4)

    tb.finalize_test()
    assert ok, f"source-path datapath failed: {stats.get('errors')}"
    tb.log.info("rapids_beats_top SOURCE path PASSED")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_sink_path(dut):
    """SINK datapath (AXIS -> memory), configured + kicked over APB by name."""
    tb = RapidsBeatsTopTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    ok, stats = await tb.test_sink_path(channel=0, beats=4)

    tb.finalize_test()
    assert ok, f"sink-path datapath failed: {stats.get('errors')}"
    tb.log.info("rapids_beats_top SINK path PASSED")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_control_path(dut):
    """PRODUCER/CONSUMER control path through the split TOP with a real semaphore
    memory on the control masters. A CTRL_READ gate is held off until a CTRL_WRITE
    doorbell (through the shared per-half semaphore store) satisfies its condition."""
    tb = RapidsBeatsTopTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    ok, stats = await tb.test_control_path(half='src', gate_ch=0, doorbell_ch=1)

    tb.finalize_test()
    assert ok, f"control-path failed: {stats.get('errors')}"
    tb.log.info("rapids_beats_top CONTROL path PASSED")


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

def _run_top(testcase, test_name):
    """Shared runner: compile rapids_beats_top (split core) and run a testcase.

    The split top uses a 13-bit APB (address bit[12] selects SRC/SNK), so both
    the RTL build (-G APB_ADDR_WIDTH=13) and the TB (TEST_APB_ADDR_WIDTH=13) are
    pinned to 13 bits."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_top_beats': '../../rtl/top_beats',
    })
    dut_name = "rapids_beats_top"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/dmas/rapids/rtl/filelists/top_beats/rapids_beats_top.f'
    )

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
        'DATA_WIDTH': 512,
        'ADDR_WIDTH': 64,
        'AXI_ID_WIDTH': 8,
        'SRAM_DEPTH': 512,
        'APB_ADDR_WIDTH': 13,
        'APB_DATA_WIDTH': 32,
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(12345),
        'TEST_NUM_CHANNELS': '8',
        'TEST_ADDR_WIDTH': '64',
        'TEST_DATA_WIDTH': '512',
        'TEST_AXI_ID_WIDTH': '8',
        'TEST_APB_ADDR_WIDTH': '13',
        'TEST_APB_DATA_WIDTH': '32',
    }

    compile_args = [
        "-Wno-fatal",  # generated rapids_regs.sv trips MULTIDRIVEN/UNOPT; keep warnings non-fatal
        "-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE",
        "-Wno-MULTIDRIVEN", "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL",
    ]
    if enable_waves:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir, os.path.join(repo_root, 'projects/components/dmas/rapids/dv/tbclasses')],
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
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_source(request):
    """SOURCE datapath: memory -> AXIS, config + kick over APB (by name)."""
    _run_top("cocotb_test_source_path", "test_rapids_beats_top_source")


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_sink(request):
    """SINK datapath: AXIS -> memory, config + kick over APB (by name)."""
    _run_top("cocotb_test_sink_path", "test_rapids_beats_top_sink")


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_control(request):
    """CONTROL path: producer/consumer through the split TOP with a real semaphore
    memory on the control masters (CTRL_READ gate held off, CTRL_WRITE doorbell
    releases it)."""
    _run_top("cocotb_test_control_path", "test_rapids_beats_top_control")


if __name__ == "__main__":
    class MockRequest:
        pass
    test_rapids_beats_top_source(MockRequest())
    test_rapids_beats_top_sink(MockRequest())
    test_rapids_beats_top_control(MockRequest())
