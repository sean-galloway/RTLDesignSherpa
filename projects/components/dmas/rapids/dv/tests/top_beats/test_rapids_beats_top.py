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
merged MonBus stream is consumed by the always-present monbus_axil4_axil4_group,
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
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
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


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_status_readback(dut):
    """Hardware-driven status registers must report the design, not zero.

    hwif_in was `'{default: '0}` -- the register block's hardware inputs were
    tied off -- so every status field in the map read 0 in every build and a
    zero could not be told apart from "this CSR is not wired". This reads the
    fields that now have real sources behind them.
    """
    tb = RapidsBeatsTopTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    seen = {}
    for half in ('src', 'snk'):
        for reg in ('GLOBAL_STATUS', 'SCHEDULER_IDLE', 'DESC_ENGINE_IDLE',
                    'SCHED_ERROR', 'CH_STATE0_STATE'):
            seen[f'{half}.{reg}'] = await tb.read_reg(half, reg)
    seen['src.AXI_RD_COMPLETE'] = await tb.read_reg('src', 'AXI_RD_COMPLETE')

    for k, v in seen.items():
        tb.log.info(f"status readback {k} = 0x{v:08X}")

    tb.finalize_test()

    # At rest after reset both halves are idle, so these must read non-zero.
    # Every one of them read 0 with the tie-off in place.
    for k in ('src.GLOBAL_STATUS', 'snk.GLOBAL_STATUS',
              'src.SCHEDULER_IDLE', 'snk.SCHEDULER_IDLE',
              'src.DESC_ENGINE_IDLE', 'snk.DESC_ENGINE_IDLE'):
        assert seen[k] != 0, (
            f"{k} reads 0 -- the register block's hardware inputs are not "
            f"connected, so this CSR reports nothing. Saw: {seen}")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_perf_window(dut):
    """The data-path perf windows must count, not read zero.

    The RDMON_/WRMON_PERF_* registers existed in the map with nothing driving
    them, so every one read 0 in every build. Each half now has an always-on
    axi_bus_meter behind it: SRC covers the read master, SNK the write master.
    Opens each window through its own CTRL.RUN, requires it to report itself
    active and to accumulate, then closes it.
    """
    tb = RapidsBeatsTopTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    # Closed out of reset: WIN_ACTIVE clear, and WINDOW_CYCLES is live-only.
    assert (await tb.read_reg('src', 'RDMON_PERF_STATUS')) & 1 == 0, \
        "RDMON window reports active before it was opened"
    assert (await tb.read_reg('snk', 'WRMON_PERF_STATUS')) & 1 == 0, \
        "WRMON window reports active before it was opened"

    await tb.write_fields('src', 'RDMON_PERF_CTRL', RUN=1)
    await tb.write_fields('snk', 'WRMON_PERF_CTRL', RUN=1)
    await tb.wait_clocks('aclk', 300)

    rd_status = await tb.read_reg('src', 'RDMON_PERF_STATUS')
    wr_status = await tb.read_reg('snk', 'WRMON_PERF_STATUS')
    rd_cycles = await tb.read_reg('src', 'RDMON_PERF_WINDOW_CYCLES')
    wr_cycles = await tb.read_reg('snk', 'WRMON_PERF_WINDOW_CYCLES')
    rd_bkts = {b: await tb.read_reg('src', f'RDMON_PERF_{b}_CYCLES')
               for b in ('PROD', 'BP', 'STARV', 'IDLE')}
    wr_bkts = {b: await tb.read_reg('snk', f'WRMON_PERF_{b}_CYCLES')
               for b in ('PROD', 'BP', 'STARV', 'IDLE')}
    tb.log.info(f"perf window OPEN: rd status=0x{rd_status:X} cycles={rd_cycles} "
                f"buckets={rd_bkts} | wr status=0x{wr_status:X} "
                f"cycles={wr_cycles} buckets={wr_bkts}")

    assert rd_status & 1, "RDMON_PERF_STATUS.WIN_ACTIVE clear while RUN is set"
    assert wr_status & 1, "WRMON_PERF_STATUS.WIN_ACTIVE clear while RUN is set"
    assert rd_cycles != 0, "RDMON_PERF_WINDOW_CYCLES reads 0 with the window open"
    assert wr_cycles != 0, "WRMON_PERF_WINDOW_CYCLES reads 0 with the window open"
    # With no traffic the cycles land in exactly one of starvation or idle,
    # depending on whether the far end holds its ready high. Measured on this
    # harness: the read channel's rready IS held, so its cycles go to STARV,
    # while the write channel's go to IDLE. Naming one bucket would assert an
    # accident of the slave model, so require the meter to have accumulated
    # SOMETHING -- that is what distinguishes a live meter from a CSR that
    # reads zero because nothing drives it.
    assert sum(rd_bkts.values()) != 0, \
        f"RDMON buckets all zero with the window open: {rd_bkts}"
    assert sum(wr_bkts.values()) != 0, \
        f"WRMON buckets all zero with the window open: {wr_bkts}"

    await tb.write_fields('src', 'RDMON_PERF_CTRL', RUN=0)
    await tb.write_fields('snk', 'WRMON_PERF_CTRL', RUN=0)
    await tb.wait_clocks('aclk', 20)

    assert (await tb.read_reg('src', 'RDMON_PERF_STATUS')) & 1 == 0, \
        "RDMON window still active after RUN was cleared"
    assert (await tb.read_reg('snk', 'WRMON_PERF_STATUS')) & 1 == 0, \
        "WRMON window still active after RUN was cleared"

    tb.finalize_test()


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
    sim_build = sim_build_path(tests_dir, test_name)
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


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_status(request):
    """Status CSR read-back: the fields with real sources must not read 0."""
    _run_top("cocotb_test_status_readback", "test_rapids_beats_top_status")


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_perf_window(request):
    """Perf window: the RDMON/WRMON CSRs must count rather than read 0."""
    _run_top("cocotb_test_perf_window", "test_rapids_beats_top_perf_window")


if __name__ == "__main__":
    class MockRequest:
        pass
    test_rapids_beats_top_source(MockRequest())
    test_rapids_beats_top_sink(MockRequest())
    test_rapids_beats_top_control(MockRequest())
