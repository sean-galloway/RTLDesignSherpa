# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_dma_observer
# Purpose: Smoke test for the standalone axi4_dma_observer wrapper.
#
# Author: sean galloway
# Created: 2026-06-13

"""
Smoke test for `rtl/amba/shared/axi4_dma_observer.sv` — the standalone
DMA-agnostic observability wrapper. Validates:

  1. Pass-through correctness on the read tap (DMA-side AR <-> fabric-side
     AR, fabric-side R <-> DMA-side R; data + length + ID preserved).
  2. Pass-through correctness on the write tap (AW + W + B).
  3. Monbus aggregation produces master-write activity on the dump port
     once enough transactions have been observed (watermark-driven flush).

This is one-port-each (NUM_RD_PORTS=1, NUM_WR_PORTS=1) — the simplest
shape. Multi-port and protocol-variant coverage is future work.
"""

import os
import random
from typing import List

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly, Combine
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.axi4_dma_observer_tb import Axi4DmaObserverTB
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


# ---------------------------------------------------------------------
# AXI4 master-side stimulus + AXI4 slave-side responder
# ---------------------------------------------------------------------
#
# Naming convention for ports (when the observer is between DMA and fabric):
#   dma_rd_* / dma_wr_*  : the DMA side of the observer (we drive from here)
#   fab_rd_* / fab_wr_*  : the fabric side (we model an AXI4 slave here)
#   m_axi_* / s_axil_*   : the observer's own dump + IRQ-FIFO ports
# ---------------------------------------------------------------------




@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_axi4_dma_observer(dut):
    tb = Axi4DmaObserverTB(dut)
    await tb.start_clock('aclk', 10, 'ns')

    # ---------------- Phase 1: Read pass-through ----------------
    tb.log.info("=== Phase 1: read pass-through ===")
    BASE  = 0x0000_2000
    LIMIT = 0x0000_5FFF
    # Set watermark high so the dump port stays quiet during this phase.
    await tb.reset_dut(BASE, LIMIT, flush_watermark=1024)

    n_reads = 4
    responder = cocotb.start_soon(tb._fab_rd_responder(n_reads))
    for i in range(n_reads):
        await tb.dma_read(addr=0x10000 + 16 * i, arid=(i & 0xF) + 1)
    await Combine(responder)

    assert len(tb.fab_seen_ar) == n_reads, (
        f"Phase 1: fabric saw {len(tb.fab_seen_ar)} ARs, expected {n_reads}"
    )
    for i, addr in enumerate(tb.fab_seen_ar):
        assert addr == 0x10000 + 16 * i, (
            f"Phase 1: AR {i} mismatch: got 0x{addr:08x}"
        )
    # Each R came back with data = 0xDEADBEEF00000000 | addr
    assert len(tb.dma_seen_r) == n_reads
    for i, data in enumerate(tb.dma_seen_r):
        expected = 0xDEADBEEF00000000 | (0x10000 + 16 * i)
        assert data == expected, (
            f"Phase 1: R {i} mismatch: got 0x{data:032x}, expected 0x{expected:032x}"
        )
    tb.log.info(f"  {n_reads} reads passed through cleanly")

    # ---------------- Phase 2: Write pass-through ----------------
    tb.log.info("=== Phase 2: write pass-through ===")
    await tb.reset_dut(BASE, LIMIT, flush_watermark=1024)

    n_writes = 4
    responder = cocotb.start_soon(tb._fab_wr_responder(n_writes))
    for i in range(n_writes):
        await tb.dma_write(addr=0x20000 + 16 * i, data=0xCAFEBABE_00000000 | i,
                           awid=(i & 0xF) + 1)
    await Combine(responder)

    assert len(tb.fab_seen_aw) == n_writes
    for i, addr in enumerate(tb.fab_seen_aw):
        assert addr == 0x20000 + 16 * i
    assert len(tb.fab_seen_w) == n_writes
    for i, data in enumerate(tb.fab_seen_w):
        expected = 0xCAFEBABE_00000000 | i
        assert data == expected
    assert len(tb.dma_seen_b) == n_writes
    tb.log.info(f"  {n_writes} writes passed through cleanly")

    # ---------------- Phase 3: monbus dump activity ----------------
    tb.log.info("=== Phase 3: monbus dump activity ===")
    # Low watermark: every completed record should trigger a flush.
    BEATS_PER_RECORD = 3
    n_xfers = 4
    expected_min_records = n_xfers * 2  # at least one completion per read + per write
    expected_min_beats = expected_min_records * BEATS_PER_RECORD

    await tb.reset_dut(BASE, LIMIT, flush_watermark=BEATS_PER_RECORD)

    fab_rd_task   = cocotb.start_soon(tb._fab_rd_responder(n_xfers))
    fab_wr_task   = cocotb.start_soon(tb._fab_wr_responder(n_xfers))
    dump_task     = cocotb.start_soon(tb._dump_capture(expected_min_beats))

    # Interleave reads and writes
    for i in range(n_xfers):
        await tb.dma_read(addr=0x30000 + 16 * i, arid=(i & 0xF) + 1)
        await tb.dma_write(addr=0x40000 + 16 * i, data=0xA5A5_0000 | i,
                           awid=(i & 0xF) + 1)

    await Combine(fab_rd_task)
    await Combine(fab_wr_task)
    # Give the dump pipeline time to drain
    await tb.wait_clocks('aclk', 1000)
    # Don't wait forever for the dump task to complete; just check what
    # we got.
    n_dump_beats = len(tb.dump_w)
    n_dump_aws   = len(tb.dump_aw)
    tb.log.info(f"  dump port: {n_dump_aws} AWs, {n_dump_beats} W beats")

    assert n_dump_beats >= BEATS_PER_RECORD, (
        f"Phase 3: expected at least {BEATS_PER_RECORD} dump beats "
        f"(one full record), got {n_dump_beats}. The observer is not "
        f"emitting any master-write activity."
    )
    # Each captured AW address should be within the configured window
    for i, addr in enumerate(tb.dump_aw):
        assert BASE <= addr <= LIMIT, (
            f"Phase 3: dump AW {i} addr 0x{addr:08x} outside window "
            f"[0x{BASE:08x}, 0x{LIMIT:08x}]"
        )

    tb.log.info(f"  observer captured >= 1 record's worth of dump beats")

    # ---------------- Phase 4: bus_meter counters ----------------
    tb.log.info("=== Phase 4: bus_meter counters ===")
    # By the time Phase 3 completes, we've issued real R + W traffic
    # through the observer. Read the aggregate counters and assert that
    # productive cycles fired on both sides.
    rd_prod = int(tb.dut.rd_meter_agg_productive[0].value)
    rd_idle = int(tb.dut.rd_meter_agg_idle[0].value)
    wr_prod = int(tb.dut.wr_meter_agg_productive[0].value)
    wr_idle = int(tb.dut.wr_meter_agg_idle[0].value)
    tb.log.info(f"  rd meter: productive={rd_prod}, idle={rd_idle}")
    tb.log.info(f"  wr meter: productive={wr_prod}, idle={wr_idle}")
    assert rd_prod >= n_xfers, (
        f"rd meter: expected >= {n_xfers} productive cycles, got {rd_prod}"
    )
    assert wr_prod >= n_xfers, (
        f"wr meter: expected >= {n_xfers} productive cycles, got {wr_prod}"
    )
    # AW->W tracker (WR_CH_FROM_AWID=1): write beats are attributed per-channel
    # from awid, so the per-channel productive buckets should be populated and
    # sum to no more than the aggregate (a beat is attributed to at most one
    # channel; the first beat of a burst may be unattributed if W lands the same
    # cycle its AW is accepted, so this is `<= wr_prod`, not `==`).
    try:
        wr_ch_sum = sum(int(tb.dut.wr_meter_ch_productive[0][ch].value)
                        for ch in range(8))
        tb.log.info(f"  wr per-channel productive sum (awid tracker)={wr_ch_sum}")
        assert 0 < wr_ch_sum <= wr_prod, (
            f"wr AW->W tracker: per-channel sum {wr_ch_sum} not in (0, {wr_prod}]"
        )
    except (AttributeError, IndexError) as e:
        tb.log.warning(f"  per-channel write readback skipped: {e}")
    # Per-channel attribution: with the identity rid->channel map and arids
    # 1..n_xfers, channels 0..(n_xfers-1) should each show one productive
    # cycle on the read side. (This is a soft check -- skip if the array
    # index isn't reachable.)
    try:
        for ch in range(n_xfers):
            rd_ch_prod = int(tb.dut.rd_meter_ch_productive[0][ch].value)
            tb.log.info(f"  rd ch[{ch}]: productive={rd_ch_prod}")
            assert rd_ch_prod >= 1, (
                f"rd ch[{ch}]: expected >= 1 productive (arid={ch+1}), "
                f"got {rd_ch_prod}"
            )
    except (AttributeError, IndexError) as e:
        tb.log.warning(f"  per-channel readback skipped: {e}")

    tb.log.info("=== ALL PHASES PASSED ===")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------

def test_axi4_dma_observer(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_axil4':    'rtl/amba/axil4',
        'rtl_axi4':     'rtl/amba/axi4',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "axi4_dma_observer"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_smoke"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi4_dma_observer.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    parameters = {
        'NUM_RD_PORTS':         1,
        'NUM_WR_PORTS':         1,
        'ADDR_WIDTH':           32,
        'DATA_WIDTH':           128,
        'AXI_ID_WIDTH':         4,
        'AXI_USER_WIDTH':       1,
        'OBS_AXI_ID_WIDTH':     1,
        'MAX_BURST_BEATS':      64,
        'FLUSH_TIMEOUT_CYCLES': 200,
        'USE_COMPRESSION':      0,
        'ENABLE_BUS_METER':     1,
        'NUM_CHANNELS':         8,
        # Exercise the AW->W order tracker: derive write per-channel attribution
        # from awid (the driver issues awid=(i&0xF)+1) instead of the sideband.
        'WR_CH_FROM_AWID':      1,
        # The synthesized characterization instances default the observer taps to
        # perf-only (fits the xc7a100t). This unit test exercises the monbus dump
        # path (Phase 3), which is completion-driven, so enable the completion
        # cone here. Perf stays on for the bus_meter/histogram checks.
        'TAP_ENABLE_COMPL_LOGIC': 1,
        'TAP_ENABLE_PERF_LOGIC':  1,
    }

    extra_env = {
        'DUT':              dut_name,
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':             os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    compile_args = [
        '+define+SIMULATION',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-UNUSEDSIGNAL', '-Wno-TIMESCALEMOD',
        '-Wno-PINCONNECTEMPTY',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module='test_axi4_dma_observer',
            testcase="cocotb_test_axi4_dma_observer",
            sim_build=sim_build,
            extra_env=extra_env,
            parameters=parameters,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ axi4_dma_observer smoke test PASSED! Logs: {log_path}")
    except Exception as e:
        print(f"✗ axi4_dma_observer smoke test FAILED: {e}")
        print(f"Logs: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
