# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_compressor
# Purpose: Acceptance test for rtl/amba/monitor/monbus_compressor.sv
#          against the Python golden Encoder in monbus_compressor.py
#          and the real-silicon dataset in
#          projects/NexysA7/stream_characterization/reports/compression_dataset/
#
# Author: sean galloway
# Created: 2026-06-07

"""
Acceptance test for monbus_compressor.

Test plan:
  1. Drive a sequence of (packet, source_ts) records into the RTL.
  2. Capture every 64-bit output slot.
  3. Compare against Python Encoder.encode(records) byte-for-byte.

Data sources:
  - small synthesized hand-crafted streams (deterministic, easy to debug)
  - the real-silicon dataset `desc_axi_16desc_8ch_1MB.json` (682 records)

If the RTL slot stream is byte-identical to the Python golden, the
compressor passes the handoff Step-4 acceptance gate.
"""

import json
import os
import random
from pathlib import Path
from typing import List, Tuple

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.monbus_compressor_tb import MonbusCompressorTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.monbus.monbus_compressor import Encoder
from TBClasses.monbus.sniffer import load_capture


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parents[2]
DATASET_PATH = (REPO_ROOT
                / "projects/NexysA7/stream_characterization"
                / "reports/compression_dataset/desc_axi_16desc_8ch_1MB.json")


def synth_small_stream() -> List[Tuple[int, int]]:
    """A small hand-crafted record stream that exercises every format.

    Sequence reasoning (with CAM cold-start):
      1. cold miss   -> Tier-0 install
      2. same key, small delta_ts, small event_data -> Format A
      3. same key, big delta_ts (>2^15)             -> Format B
      4. same key, event_data delta of +0x10        -> Format A (still small ed)
      5. new cold key                               -> Tier-0 install
    """
    from TBClasses.monbus import (
        create_monitor_packet, PktType, ProtocolType,
        AXIErrorCode, AXIPerformanceCode,
    )
    p_err = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x21, 0xCAFE,
    )
    p_err_2 = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x21, 0xCAFE + 0x10,
    )
    p_perf = create_monitor_packet(
        PktType.PktTypePerf, ProtocolType.PROTOCOL_AXI,
        AXIPerformanceCode.AXI_PERF_TOTAL_LATENCY, 0, 1, 0x11, 0x42,
    )
    return [
        (p_err,   100),
        (p_err,   110),       # small delta_ts, format A
        (p_err,   200_000),   # > 2^15, format B
        (p_err_2, 200_010),   # small delta_ts, event_data changed -> format A
        (p_perf,  200_020),   # new key, tier-0
    ]


# ----------------------------------------------------------------------------
# Testbench
# ----------------------------------------------------------------------------



# ----------------------------------------------------------------------------
# Cocotb test
# ----------------------------------------------------------------------------

@cocotb.test(timeout_time=60, timeout_unit="ms")
async def monbus_compressor_test(dut):
    tb = MonbusCompressorTB(dut)
    await tb.start_clock('clk', 10, 'ns')
    await tb.reset_dut()

    # ---- Phase 0: the credit invariant that prevents a silent drop ----
    # monbus_cam_pipe has NO result_ready -- its result is autonomous -- and
    # the compressor never consults skid_wr_ready. So the ONLY thing stopping
    # a CAM result from arriving at a full skid and vanishing is the credit
    # guard (cam_en requires r_credit < SKID_DEPTH). That invariant is load-
    # bearing and invisible: if a future change raises the credit ceiling
    # without deepening the skid, or deepens the pipeline so more results are
    # in flight, packets are lost with nothing to report it.
    #
    # Assert it directly: whenever the CAM presents a result, the skid must
    # have room for it, checked every cycle across a saturating run.
    #
    # RUNS FIRST, deliberately. Breaking the invariant desyncs the slot
    # stream, so the golden comparison in phase 1 does catch it -- as a
    # four-minute SimTimeoutError with nothing pointing at the cause.
    # Verified by mutation: raising the credit ceiling above SKID_DEPTH
    # hangs phase 1 if this runs after it, and reports the dropped result
    # immediately if it runs before.
    tb.log.info("=== Phase 0: skid always has room for a CAM result ===")
    tb.dut.out_ready.value = 1

    probes = {n: getattr(tb.dut, n, None)
              for n in ('pipe_res_valid', 'skid_wr_ready', 'r_credit')}
    if any(v is None for v in probes.values()):
        missing = [n for n, v in probes.items() if v is None]
        raise AssertionError(
            f"phase 5 cannot run: internal signals not visible {missing}. "
            f"This check must not silently skip -- a skipped assertion is "
            f"decoration. Build with --public-flat-rw or move the invariant "
            f"into an RTL assertion.")

    from TBClasses.monbus import (create_monitor_packet, PktType,
                                  ProtocolType, AXIErrorCode)
    hot = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x21, 0xF00D)
    await tb.drive_record(hot, 500)          # warm the CAM
    await tb.wait_clocks('clk', 8)

    # BACK-PRESSURE THE OUTPUT. With out_ready held high the skid drains as
    # fast as it fills, the credit never approaches its ceiling, and the
    # invariant is never stressed -- an earlier version of this phase ran that
    # way and reported violations=0 even against a deliberately broken credit
    # guard. Stalling the consumer is what backs the skid up and makes a
    # mismatched ceiling produce a result with nowhere to land.
    tb.dut.out_ready.value = 0

    ts = 3000
    tb.dut.in_packet.value = hot
    tb.dut.in_source_ts.value = ts
    tb.dut.in_valid.value = 1
    violations = 0
    max_credit = 0
    for i in range(300):
        # Occasional short drain windows, so the run keeps making progress
        # instead of parking in one steady state.
        tb.dut.out_ready.value = 1 if (i % 16) >= 13 else 0
        await ReadOnly()
        if int(tb.dut.pipe_res_valid.value) and not int(tb.dut.skid_wr_ready.value):
            violations += 1
        max_credit = max(max_credit, int(tb.dut.r_credit.value))
        await RisingEdge(tb.dut.clk)
        ts += 4
        tb.dut.in_source_ts.value = ts
    tb.dut.in_valid.value = 0
    tb.dut.out_ready.value = 1
    await tb.wait_clocks('clk', 10)

    tb.log.info(f"  peak r_credit={max_credit}, result-at-full-skid={violations}")
    assert violations == 0, (
        f"a CAM result was presented on {violations} cycle(s) while the result "
        f"skid was full. monbus_cam_pipe cannot be back-pressured and "
        f"skid_wr_ready is not consulted, so each of those is a SILENTLY "
        f"DROPPED record. The credit guard (r_credit < SKID_DEPTH) is what "
        f"prevents this -- check that the credit ceiling still matches the "
        f"skid depth.")
    tb.log.info("=== Phase 0: PASS ===")

    await tb.reset_dut()

    # ---- Phase 1: small synthesized stream ----
    tb.log.info("=== Phase 1: small synthesized stream ===")
    records = synth_small_stream()
    enc = Encoder()
    expected = list(enc.encode(records))
    tb.log.info(f"  records={len(records)}, golden_slots={len(expected)}")
    await tb.run_records_through(records, expected)
    await tb.verify_stats(enc)
    tb.log.info("=== Phase 1: PASS ===")

    # Reset between phases so the CAM + last_ts start fresh.
    await tb.reset_dut()

    # ---- Phase 2: real-silicon dataset ----
    use_full = os.environ.get('REG_LEVEL', 'FUNC').upper() in ('FUNC', 'FULL')
    if use_full and DATASET_PATH.exists():
        tb.log.info("=== Phase 2: real-silicon dataset ===")
        records = load_capture(str(DATASET_PATH))
        enc = Encoder()
        expected = list(enc.encode(records))
        tb.log.info(f"  records={len(records)}, golden_slots={len(expected)}")
        await tb.run_records_through(records, expected)
        await tb.verify_stats(enc)
        tb.log.info(f"  rtl_a={enc.stats.tier1_a_hits}, "
                    f"rtl_b={enc.stats.tier1_b_hits}, "
                    f"rtl_c={enc.stats.tier1_c_hits}, "
                    f"tier0={enc.stats.tier0_escapes}")
        tb.log.info("=== Phase 2: PASS ===")
    elif not DATASET_PATH.exists():
        tb.log.info("=== Phase 2: SKIPPED (dataset not present) ===")

    # ---- Phase 3: synchronous CAM clear ----
    # Populate the CAM + stats, pulse `clear`, and verify (a) all stat counters
    # zero and (b) a key that hit before now MISSES -- i.e. the template CAM was
    # actually emptied, not just the stats.
    tb.log.info("=== Phase 3: synchronous CAM clear ===")
    await tb.reset_dut()
    s3 = synth_small_stream()
    tb.dut.out_ready.value = 1
    for pkt, ts in s3:
        await tb.drive_record(pkt, ts)
    await tb.wait_clocks('clk', 5)
    await ReadOnly()
    pre = (int(tb.dut.stat_tier1_a.value) + int(tb.dut.stat_tier1_c.value)
           + int(tb.dut.stat_tier0.value))
    await RisingEdge(tb.dut.clk)
    assert pre > 0, "Phase 3: expected nonzero stats before clear"

    # Pulse clear for one cycle.
    tb.dut.clear.value = 1
    await RisingEdge(tb.dut.clk)
    tb.dut.clear.value = 0
    await RisingEdge(tb.dut.clk)
    await ReadOnly()
    for sig in ('stat_tier1_a', 'stat_tier1_b', 'stat_tier1_c', 'stat_tier0',
                'stat_cam_miss'):
        assert int(getattr(tb.dut, sig).value) == 0, \
            f"Phase 3: {sig} not cleared (= {int(getattr(tb.dut, sig).value)})"
    await RisingEdge(tb.dut.clk)

    # A previously-hit key must now be a fresh CAM miss (CAM emptied).
    await tb.drive_record(s3[0][0], s3[0][1] + 1000)
    await tb.wait_clocks('clk', 5)
    await ReadOnly()
    assert int(tb.dut.stat_cam_miss.value) == 1, \
        ("Phase 3: post-clear record should be a fresh CAM miss "
         f"(cam_miss={int(tb.dut.stat_cam_miss.value)}) -- CAM not emptied")
    await RisingEdge(tb.dut.clk)
    tb.log.info("=== Phase 3 (CAM clear): PASS ===")

    # ---- Phase 4: sustained Tier-1 input throughput ----
    # MEASURED, not asserted from the pipeline diagram. Both the RTL header
    # ("Throughput is unchanged: Tier-1 records: 1 record/cycle") and the doc
    # claim one record per cycle; qc round_24 argued on paper that the
    # credit-gated result skid caps it lower, because a credit is only
    # returned when the registered skid output is popped:
    #   present at T -> CAM result T+1 -> registered rd_valid T+2 -> pop T+2
    #   -> credit visible T+3, with only SKID_DEPTH=2 credits in flight.
    # This phase settles it by holding in_valid high across a long run of
    # same-template records (all Tier-1 hits after the first) and counting
    # actual input handshakes per cycle.
    tb.log.info("=== Phase 4: sustained Tier-1 input rate ===")
    await tb.reset_dut()
    tb.dut.out_ready.value = 1

    from TBClasses.monbus import (
        create_monitor_packet, PktType, ProtocolType, AXIErrorCode,
    )
    p_hot = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x21, 0xBEEF,
    )

    # Warm the CAM so every measured record is a Tier-1 hit, not an install.
    await tb.drive_record(p_hot, 1000)
    await tb.wait_clocks('clk', 8)

    N_CYCLES = 200
    ts = 2000
    handshakes = 0
    tb.dut.in_packet.value = p_hot
    tb.dut.in_source_ts.value = ts
    tb.dut.in_valid.value = 1
    for _ in range(N_CYCLES):
        await ReadOnly()
        took = int(tb.dut.in_ready.value) == 1
        await RisingEdge(tb.dut.clk)
        if took:
            handshakes += 1
            ts += 4                       # small delta -> stays Format A
            tb.dut.in_source_ts.value = ts
    tb.dut.in_valid.value = 0
    await tb.wait_clocks('clk', 10)

    rate = handshakes / N_CYCLES
    tb.log.info(f"  sustained Tier-1 input rate: {handshakes}/{N_CYCLES} "
                f"= {rate:.3f} records/cycle")

    # MEASURED 2026-08-27: 200/200 = 1.000 at SKID_DEPTH=3 (AMBA-COMPTP).
    #
    # History worth keeping, because it is what this assertion defends: the
    # RTL header and docs claimed 1 record/cycle for a long time while the
    # hardware did 0.67 (134/200). The credit round trip is 3 cycles --
    # present T, CAM result T+1, registered skid rd_valid and pop T+2, credit
    # visible T+3 -- so N credits sustain N/3 records/cycle. SKID_DEPTH was 2.
    # Raising it to 3 gives exactly 1.0, and the input handshake caps it there.
    #
    # A LOWER bound only. There is no upper bound to trip now: 1.0 is the
    # ceiling the handshake imposes, so anything below it is a regression and
    # nothing can legitimately exceed it. If this ever drops, check
    # SKID_DEPTH against the credit round trip before anything else.
    assert rate >= 0.98, (
        f"sustained Tier-1 input rate is {rate:.3f} records/cycle "
        f"({handshakes} handshakes in {N_CYCLES} cycles); expected ~1.0 at "
        f"SKID_DEPTH=3. N credits sustain N/3 records/cycle against the "
        f"3-cycle credit round trip, so a drop here usually means SKID_DEPTH "
        f"was reduced or the round trip grew. Update monbus_compressor.sv's "
        f"header, monbus_compressor.md and this bound together.")
    tb.log.info(f"=== Phase 4: PASS (rate={rate:.3f}) ===")

    tb.log.info("=== ALL PHASES PASSED ===")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------

def test_monbus_compressor(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_includes': 'rtl/amba/includes',
    })

    dut_name = "monbus_compressor"
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_{reg_level}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/monbus_compressor.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    extra_env = {
        'DUT':              dut_name,
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':             os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_CLK_PERIOD':  '10',
    }

    compile_args = [
        '+define+SIMULATION',
        '--trace-fst', '--trace-structs',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module=module,
            sim_build=sim_build,
            parameters={},  # CAM is always pipelined (parameter removed)
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"Test failed: {e}")
        print(f"Logs: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
