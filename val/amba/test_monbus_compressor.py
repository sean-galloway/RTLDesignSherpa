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
from TBClasses.shared.utilities import get_paths, create_view_cmd
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
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
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
