# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_compressor
# Purpose: Acceptance test for rtl/amba/shared/monbus_compressor.sv
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
from TBClasses.shared.utilities import get_paths, create_view_cmd
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

class MonbusCompressorTB(TBBase):
    """Drive records in, capture slots out, cross-check against Python golden."""

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        self.captured_slots: List[int] = []

    async def reset_dut(self):
        self.dut.in_valid.value     = 0
        self.dut.in_packet.value    = 0
        self.dut.in_source_ts.value = 0
        self.dut.out_ready.value    = 1
        self.dut.rst_n.value        = 0
        await self.wait_clocks('clk', 5)
        self.dut.rst_n.value        = 1
        await self.wait_clocks('clk', 2)
        self.captured_slots.clear()

    async def drive_record(self, packet: int, source_ts: int):
        """Drive a single record through the valid/ready handshake.

        Pattern: assert valid, sample in_ready at ReadOnly (pre-edge),
        loop until ready is high, then advance ONE edge (handshake
        fires at that edge) and deassert valid immediately so the
        same record isn't double-handshook on subsequent IDLE cycles.
        """
        self.dut.in_packet.value    = packet
        self.dut.in_source_ts.value = source_ts
        self.dut.in_valid.value     = 1
        while True:
            await ReadOnly()
            if int(self.dut.in_ready.value) == 1:
                break
            await RisingEdge(self.dut.clk)
        # Next rising edge handshakes; deassert valid immediately after.
        await RisingEdge(self.dut.clk)
        self.dut.in_valid.value = 0

    async def capture_loop(self, n_slots_expected: int):
        """Sample one slot per cycle whenever out_valid && out_ready."""
        while len(self.captured_slots) < n_slots_expected:
            await ReadOnly()
            if (int(self.dut.out_valid.value) == 1
                    and int(self.dut.out_ready.value) == 1):
                self.captured_slots.append(int(self.dut.out_slot.value))
            await RisingEdge(self.dut.clk)

    async def run_records_through(self,
                                  records: List[Tuple[int, int]],
                                  expected_slots: List[int]):
        """Drive all records and assert the captured slots match exactly."""
        # Always ready to absorb outputs (no backpressure).
        self.dut.out_ready.value = 1
        # Start the capture in parallel with the driver.
        cap = cocotb.start_soon(self.capture_loop(len(expected_slots)))
        for pkt, ts in records:
            await self.drive_record(pkt, ts)
        # Wait for the capture to finish (or time out).
        await cap
        # Compare lengths first, then slot-by-slot.
        assert len(self.captured_slots) == len(expected_slots), (
            f"slot count mismatch: rtl={len(self.captured_slots)}, "
            f"golden={len(expected_slots)}"
        )
        for i, (rtl, golden) in enumerate(zip(self.captured_slots, expected_slots)):
            assert rtl == golden, (
                f"slot {i} mismatch: rtl=0x{rtl:016x}, golden=0x{golden:016x}"
            )

    async def verify_stats(self, enc: Encoder):
        """After all records drive through, the RTL's stat counters
        should match the Python encoder's per-tier counts."""
        await ReadOnly()
        rtl_a    = int(self.dut.stat_tier1_a.value)
        rtl_b    = int(self.dut.stat_tier1_b.value)
        rtl_c    = int(self.dut.stat_tier1_c.value)
        rtl_t0   = int(self.dut.stat_tier0.value)
        assert rtl_a  == enc.stats.tier1_a_hits, \
            f"tier1_a mismatch: rtl={rtl_a}, py={enc.stats.tier1_a_hits}"
        assert rtl_b  == enc.stats.tier1_b_hits, \
            f"tier1_b mismatch: rtl={rtl_b}, py={enc.stats.tier1_b_hits}"
        assert rtl_c  == enc.stats.tier1_c_hits, \
            f"tier1_c mismatch: rtl={rtl_c}, py={enc.stats.tier1_c_hits}"
        assert rtl_t0 == enc.stats.tier0_escapes, \
            f"tier0 mismatch: rtl={rtl_t0}, py={enc.stats.tier0_escapes}"
        # Leave the ReadOnly phase so the next phase can drive signals.
        await RisingEdge(self.dut.clk)


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

    tb.log.info("=== ALL PHASES PASSED ===")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------

def test_monbus_compressor(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_includes': 'rtl/amba/includes',
    })

    dut_name = "monbus_compressor"
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name = f"test_{dut_name}_{reg_level}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba5_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_cam.sv"),
        os.path.join(rtl_dict['rtl_shared'],   f"{dut_name}.sv"),
    ]
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
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module=module,
            sim_build=sim_build,
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
