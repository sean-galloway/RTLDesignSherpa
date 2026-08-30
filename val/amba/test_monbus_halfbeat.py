# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Purpose: Acceptance test for the half-beat packing path
#          (rtl/amba/monitor/monbus_compressor.sv HALF_BEAT_EN=1 +
#           monbus_halfbeat_packer.sv) against the Python golden
#           Encoder(half_beat=True) in monbus_compressor.py.
#
#   1. Drive a record stream GAP-FREE (in_valid held continuous) so the
#      packer only flushes its lone trailing half at end-of-stream, exactly
#      like the golden's encode() end-flush.
#   2. Capture the 64-bit beats out.
#   3. Compare against Encoder(half_beat=True).encode(records) byte-for-byte.

import os
import random
from pathlib import Path
from typing import List, Tuple

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.monbus_halfbeat_tb import MonbusHalfbeatTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.monbus.monbus_compressor import Encoder
from TBClasses.monbus.sniffer import load_capture

REPO_ROOT = Path(__file__).resolve().parents[2]
# DATASET_OVERRIDE lets the bit-exact RTL-vs-golden check be pointed at any
# captured (packet, timestamp) stream (e.g. a per-run capture_raw_trace dump)
# to recreate a specific on-silicon scenario in simulation.
DATASET_PATH = Path(os.environ.get("DATASET_OVERRIDE", str(
                REPO_ROOT
                / "projects/fpga-systems/Genesys2/stream/reports/compression/json"
                / "desc_axi_16desc_8ch_1MB.json")))


def synth_small_stream() -> List[Tuple[int, int]]:
    """Exercises half-A (small abs data), half-C (small ed delta), full
    fallbacks and raw escapes — and an odd count so a lone half is flushed."""
    from TBClasses.monbus import (
        create_monitor_packet, PktType, ProtocolType,
        AXIErrorCode, AXIPerformanceCode,
    )
    p_err = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x21, 0x100,
    )
    p_err_d = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x21, 0x120,   # +0x20 ed delta
    )
    p_perf = create_monitor_packet(
        PktType.PktTypePerf, ProtocolType.PROTOCOL_AXI,
        AXIPerformanceCode.AXI_PERF_TOTAL_LATENCY, 0, 1, 0x11, 0x42,
    )
    return [
        (p_err,   100),
        (p_err,   110),       # half-A (small delta, small abs data)
        (p_err_d, 120),       # half-C (small delta, small ed delta)
        (p_err,   130),       # half-C (ed delta back -0x20)
        (p_perf,  140),       # new key -> raw (flushes pending half first)
        (p_perf,  150),       # half-A
    ]




@cocotb.test(timeout_time=120, timeout_unit="ms")
async def monbus_halfbeat_test(dut):
    tb = MonbusHalfbeatTB(dut)
    await tb.start_clock('clk', 10, 'ns')

    # ---- Phase 1: small synthesized stream ----
    await tb.reset_dut()
    tb.log.info("=== Phase 1: small synthesized stream ===")
    records = synth_small_stream()
    enc = Encoder(half_beat=True)
    expected = list(enc.encode(records))    # encode() flushes the trailing half
    tb.log.info(f"  records={len(records)}, golden_beats={len(expected)}")
    await tb.run_records_through(records, expected)
    await tb.verify_stats(enc)
    tb.log.info("=== Phase 1: PASS ===")

    # ---- Phase 2: real-silicon dataset ----
    use_full = os.environ.get('REG_LEVEL', 'FUNC').upper() in ('FUNC', 'FULL')
    if use_full and DATASET_PATH.exists():
        await tb.reset_dut()
        tb.log.info("=== Phase 2: real-silicon dataset ===")
        records = load_capture(str(DATASET_PATH))
        enc = Encoder(half_beat=True)
        expected = list(enc.encode(records))
        tb.log.info(f"  records={len(records)}, golden_beats={len(expected)}")
        await tb.run_records_through(records, expected)
        await tb.verify_stats(enc)
        tb.log.info("=== Phase 2: PASS ===")
    elif not DATASET_PATH.exists():
        tb.log.info("=== Phase 2: SKIPPED (dataset not present) ===")

    tb.log.info("=== ALL PHASES PASSED ===")


def test_monbus_halfbeat(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_includes': 'rtl/amba/includes',
        'val_amba':     'val/amba',
    })

    dut_name = "monbus_halfbeat_dut"
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
        filelist_path="rtl/amba/filelists/monbus_halfbeat_dut.f")
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
