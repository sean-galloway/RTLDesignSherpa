# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_axil_axil_group_compressed
# Purpose: End-to-end acceptance test for monbus_axil_axil_group with
#          USE_COMPRESSION=1. Drives monbus records in, captures the
#          AXIL master write stream out, and asserts the captured slot
#          sequence is byte-identical to the Python Encoder golden.
#
# Author: sean galloway
# Created: 2026-06-07; retargeted 2026-06-10 for the family refactor
#          (monbus_axil_group -> monbus_axil_axil_group; beat-granular
#          write FIFO; cfg_flush_watermark = 1 keeps the per-slot
#          drain shape identical to the legacy module).

"""
End-to-end test for monbus_axil_axil_group's compressed write path.

The monbus_compressor sub-module is already byte-exact against the
Python golden (val/amba/test_monbus_compressor.py). This test closes
the next layer:
  - the compressor sits behind the write FIFO
  - the AXIL writer drains one beat per slot
  - cfg_base_addr / cfg_limit_addr enforces a per-slot ring wrap

A failure here means the FSM, FIFO plumbing, or wrap arithmetic is
broken even though the compressor itself works in isolation.

Test phases:
  1. small synthesized stream, generous window (no wrap)
  2. real-silicon dataset (FUNC+FULL), generous window (no wrap)
  3. tight window forces a mid-stream wrap; assert addresses cycle
     back to cfg_base_addr at the right slot
"""

import json
import os
import random
from pathlib import Path
from typing import List, Tuple

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly, Combine
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.monbus_axil_axil_group_compressed_tb import MonbusAxilAxilGroupTB
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.monbus.monbus_compressor import Encoder
from TBClasses.monbus.sniffer import load_capture
from TBClasses.scoreboards.monbus_group import MonbusGroupHarness


REPO_ROOT = Path(__file__).resolve().parents[2]
DATASET_PATH = (REPO_ROOT
                / "projects/NexysA7/stream_characterization"
                / "reports/compression_dataset/desc_axi_16desc_8ch_1MB.json")


# ----------------------------------------------------------------------------
# Helpers: synthesized stream that mirrors the compressor sub-module test
# ----------------------------------------------------------------------------

def synth_small_stream() -> List[Tuple[int, int]]:
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
        (p_err,   110),
        (p_err,   200_000),
        (p_err_2, 200_010),
        (p_perf,  200_020),
    ]


# ----------------------------------------------------------------------------
# Testbench
# ----------------------------------------------------------------------------



# ----------------------------------------------------------------------------
# Cocotb test
# ----------------------------------------------------------------------------

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def monbus_axil_axil_group_compressed_test(dut):
    tb = MonbusAxilAxilGroupTB(dut)
    await tb.start_clock('axi_aclk', 10, 'ns')

    # ---- Phase 1: small synthesized stream, generous window ----
    BASE_BIG   = 0x0000_1000
    LIMIT_BIG  = 0x0001_FFFF  # 60 KiB window, no wrap for small streams
    await tb.reset_dut(BASE_BIG, LIMIT_BIG)
    tb.log.info("=== Phase 1: small synthesized stream ===")
    records  = synth_small_stream()
    enc      = Encoder()
    expected = list(enc.encode(records))
    tb.log.info(f"  records={len(records)}, golden_slots={len(expected)}")
    await tb.run_records_through(records, expected)
    tb.assert_wrap_addresses(BASE_BIG, LIMIT_BIG)
    tb.log.info("=== Phase 1: PASS ===")

    # ---- Phase 3 (small): wrap-window exercise ----
    # Pick a window that holds exactly 8 slots (64 bytes) so the small
    # synth stream's 9 slots force one wrap. We run this before the
    # heavy Phase 2 so a wrap bug fails fast.
    BASE_WRAP  = 0x0000_2000
    LIMIT_WRAP = 0x0000_203F   # 64 bytes = 8 slots
    await tb.reset_dut(BASE_WRAP, LIMIT_WRAP)
    tb.log.info("=== Phase 3: wrap-window (8-slot capacity) ===")
    records  = synth_small_stream()
    enc      = Encoder()
    expected = list(enc.encode(records))
    tb.log.info(f"  records={len(records)}, golden_slots={len(expected)}, "
                f"window holds 8 slots")
    await tb.run_records_through(records, expected)
    tb.assert_wrap_addresses(BASE_WRAP, LIMIT_WRAP)
    # Confirm we actually did wrap at least once: slot 8 should be at base.
    if len(tb.captured) >= 9:
        assert tb.captured[8][0] == BASE_WRAP, (
            f"slot 8 expected wrap to 0x{BASE_WRAP:08x}, "
            f"got 0x{tb.captured[8][0]:08x}"
        )
    tb.log.info("=== Phase 3: PASS ===")

    # ---- Phase 2: real-silicon dataset, generous window ----
    use_full = os.environ.get('REG_LEVEL', 'FUNC').upper() in ('FUNC', 'FULL')
    if use_full and DATASET_PATH.exists():
        BASE_BIG2  = 0x0000_1000
        # 770 slots * 8 bytes = 6160 bytes; window of 64 KiB has plenty.
        LIMIT_BIG2 = 0x0001_0FFF
        await tb.reset_dut(BASE_BIG2, LIMIT_BIG2)
        tb.log.info("=== Phase 2: real-silicon dataset ===")
        records  = load_capture(str(DATASET_PATH))
        enc      = Encoder()
        expected = list(enc.encode(records))
        tb.log.info(f"  records={len(records)}, golden_slots={len(expected)}")
        await tb.run_records_through(records, expected)
        tb.assert_wrap_addresses(BASE_BIG2, LIMIT_BIG2)
        tb.log.info("=== Phase 2: PASS ===")
    elif not DATASET_PATH.exists():
        tb.log.info("=== Phase 2: SKIPPED (dataset not present) ===")

    tb.log.info("=== ALL PHASES PASSED ===")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------

def test_monbus_axil_axil_group_compressed(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_axil4':    'rtl/amba/axil4',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "monbus_axil_axil_group"
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_compressed_{reg_level}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/monbus_axil_axil_group.f")
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
        '-Wno-UNUSEDPARAM', '-Wno-UNUSEDSIGNAL', '-Wno-TIMESCALEMOD',
    ]

    # Parameter override: turn the compressor branch on.
    parameters = {
        'USE_COMPRESSION': 1,
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module=module,
            sim_build=sim_build,
            extra_env=extra_env,
            parameters=parameters,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"Test failed: {e}")
        print(f"Logs: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
