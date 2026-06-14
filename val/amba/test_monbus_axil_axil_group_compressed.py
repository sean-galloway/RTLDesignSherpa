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
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.monbus.monbus_compressor import Encoder
from TBClasses.monbus.sniffer import load_capture


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

class MonbusAxilAxilGroupTB(TBBase):
    """Drive records into the monbus input, capture every AXIL write
    on the master interface, and compare against the Python golden."""

    SLOT_STRIDE = 8

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        # Captured (addr, data) per completed AXIL B response.
        self.captured: List[Tuple[int, int]] = []
        # Tracks pending AW (addrs) and W (data) until paired up by B.
        self._aw_q: List[int] = []
        self._w_q: List[int] = []

    # ---------- setup / reset ----------

    def _tie_off_config(self):
        """Disable all dropping and all err-FIFO routing so every monbus
        packet lands in the write FIFO, feeding the compressor."""
        # Drop masks = 0, err_select = 0, event masks = 0.
        for sig in (
            'cfg_axi_pkt_mask', 'cfg_axi_err_select', 'cfg_axi_error_mask',
            'cfg_axi_timeout_mask', 'cfg_axi_compl_mask', 'cfg_axi_thresh_mask',
            'cfg_axi_perf_mask', 'cfg_axi_addr_mask', 'cfg_axi_debug_mask',
            'cfg_axis_pkt_mask', 'cfg_axis_err_select', 'cfg_axis_error_mask',
            'cfg_axis_timeout_mask', 'cfg_axis_compl_mask', 'cfg_axis_credit_mask',
            'cfg_axis_channel_mask', 'cfg_axis_stream_mask',
            'cfg_core_pkt_mask', 'cfg_core_err_select', 'cfg_core_error_mask',
            'cfg_core_timeout_mask', 'cfg_core_compl_mask', 'cfg_core_thresh_mask',
            'cfg_core_perf_mask', 'cfg_core_debug_mask',
        ):
            getattr(self.dut, sig).value = 0

    async def reset_dut(self, base_addr: int, limit_addr: int):
        self.dut.monbus_valid.value     = 0
        self.dut.monbus_packet.value    = 0
        self.dut.monbus_timestamp.value = 0
        # s_axil slave read interface unused -- we never drain the err FIFO,
        # but with err_select=0 the err FIFO never fills anyway.
        self.dut.s_axil_arvalid.value = 0
        self.dut.s_axil_araddr.value  = 0
        self.dut.s_axil_arprot.value  = 0
        self.dut.s_axil_rready.value  = 0
        # AXIL master write slave model (we behave as the memory side).
        self.dut.m_axil_awready.value = 0
        self.dut.m_axil_wready.value  = 0
        self.dut.m_axil_bvalid.value  = 0
        self.dut.m_axil_bresp.value   = 0
        # Window.
        self.dut.cfg_base_addr.value  = base_addr
        self.dut.cfg_limit_addr.value = limit_addr
        # Eagerly flush every slot so this slot-by-slot golden compare
        # works the same way it did against the pre-family monolithic
        # writer. With a beat-granular FIFO, watermark=1 means a single
        # compressed-mode slot in the FIFO triggers a flush immediately.
        self.dut.cfg_flush_watermark.value = 1
        # Compression is now runtime-selected; this group is built with the
        # compressor hardware present (USE_COMPRESSION=1), so enable it.
        self.dut.cfg_compress_en.value = 1
        self._tie_off_config()
        # Reset pulse.
        self.dut.axi_aresetn.value = 0
        await self.wait_clocks('axi_aclk', 5)
        self.dut.axi_aresetn.value = 1
        await self.wait_clocks('axi_aclk', 2)
        self.captured.clear()
        self._aw_q.clear()
        self._w_q.clear()

    # ---------- monbus driver (input side) ----------

    async def drive_record(self, packet: int, source_ts: int):
        """Same pre-edge ReadOnly handshake pattern as the compressor
        test, so a single record cannot be double-handshook."""
        self.dut.monbus_packet.value    = packet
        self.dut.monbus_timestamp.value = source_ts
        self.dut.monbus_valid.value     = 1
        while True:
            await ReadOnly()
            if int(self.dut.monbus_ready.value) == 1:
                break
            await RisingEdge(self.dut.axi_aclk)
        await RisingEdge(self.dut.axi_aclk)
        self.dut.monbus_valid.value = 0

    # ---------- AXIL slave model (output side) ----------

    async def _aw_handler(self, stop_after: int):
        """Always-ready AW capture. Pushes each captured awaddr into
        the pending AW queue; gives up once we've captured >= stop_after
        AW handshakes (slot count budget)."""
        self.dut.m_axil_awready.value = 1
        seen = 0
        while seen < stop_after:
            await ReadOnly()
            if (int(self.dut.m_axil_awvalid.value) == 1
                    and int(self.dut.m_axil_awready.value) == 1):
                self._aw_q.append(int(self.dut.m_axil_awaddr.value))
                seen += 1
            await RisingEdge(self.dut.axi_aclk)
        # One extra cycle of awready high to let any in-flight handshake
        # settle, then drop it so the compressor backpressures gracefully.
        await RisingEdge(self.dut.axi_aclk)
        self.dut.m_axil_awready.value = 0

    async def _w_handler(self, stop_after: int):
        self.dut.m_axil_wready.value = 1
        seen = 0
        while seen < stop_after:
            await ReadOnly()
            if (int(self.dut.m_axil_wvalid.value) == 1
                    and int(self.dut.m_axil_wready.value) == 1):
                self._w_q.append(int(self.dut.m_axil_wdata.value))
                seen += 1
            await RisingEdge(self.dut.axi_aclk)
        await RisingEdge(self.dut.axi_aclk)
        self.dut.m_axil_wready.value = 0

    async def _b_handler(self, stop_after: int):
        """When both AW and W queues are non-empty, drive bvalid for one
        handshake, pop both queues, and record (addr, data)."""
        sent = 0
        while sent < stop_after:
            # Wait until we have both an addr and data to ack.
            await ReadOnly()
            ready_to_ack = bool(self._aw_q) and bool(self._w_q)
            await RisingEdge(self.dut.axi_aclk)
            if not ready_to_ack:
                continue
            # Drive B response.
            self.dut.m_axil_bvalid.value = 1
            self.dut.m_axil_bresp.value  = 0  # OKAY
            while True:
                await ReadOnly()
                if int(self.dut.m_axil_bready.value) == 1:
                    break
                await RisingEdge(self.dut.axi_aclk)
            await RisingEdge(self.dut.axi_aclk)
            self.dut.m_axil_bvalid.value = 0
            addr = self._aw_q.pop(0)
            data = self._w_q.pop(0)
            self.captured.append((addr, data))
            sent += 1

    async def run_records_through(self,
                                  records: List[Tuple[int, int]],
                                  expected_slots: List[int]):
        n_slots = len(expected_slots)
        # AW handler captures one more than expected to absorb any
        # late-stage capture race; the W and B handlers stop at the
        # exact slot count so we don't hang waiting for phantom beats.
        aw_task = cocotb.start_soon(self._aw_handler(n_slots))
        w_task  = cocotb.start_soon(self._w_handler(n_slots))
        b_task  = cocotb.start_soon(self._b_handler(n_slots))

        for pkt, ts in records:
            await self.drive_record(pkt, ts)

        # Drain: wait for all B handshakes to fire.
        await Combine(aw_task, w_task, b_task)

        assert len(self.captured) == n_slots, (
            f"captured slot count mismatch: got={len(self.captured)}, "
            f"expected={n_slots}"
        )

        rtl_slots = [d for (_, d) in self.captured]
        for i, (rtl, golden) in enumerate(zip(rtl_slots, expected_slots)):
            assert rtl == golden, (
                f"slot {i} mismatch: rtl=0x{rtl:016x}, golden=0x{golden:016x}"
            )

    # ---------- wrap-window assertion ----------

    def assert_wrap_addresses(self, base_addr: int, limit_addr: int):
        """Walk the captured (addr, data) pairs and confirm every addr
        is inside [base_addr, limit_addr - 7] and that consecutive addrs
        either step by +8 or wrap back to base_addr."""
        for i, (addr, _) in enumerate(self.captured):
            assert base_addr <= addr <= (limit_addr - (self.SLOT_STRIDE - 1)), (
                f"slot {i}: addr 0x{addr:08x} outside window "
                f"[0x{base_addr:08x}, 0x{limit_addr:08x}]"
            )
            if i == 0:
                continue
            prev_addr = self.captured[i - 1][0]
            step = addr - prev_addr
            wrapped = (prev_addr + self.SLOT_STRIDE) > limit_addr and addr == base_addr
            assert step == self.SLOT_STRIDE or wrapped, (
                f"slot {i}: bad addr step from 0x{prev_addr:08x} to 0x{addr:08x}"
            )


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

    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba5_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'],   "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_axil4'],    "axil4_slave_rd.sv"),
        os.path.join(rtl_dict['rtl_axil4'],    "axil4_master_wr.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_cam.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_compressor.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_group_core.sv"),
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
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
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
