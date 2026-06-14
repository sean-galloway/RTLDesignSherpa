# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_axil_axil_group_master_write
# Purpose: AXIL master-write raw-mode coverage for monbus_axil_axil_group.
#
# Author: sean galloway
# Created: 2026-06-11

"""
AXIL/AXIL master-write coverage in raw mode (USE_COMPRESSION=0).

The basic test_monbus_axil_axil_group.py treats the master-write side as
a synthetic sink and never asserts that beats actually leave m_axil_w*.
That gap let
[MONBUS_GROUP_AXIL_MASTER_RAWMODE_FLUSH_BUG.md](../../MONBUS_GROUP_AXIL_MASTER_RAWMODE_FLUSH_BUG.md)
slip through: when the master leaf is AXIL (MAX_BURST_BEATS=1) and raw
mode is selected (BEATS_PER_UNIT=3), the per-burst beat plan is capped
to 1, rounded down to a whole 3-beat record, which yields 0, so the
write FSM's IDLE->AW guard never fires.

This test exercises that exact configuration with a real AXIL slave model
that captures beats, and asserts the expected 3-beats-per-record cadence.

Three phases:
  1. **Bounded window, watermark-driven flush.** Send N records,
     capture exactly 3*N beats at increasing 8-byte-stride addresses
     starting at cfg_base_addr.
  2. **Timeout-driven flush.** Send 1 record, watermark high; the
     writer should still flush via the timeout path.
  3. **Wrap-back.** Tight window holds < N records; assert the
     captured addresses wrap back to cfg_base_addr at the right beat.
"""

import os
import random
from typing import List, Tuple

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly, Combine
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


BEATS_PER_RECORD = 3            # raw mode
BYTES_PER_BEAT   = 8


def synth_record_stream(n: int, seed: int = 0xC1C1) -> List[Tuple[int, int]]:
    """Generate `n` monbus error records."""
    from TBClasses.monbus import (
        create_monitor_packet, PktType, ProtocolType, AXIErrorCode,
    )
    rng = random.Random(seed)
    return [
        (
            create_monitor_packet(
                PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
                AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, i % 8, 0x21,
                rng.randint(0, 0xFFFF_FFFF_FFFF_FFFF),
            ),
            1000 + 10 * i,
        )
        for i in range(n)
    ]


class MonbusAxilAxilMasterWriteTB(TBBase):
    """Drive records in, act as an AXIL slave on the master-write side,
    capture every beat that the DUT writes out."""

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        # Captured (addr, data) pairs in handshake order.
        self.captured: List[Tuple[int, int]] = []
        self._aw_q: List[int] = []
        self._w_q: List[int] = []

    # ---------- setup / reset ----------

    def _tie_off_config(self):
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

    async def reset_dut(self, base_addr: int, limit_addr: int,
                        flush_watermark: int):
        self.dut.monbus_valid.value     = 0
        self.dut.monbus_packet.value    = 0
        self.dut.monbus_timestamp.value = 0
        self.dut.s_axil_arvalid.value   = 0
        self.dut.s_axil_araddr.value    = 0
        self.dut.s_axil_arprot.value    = 0
        self.dut.s_axil_rready.value    = 0
        self.dut.m_axil_awready.value   = 0
        self.dut.m_axil_wready.value    = 0
        self.dut.m_axil_bvalid.value    = 0
        self.dut.m_axil_bresp.value     = 0
        self.dut.cfg_base_addr.value       = base_addr
        self.dut.cfg_limit_addr.value      = limit_addr
        self.dut.cfg_flush_watermark.value = flush_watermark
        self._tie_off_config()
        self.dut.axi_aresetn.value = 0
        await self.wait_clocks('axi_aclk', 5)
        self.dut.axi_aresetn.value = 1
        await self.wait_clocks('axi_aclk', 2)
        self.captured.clear()
        self._aw_q.clear()
        self._w_q.clear()

    # ---------- monbus driver ----------

    async def drive_record(self, packet: int, source_ts: int):
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

    async def drive_records(self, records):
        for pkt, ts in records:
            await self.drive_record(pkt, ts)

    # ---------- AXIL slave model on m_axil_* ----------

    async def _aw_handler(self, stop_after: int):
        self.dut.m_axil_awready.value = 1
        seen = 0
        while seen < stop_after:
            await ReadOnly()
            if (int(self.dut.m_axil_awvalid.value) == 1
                    and int(self.dut.m_axil_awready.value) == 1):
                self._aw_q.append(int(self.dut.m_axil_awaddr.value))
                seen += 1
            await RisingEdge(self.dut.axi_aclk)
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
        sent = 0
        while sent < stop_after:
            await ReadOnly()
            ready_to_ack = bool(self._aw_q) and bool(self._w_q)
            await RisingEdge(self.dut.axi_aclk)
            if not ready_to_ack:
                continue
            self.dut.m_axil_bvalid.value = 1
            self.dut.m_axil_bresp.value  = 0
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

    async def capture_n_beats(self, n: int, drain_cycles: int = 4000):
        """Spawn the AXIL slave model handlers, run the bus for up to
        drain_cycles, and return whatever was captured. The handlers
        return when stop_after is reached, so this is bounded above by
        either capture-count or wall-clock."""
        aw_task = cocotb.start_soon(self._aw_handler(n))
        w_task  = cocotb.start_soon(self._w_handler(n))
        b_task  = cocotb.start_soon(self._b_handler(n))
        timer = cocotb.start_soon(self.wait_clocks('axi_aclk', drain_cycles))
        await Combine(timer)
        # Allow any in-flight beats to land
        await self.wait_clocks('axi_aclk', 4)

    # ---------- assertions ----------

    def assert_record_cadence(self, base_addr: int, expected_records: int):
        """Assert that captured beats step by 8 bytes within a record,
        and that there are expected_records * 3 beats."""
        expected_beats = expected_records * BEATS_PER_RECORD
        assert len(self.captured) == expected_beats, (
            f"captured {len(self.captured)} beats, expected "
            f"{expected_beats} (= {expected_records} records x "
            f"{BEATS_PER_RECORD} beats)"
        )
        for i, (addr, _) in enumerate(self.captured):
            expected_addr = base_addr + (i * BYTES_PER_BEAT)
            assert addr == expected_addr, (
                f"beat {i}: addr 0x{addr:08x}, expected 0x{expected_addr:08x}"
            )


# ----------------------------------------------------------------------------
# Cocotb test
# ----------------------------------------------------------------------------

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_monbus_axil_axil_master_write(dut):
    tb = MonbusAxilAxilMasterWriteTB(dut)
    await tb.start_clock('axi_aclk', 10, 'ns')

    # =========================================================
    # Phase 1: watermark-driven flush, bounded window
    # =========================================================
    tb.log.info("=== Phase 1: watermark-driven flush, AXIL master, raw mode ===")
    N_RECS = 3
    BASE   = 0x0000_1000
    LIMIT  = 0x0000_4FFF
    # Watermark = exactly one record's worth of beats. The writer should
    # flush as soon as the first record lands in the FIFO.
    await tb.reset_dut(BASE, LIMIT, flush_watermark=BEATS_PER_RECORD)
    expected_beats = N_RECS * BEATS_PER_RECORD

    capture = cocotb.start_soon(tb.capture_n_beats(expected_beats,
                                                   drain_cycles=4000))
    await tb.drive_records(synth_record_stream(N_RECS))
    await Combine(capture)

    tb.assert_record_cadence(BASE, N_RECS)
    tb.log.info(f"  captured {len(tb.captured)} beats at "
                f"0x{tb.captured[0][0]:08x}..0x{tb.captured[-1][0]:08x} -- OK")

    # =========================================================
    # Phase 2: timeout-driven flush
    # =========================================================
    tb.log.info("=== Phase 2: timeout-driven flush ===")
    BASE  = 0x0000_2000
    LIMIT = 0x0000_3FFF
    await tb.reset_dut(BASE, LIMIT, flush_watermark=1024)  # huge => never fires

    capture = cocotb.start_soon(tb.capture_n_beats(BEATS_PER_RECORD,
                                                   drain_cycles=4000))
    await tb.drive_records(synth_record_stream(1, seed=0xD2D2))
    await Combine(capture)

    tb.assert_record_cadence(BASE, 1)
    tb.log.info(f"  timeout flushed {len(tb.captured)} beats -- OK")

    # =========================================================
    # Phase 3: wrap-back window
    # =========================================================
    tb.log.info("=== Phase 3: window wrap-back ===")
    BASE  = 0x0000_3000
    # Window holds exactly 1 record (24 bytes) before wrap.
    LIMIT = BASE + (BEATS_PER_RECORD * BYTES_PER_BEAT) - 1
    N_RECS = 3
    await tb.reset_dut(BASE, LIMIT, flush_watermark=BEATS_PER_RECORD)
    expected_beats = N_RECS * BEATS_PER_RECORD

    capture = cocotb.start_soon(tb.capture_n_beats(expected_beats,
                                                   drain_cycles=6000))
    await tb.drive_records(synth_record_stream(N_RECS, seed=0xE3E3))
    await Combine(capture)

    # Every record should land at exactly BASE (window wraps each time).
    assert len(tb.captured) == expected_beats, (
        f"got {len(tb.captured)} beats, expected {expected_beats}"
    )
    for rec in range(N_RECS):
        for slot in range(BEATS_PER_RECORD):
            i = rec * BEATS_PER_RECORD + slot
            expected_addr = BASE + slot * BYTES_PER_BEAT
            actual_addr = tb.captured[i][0]
            assert actual_addr == expected_addr, (
                f"record {rec}, slot {slot}: got 0x{actual_addr:08x}, "
                f"expected 0x{expected_addr:08x}"
            )
    tb.log.info(f"  3 records wrapped to BASE -- OK")

    tb.log.info("=== ALL PHASES PASSED ===")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------

def test_monbus_axil_axil_group_master_write(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_shared':   'rtl/amba/shared',
        'rtl_axil4':    'rtl/amba/axil4',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "monbus_axil_axil_group"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_master_write_raw"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'],   "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axil4'],    "axil4_slave_rd.sv"),
        os.path.join(rtl_dict['rtl_axil4'],    "axil4_master_wr.sv"),
        # Monbus group core family (cam/compressor/core + div-by-3 helper)
        # from the shared canonical filelist -- one place for new deps.
        *get_sources_from_filelist(repo_root, 'rtl/amba/filelists/monbus_group.f')[0],
        os.path.join(rtl_dict['rtl_shared'],   f"{dut_name}.sv"),
    ]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    parameters = {
        'ADDR_WIDTH':           32,
        'FLUSH_TIMEOUT_CYCLES': 200,    # short enough that Phase 2 doesn't hang the test
        'USE_COMPRESSION':      0,
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
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module='test_monbus_axil_axil_group_master_write',
            testcase="cocotb_test_monbus_axil_axil_master_write",
            sim_build=sim_build,
            extra_env=extra_env,
            parameters=parameters,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ Master-write raw-mode test PASSED! Logs: {log_path}")
    except Exception as e:
        print(f"✗ Master-write raw-mode test FAILED: {e}")
        print(f"Logs: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
