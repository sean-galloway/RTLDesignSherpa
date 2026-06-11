# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_axil_axi4_group
# Purpose: AXI4-burst master-write coverage for monbus_axil_axi4_group.
#
# Author: sean galloway
# Created: 2026-06-11

"""
Burst-coverage test for `rtl/amba/shared/monbus_axil_axi4_group.sv`.

The AXIL/AXIL family member exercises the master-write path one beat
at a time, so it doesn't catch bugs in AXI4 burst behavior. This test
targets the AXI4-burst master-write member specifically and verifies:

  1. **Watermark-triggered multi-beat burst.** Records accumulate
     to >= cfg_flush_watermark, then a single AW + N x W + B fires
     where N is min(beats_in_fifo, MAX_BURST_BEATS, 4kB_boundary).
     wlast asserts only on beat N.
  2. **Timeout-triggered flush.** No further input arrives; after
     FLUSH_TIMEOUT_CYCLES the writer flushes whatever it has
     (provided it's at least BEATS_PER_UNIT beats).
  3. **4KB boundary respect.** With cfg_base addressed near a 4K
     boundary and enough records to overrun it, the writer must
     split rather than emit a single burst that crosses the
     boundary.

The DUT's master AXI4 outputs are consumed by a slot-by-slot AXI4
slave model living in this file.
"""

import os
import random
from typing import List, Tuple

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

BEATS_PER_RECORD = 3            # raw mode: 24 bytes / record
BYTES_PER_BEAT   = 8


def synth_record_stream(n: int) -> List[Tuple[int, int]]:
    """Generate `n` monbus records (packet + source_ts) using the same
    helpers the compressor test uses. Returns [(packet, source_ts), ...]."""
    from TBClasses.monbus import (
        create_monitor_packet, PktType, ProtocolType,
        AXIErrorCode,
    )
    out = []
    rng = random.Random(0xA1A1)
    for i in range(n):
        pkt = create_monitor_packet(
            PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
            AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, i % 8, 0x21,
            rng.randint(0, 0xFFFF_FFFF_FFFF_FFFF),
        )
        out.append((pkt, 1000 + 10 * i))
    return out


# ----------------------------------------------------------------------------
# TB
# ----------------------------------------------------------------------------

class MonbusAxilAxi4GroupTB(TBBase):
    """Drive monbus records in, act as an AXI4 slave on the master-write
    side, and verify the shape of each captured burst."""

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        # Each captured burst = list of (addr, [beat0, beat1, ...])
        self.bursts: List[Tuple[int, List[int]]] = []
        # Pending state during a burst
        self._current_aw_addr: int = 0
        self._current_aw_len: int  = 0
        self._current_w_beats: List[int] = []

    # ---------- setup / reset ----------

    def _tie_off_config(self):
        """Disable all dropping and all err-FIFO routing so every monbus
        packet lands in the write FIFO. This minimal TB doesn't drain
        the err FIFO; with err_select=0 it never fills."""
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
        # Slave read side unused.
        self.dut.s_axil_arvalid.value = 0
        self.dut.s_axil_araddr.value  = 0
        self.dut.s_axil_arprot.value  = 0
        self.dut.s_axil_rready.value  = 0
        # Master-write side ready signals (we consume freely).
        self.dut.m_axi_awready.value = 1
        self.dut.m_axi_wready.value  = 1
        self.dut.m_axi_bvalid.value  = 0
        self.dut.m_axi_bresp.value   = 0
        self.dut.m_axi_bid.value     = 0
        self.dut.m_axi_buser.value   = 0
        # Window.
        self.dut.cfg_base_addr.value       = base_addr
        self.dut.cfg_limit_addr.value      = limit_addr
        self.dut.cfg_flush_watermark.value = flush_watermark
        self._tie_off_config()
        # Reset pulse.
        self.dut.axi_aresetn.value = 0
        await self.wait_clocks('axi_aclk', 5)
        self.dut.axi_aresetn.value = 1
        await self.wait_clocks('axi_aclk', 2)
        self.bursts.clear()
        self._current_w_beats.clear()

    # ---------- monbus driver (input side) ----------

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

    async def drive_records(self, records: List[Tuple[int, int]]):
        for pkt, ts in records:
            await self.drive_record(pkt, ts)

    # ---------- AXI4 slave model (output side) ----------

    async def _capture_burst_handler(self, expected_bursts: int):
        """Capture (addr, awlen, [data...]) tuples and assert wlast
        timing as we go. Stops after `expected_bursts` bursts have
        completed (AW + N x W + B for each)."""
        captured = 0
        while captured < expected_bursts:
            # 1) Wait for AW
            while True:
                await ReadOnly()
                aw_seen = (int(self.dut.m_axi_awvalid.value) == 1
                           and int(self.dut.m_axi_awready.value) == 1)
                await RisingEdge(self.dut.axi_aclk)
                if aw_seen:
                    self._current_aw_addr = int(self.dut.m_axi_awaddr.value)
                    self._current_aw_len  = int(self.dut.m_axi_awlen.value)
                    awsize = int(self.dut.m_axi_awsize.value)
                    awburst = int(self.dut.m_axi_awburst.value)
                    # Expected: 8 bytes per beat (size=3), INCR (burst=01)
                    assert awsize == 3, f"awsize={awsize}, expected 3 (8B)"
                    assert awburst == 1, f"awburst={awburst}, expected 1 (INCR)"
                    break

            # 2) Collect W beats; assert wlast timing
            self._current_w_beats.clear()
            n_beats = self._current_aw_len + 1
            while len(self._current_w_beats) < n_beats:
                await ReadOnly()
                w_seen = (int(self.dut.m_axi_wvalid.value) == 1
                          and int(self.dut.m_axi_wready.value) == 1)
                if w_seen:
                    wdata = int(self.dut.m_axi_wdata.value)
                    wlast = int(self.dut.m_axi_wlast.value)
                    self._current_w_beats.append(wdata)
                    is_final = (len(self._current_w_beats) == n_beats)
                    assert wlast == int(is_final), (
                        f"burst@0x{self._current_aw_addr:08x}: "
                        f"wlast={wlast} on beat {len(self._current_w_beats)}/{n_beats}, "
                        f"expected={int(is_final)}"
                    )
                await RisingEdge(self.dut.axi_aclk)

            # 3) Send B
            self.dut.m_axi_bvalid.value = 1
            self.dut.m_axi_bresp.value  = 0
            while True:
                await ReadOnly()
                if int(self.dut.m_axi_bready.value) == 1:
                    break
                await RisingEdge(self.dut.axi_aclk)
            await RisingEdge(self.dut.axi_aclk)
            self.dut.m_axi_bvalid.value = 0

            # 4) Record burst
            self.bursts.append((self._current_aw_addr,
                                list(self._current_w_beats)))
            captured += 1

    # ---------- assertions ----------

    def assert_burst_shape(self, *, min_beats: int, max_beats: int,
                           expected_total_beats: int):
        total = sum(len(b[1]) for b in self.bursts)
        assert total == expected_total_beats, (
            f"total beats: got={total}, expected={expected_total_beats}"
        )
        for i, (addr, beats) in enumerate(self.bursts):
            assert min_beats <= len(beats) <= max_beats, (
                f"burst {i}@0x{addr:08x}: len={len(beats)}, "
                f"expected in [{min_beats}, {max_beats}]"
            )

    def assert_no_4kb_crossing(self):
        for i, (addr, beats) in enumerate(self.bursts):
            last_byte = addr + len(beats) * BYTES_PER_BEAT - 1
            # 4KB boundary: top 20+ bits of addr and last_byte must match
            assert (addr >> 12) == (last_byte >> 12), (
                f"burst {i}@0x{addr:08x} of {len(beats)} beats crosses "
                f"4KB boundary (last byte 0x{last_byte:08x})"
            )


# ----------------------------------------------------------------------------
# Cocotb test
# ----------------------------------------------------------------------------

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_monbus_axil_axi4_group(dut):
    tb = MonbusAxilAxi4GroupTB(dut)
    await tb.start_clock('axi_aclk', 10, 'ns')

    # ===========================================================
    # Phase 1: Watermark-triggered multi-beat burst
    # ===========================================================
    tb.log.info("=== Phase 1: watermark-triggered burst ===")
    # 8 records = 24 beats. Watermark=24 forces one burst once the FIFO
    # fills to exactly 24 beats. MAX_BURST_BEATS is large enough to fit.
    BASE   = 0x0000_2000
    LIMIT  = 0x0000_5FFF
    N_RECS = 8
    await tb.reset_dut(BASE, LIMIT, flush_watermark=N_RECS * BEATS_PER_RECORD)

    # Run capture handler. Watermark=24 means exactly one flush burst
    # of 24 beats once all records are in.
    capture = cocotb.start_soon(tb._capture_burst_handler(expected_bursts=1))
    await tb.drive_records(synth_record_stream(N_RECS))
    # Give the writer plenty of cycles to complete the burst.
    await tb.wait_clocks('axi_aclk', 200)
    assert capture.done(), "phase 1: expected 1 burst but it never completed"

    tb.assert_burst_shape(min_beats=24, max_beats=24,
                          expected_total_beats=24)
    tb.assert_no_4kb_crossing()
    addr0 = tb.bursts[0][0]
    assert addr0 == BASE, f"phase 1: burst started at 0x{addr0:08x}, expected 0x{BASE:08x}"
    tb.log.info(f"  burst0: addr=0x{addr0:08x}, beats={len(tb.bursts[0][1])} -- OK")

    # ===========================================================
    # Phase 2: Timeout-triggered flush
    # ===========================================================
    tb.log.info("=== Phase 2: timeout-triggered flush ===")
    # Send just one record (3 beats). Watermark=1024 (huge); FLUSH_TIMEOUT
    # default is 1024 cycles. The writer should NOT fire on watermark,
    # but should fire on timeout shortly thereafter.
    BASE  = 0x0000_3000
    LIMIT = 0x0000_4FFF
    await tb.reset_dut(BASE, LIMIT, flush_watermark=1024)

    capture = cocotb.start_soon(tb._capture_burst_handler(expected_bursts=1))
    await tb.drive_records(synth_record_stream(1))
    # Wait long enough for timeout to fire (>1024 cycles).
    await tb.wait_clocks('axi_aclk', 1500)
    assert capture.done(), "phase 2: timeout flush never fired"

    tb.assert_burst_shape(min_beats=3, max_beats=3, expected_total_beats=3)
    tb.assert_no_4kb_crossing()
    tb.log.info(f"  timeout flush: burst of {len(tb.bursts[0][1])} beats -- OK")

    # ===========================================================
    # Phase 3: 4KB boundary respect
    # ===========================================================
    tb.log.info("=== Phase 3: 4KB boundary split ===")
    # Start cfg_base near (but before) a 4KB boundary so a single
    # large burst would cross it. With watermark high enough that the
    # writer will pack the FIFO, the writer must still split at 0x1000
    # boundaries.
    #
    # cfg_base = 0x0FE0 (= 0x1000 - 0x20) -- 32 bytes (= 4 beats)
    # before the boundary. We push 4 records = 12 beats; that's 96
    # bytes from base, ending at 0x1040, which crosses 0x1000.
    BASE  = 0x0000_0FE0
    LIMIT = 0x0000_2000
    N_RECS = 4
    await tb.reset_dut(BASE, LIMIT, flush_watermark=N_RECS * BEATS_PER_RECORD)

    # We expect either 2 bursts (some beats before the boundary, the
    # rest after) or 1 burst if the unit-rounding forces all 12 beats
    # to fit in one of the two halves. Capture up to 3 to be safe.
    capture = cocotb.start_soon(tb._capture_burst_handler(expected_bursts=2))
    await tb.drive_records(synth_record_stream(N_RECS))
    await tb.wait_clocks('axi_aclk', 500)
    # At least one burst should have landed.
    assert len(tb.bursts) >= 1, "phase 3: no bursts at all"

    tb.assert_no_4kb_crossing()
    total = sum(len(b[1]) for b in tb.bursts)
    # raw mode rounds to multiples of 3 beats; depending on where the
    # boundary falls we might emit 12 beats across multiple bursts.
    assert total % BEATS_PER_RECORD == 0, (
        f"phase 3: total beats {total} not a multiple of {BEATS_PER_RECORD}"
    )
    tb.log.info(f"  {len(tb.bursts)} burst(s), {total} total beats, no 4KB crossing -- OK")

    tb.log.info("=== ALL PHASES PASSED ===")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------

def test_monbus_axil_axi4_group(request):
    """Pytest wrapper for MonBus AXIL/AXI4 burst coverage test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_shared':   'rtl/amba/shared',
        'rtl_axil4':    'rtl/amba/axil4',
        'rtl_axi4':     'rtl/amba/axi4',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "monbus_axil_axi4_group"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_burst"

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
        os.path.join(rtl_dict['rtl_axi4'],     "axi4_master_wr.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_cam.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_compressor.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_group_core.sv"),
        os.path.join(rtl_dict['rtl_shared'],   f"{dut_name}.sv"),
    ]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # 8 beats max per burst keeps the test from waiting forever on a
    # huge accumulation; the watermark-burst phase uses watermark=24
    # which is bigger than 8, so we'll see multiple bursts (3 x 8).
    parameters = {
        'ADDR_WIDTH':      32,
        'AXI_ID_WIDTH':    1,
        'AXI_USER_WIDTH':  1,
        'MAX_BURST_BEATS': 32,
        'FLUSH_TIMEOUT_CYCLES': 1024,
        'USE_COMPRESSION': 0,
    }

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
            module='test_monbus_axil_axi4_group',
            testcase="cocotb_test_monbus_axil_axi4_group",
            sim_build=sim_build,
            extra_env=extra_env,
            parameters=parameters,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ MonBus AXIL/AXI4 burst test PASSED! Logs: {log_path}")
    except Exception as e:
        print(f"✗ MonBus AXIL/AXI4 burst test FAILED: {e}")
        print(f"Logs: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
