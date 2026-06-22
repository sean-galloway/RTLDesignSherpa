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


class Axi4DmaObserverTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        # Read pass-through capture
        self.fab_seen_ar:  List[int] = []   # araddr values seen on the fabric side
        self.dma_seen_r:   List[int] = []   # rdata values seen on the DMA side
        # Write pass-through capture
        self.fab_seen_aw:  List[int] = []   # awaddr on fabric side
        self.fab_seen_w:   List[int] = []   # wdata on fabric side
        self.dma_seen_b:   List[int] = []   # bresp on DMA side
        # Observer-output capture
        self.dump_aw:      List[int] = []   # m_axi_awaddr (observer's own dump port)
        self.dump_w:       List[int] = []   # m_axi_wdata
        self.dump_aw_q:    List[int] = []
        self.dump_w_q:     List[int] = []

    async def reset_dut(self, base_addr: int, limit_addr: int,
                        flush_watermark: int = 3):
        self.dut.cam_clear.value       = 0
        # DMA-side inputs (all idle)
        self.dut.dma_rd_arvalid.value  = 0
        self.dut.dma_rd_araddr.value   = 0
        self.dut.dma_rd_arid.value     = 0
        self.dut.dma_rd_arlen.value    = 0
        self.dut.dma_rd_arsize.value   = 0
        self.dut.dma_rd_arburst.value  = 0
        self.dut.dma_rd_arlock.value   = 0
        self.dut.dma_rd_arcache.value  = 0
        self.dut.dma_rd_arprot.value   = 0
        self.dut.dma_rd_arqos.value    = 0
        self.dut.dma_rd_arregion.value = 0
        self.dut.dma_rd_aruser.value   = 0
        self.dut.dma_rd_rready.value   = 0

        self.dut.dma_wr_awvalid.value  = 0
        self.dut.dma_wr_awaddr.value   = 0
        self.dut.dma_wr_awid.value     = 0
        self.dut.dma_wr_awlen.value    = 0
        self.dut.dma_wr_awsize.value   = 0
        self.dut.dma_wr_awburst.value  = 0
        self.dut.dma_wr_awlock.value   = 0
        self.dut.dma_wr_awcache.value  = 0
        self.dut.dma_wr_awprot.value   = 0
        self.dut.dma_wr_awqos.value    = 0
        self.dut.dma_wr_awregion.value = 0
        self.dut.dma_wr_awuser.value   = 0
        self.dut.dma_wr_wvalid.value   = 0
        self.dut.dma_wr_wdata.value    = 0
        self.dut.dma_wr_wstrb.value    = 0
        self.dut.dma_wr_wlast.value    = 0
        self.dut.dma_wr_wuser.value    = 0
        self.dut.dma_wr_bready.value   = 0

        # Fabric-side responses (idle; the responders below drive these)
        self.dut.fab_rd_arready.value = 0
        self.dut.fab_rd_rvalid.value  = 0
        self.dut.fab_rd_rdata.value   = 0
        self.dut.fab_rd_rid.value     = 0
        self.dut.fab_rd_rresp.value   = 0
        self.dut.fab_rd_rlast.value   = 0
        self.dut.fab_rd_ruser.value   = 0
        self.dut.fab_wr_awready.value = 0
        self.dut.fab_wr_wready.value  = 0
        self.dut.fab_wr_bvalid.value  = 0
        self.dut.fab_wr_bid.value     = 0
        self.dut.fab_wr_bresp.value   = 0
        self.dut.fab_wr_buser.value   = 0

        # Observer output ports as a synthetic AXI4 slave + AXIL slave-read
        self.dut.s_axil_arvalid.value = 0
        self.dut.s_axil_araddr.value  = 0
        self.dut.s_axil_arprot.value  = 0
        self.dut.s_axil_rready.value  = 0
        self.dut.m_axi_awready.value  = 1   # always ready (we capture)
        self.dut.m_axi_wready.value   = 1
        self.dut.m_axi_bvalid.value   = 0
        self.dut.m_axi_bid.value      = 0
        self.dut.m_axi_bresp.value    = 0
        self.dut.m_axi_buser.value    = 0

        # Config
        self.dut.cfg_base_addr.value       = base_addr
        self.dut.cfg_limit_addr.value      = limit_addr
        self.dut.cfg_flush_watermark.value = flush_watermark
        # Let all packets through (no drop, no err-FIFO routing -> everything goes to write FIFO).
        # AXIS / CORE masks are configurable from the top now too; we don't
        # use those protocols in this smoke test so they stay all-zeros.
        for sig in [
            'cfg_axi_pkt_mask', 'cfg_axi_err_select',
            'cfg_axi_error_mask', 'cfg_axi_timeout_mask',
            'cfg_axi_compl_mask', 'cfg_axi_thresh_mask',
            'cfg_axi_perf_mask', 'cfg_axi_addr_mask', 'cfg_axi_debug_mask',
            'cfg_axis_pkt_mask', 'cfg_axis_err_select',
            'cfg_axis_error_mask', 'cfg_axis_timeout_mask',
            'cfg_axis_compl_mask', 'cfg_axis_credit_mask',
            'cfg_axis_channel_mask', 'cfg_axis_stream_mask',
            'cfg_core_pkt_mask', 'cfg_core_err_select',
            'cfg_core_error_mask', 'cfg_core_timeout_mask',
            'cfg_core_compl_mask', 'cfg_core_thresh_mask',
            'cfg_core_perf_mask', 'cfg_core_debug_mask',
        ]:
            getattr(self.dut, sig).value = 0

        # USE_COMPRESSION=0 in this smoke test, so cfg_compress_en has no
        # effect; still drive it so the port is initialized.
        self.dut.cfg_compress_en.value = 0

        # ---- axi_bus_meter inputs ----
        self.dut.i_meter_clear.value  = 0
        self.dut.i_meter_freeze.value = 0

        # Identity rid -> channel map for the single read port:
        # channel 0 expects rid=1, channel 1 expects rid=2, etc., matching
        # the test driver's `arid=(i & 0xF) + 1`. All NUM_CHANNELS entries
        # valid so a wider range of arids attribute correctly.
        # Note: cocotb cocotb 1.x indexes packed signals; for unpacked
        # 2D arrays the index style is dut.signal[port][ch].value = X.
        for ch in range(8):  # NUM_CHANNELS, matches the test parameter
            try:
                self.dut.cfg_rd_rid_per_channel[0][ch].value       = ch + 1
                self.dut.cfg_rd_rid_per_channel_valid[0][ch].value = 1
            except (AttributeError, IndexError):
                # Signal-list array indexing may not be reachable on some
                # cocotb/Verilator combinations. The meter still produces
                # aggregate counters either way.
                pass

        # Write-side channel-active sideband: this synthetic test doesn't
        # provide one, so tie to 0 (aggregate counters still tick).
        try:
            self.dut.dma_wr_active_ch_id[0].value    = 0
            self.dut.dma_wr_active_ch_valid[0].value = 0
        except (AttributeError, IndexError):
            pass

        # Reset pulse
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 5)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)

        self.fab_seen_ar.clear()
        self.dma_seen_r.clear()
        self.fab_seen_aw.clear()
        self.fab_seen_w.clear()
        self.dma_seen_b.clear()
        self.dump_aw.clear()
        self.dump_w.clear()
        self.dump_aw_q.clear()
        self.dump_w_q.clear()

    # ----- DMA-side AXI master (we drive) -----

    async def dma_read(self, addr: int, arid: int = 1):
        """Issue a single-beat read on the DMA-side AR; collect R."""
        self.dut.dma_rd_arvalid.value = 1
        self.dut.dma_rd_araddr.value  = addr
        self.dut.dma_rd_arid.value    = arid
        self.dut.dma_rd_arlen.value   = 0  # 1 beat
        self.dut.dma_rd_arsize.value  = 4  # 16 bytes (DATA_WIDTH=128)
        self.dut.dma_rd_arburst.value = 1  # INCR
        # AR handshake
        while True:
            await ReadOnly()
            if int(self.dut.dma_rd_arready.value) == 1:
                break
            await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)
        self.dut.dma_rd_arvalid.value = 0
        # R consumption
        self.dut.dma_rd_rready.value = 1
        while True:
            await ReadOnly()
            if int(self.dut.dma_rd_rvalid.value) == 1:
                self.dma_seen_r.append(int(self.dut.dma_rd_rdata.value))
                break
            await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)
        self.dut.dma_rd_rready.value = 0

    async def dma_write(self, addr: int, data: int, awid: int = 1):
        """Single-beat write on the DMA side."""
        self.dut.dma_wr_awvalid.value = 1
        self.dut.dma_wr_awaddr.value  = addr
        self.dut.dma_wr_awid.value    = awid
        self.dut.dma_wr_awlen.value   = 0
        self.dut.dma_wr_awsize.value  = 4
        self.dut.dma_wr_awburst.value = 1

        self.dut.dma_wr_wvalid.value = 1
        self.dut.dma_wr_wdata.value  = data
        self.dut.dma_wr_wstrb.value  = 0xFFFF   # all 16 bytes
        self.dut.dma_wr_wlast.value  = 1

        # Wait for AW handshake
        while True:
            await ReadOnly()
            aw_done = int(self.dut.dma_wr_awready.value) == 1
            await RisingEdge(self.dut.aclk)
            if aw_done:
                break
        self.dut.dma_wr_awvalid.value = 0
        # Wait for W handshake (probably already done in same cycle but
        # we re-poll to be safe)
        while True:
            await ReadOnly()
            w_done = int(self.dut.dma_wr_wready.value) == 1
            await RisingEdge(self.dut.aclk)
            if w_done:
                break
        self.dut.dma_wr_wvalid.value = 0
        # Accept B
        self.dut.dma_wr_bready.value = 1
        while True:
            await ReadOnly()
            if int(self.dut.dma_wr_bvalid.value) == 1:
                self.dma_seen_b.append(int(self.dut.dma_wr_bresp.value))
                break
            await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)
        self.dut.dma_wr_bready.value = 0

    # ----- Fabric-side responders (synthetic memory) -----

    async def _fab_rd_responder(self, n_reads: int):
        """Always-ready AR, single-beat R with synthesized data."""
        self.dut.fab_rd_arready.value = 1
        seen = 0
        # Keep arready high; emit R one cycle after each AR handshake
        while seen < n_reads:
            await ReadOnly()
            if (int(self.dut.fab_rd_arvalid.value) == 1
                    and int(self.dut.fab_rd_arready.value) == 1):
                addr = int(self.dut.fab_rd_araddr.value)
                arid = int(self.dut.fab_rd_arid.value)
                self.fab_seen_ar.append(addr)
                # Drive R one cycle later
                await RisingEdge(self.dut.aclk)
                self.dut.fab_rd_rvalid.value = 1
                self.dut.fab_rd_rdata.value  = 0xDEADBEEF00000000 | addr
                self.dut.fab_rd_rid.value    = arid
                self.dut.fab_rd_rresp.value  = 0
                self.dut.fab_rd_rlast.value  = 1
                while True:
                    await ReadOnly()
                    if int(self.dut.fab_rd_rready.value) == 1:
                        break
                    await RisingEdge(self.dut.aclk)
                await RisingEdge(self.dut.aclk)
                self.dut.fab_rd_rvalid.value = 0
                self.dut.fab_rd_rlast.value  = 0
                seen += 1
            else:
                await RisingEdge(self.dut.aclk)

    async def _fab_wr_responder(self, n_writes: int):
        """Always-ready AW + W, drive B per AW."""
        self.dut.fab_wr_awready.value = 1
        self.dut.fab_wr_wready.value  = 1
        seen = 0
        while seen < n_writes:
            # Capture AW + W
            saw_aw = False
            saw_w  = False
            while not (saw_aw and saw_w):
                await ReadOnly()
                if (int(self.dut.fab_wr_awvalid.value) == 1
                        and int(self.dut.fab_wr_awready.value) == 1
                        and not saw_aw):
                    self.fab_seen_aw.append(int(self.dut.fab_wr_awaddr.value))
                    saw_aw = True
                if (int(self.dut.fab_wr_wvalid.value) == 1
                        and int(self.dut.fab_wr_wready.value) == 1
                        and not saw_w):
                    self.fab_seen_w.append(int(self.dut.fab_wr_wdata.value))
                    saw_w = True
                await RisingEdge(self.dut.aclk)
            # Drive B
            self.dut.fab_wr_bvalid.value = 1
            self.dut.fab_wr_bresp.value  = 0
            while True:
                await ReadOnly()
                if int(self.dut.fab_wr_bready.value) == 1:
                    break
                await RisingEdge(self.dut.aclk)
            await RisingEdge(self.dut.aclk)
            self.dut.fab_wr_bvalid.value = 0
            seen += 1

    # ----- Observer m_axi_* dump port slave model -----

    async def _dump_capture(self, n_beats: int, drain_cycles: int = 8000):
        """Capture all m_axi_w* beats the observer emits."""
        sent_b = 0
        while sent_b < n_beats:
            await ReadOnly()
            aw_hs = (int(self.dut.m_axi_awvalid.value) == 1
                     and int(self.dut.m_axi_awready.value) == 1)
            w_hs  = (int(self.dut.m_axi_wvalid.value) == 1
                     and int(self.dut.m_axi_wready.value) == 1)
            if aw_hs:
                self.dump_aw_q.append(int(self.dut.m_axi_awaddr.value))
            if w_hs:
                self.dump_w_q.append(int(self.dut.m_axi_wdata.value))
            # Pair up AW+W, drive B
            await RisingEdge(self.dut.aclk)
            if self.dump_aw_q and self.dump_w_q:
                self.dut.m_axi_bvalid.value = 1
                while True:
                    await ReadOnly()
                    if int(self.dut.m_axi_bready.value) == 1:
                        break
                    await RisingEdge(self.dut.aclk)
                await RisingEdge(self.dut.aclk)
                self.dut.m_axi_bvalid.value = 0
                self.dump_aw.append(self.dump_aw_q.pop(0))
                self.dump_w.append(self.dump_w_q.pop(0))
                sent_b += 1


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

    verilog_sources = [
        # Monitor packages
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba5_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        # Common building blocks
        os.path.join(rtl_dict['rtl_common'],   "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'],   "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_common'],   "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'],   "arbiter_priority_encoder.sv"),
        os.path.join(rtl_dict['rtl_common'],   "arbiter_round_robin.sv"),
        # Skid + FIFO
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],     "gaxi_skid_buffer.sv"),
        # AXI / AXIL leaves
        os.path.join(rtl_dict['rtl_axil4'],    "axil4_slave_rd.sv"),
        os.path.join(rtl_dict['rtl_axi4'],     "axi4_master_wr.sv"),
        os.path.join(rtl_dict['rtl_axi4'],     "axi4_master_rd.sv"),
        # Monitor infrastructure
        os.path.join(rtl_dict['rtl_shared'],   "monitor_trans_cam.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_addr_check.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_reporter_error.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_reporter_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_reporter_compl.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_reporter_threshold.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_reporter_perf.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_reporter_debug.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "axi_monitor_filtered.sv"),
        # AXI _mon wrappers
        os.path.join(rtl_dict['rtl_axi4'],     "axi4_master_rd_mon.sv"),
        os.path.join(rtl_dict['rtl_axi4'],     "axi4_master_wr_mon.sv"),
        # Monbus delivery -- group core family (cam/compressor/core +
        # div-by-3 helper) from the shared canonical filelist.
        *get_sources_from_filelist(repo_root, 'rtl/amba/filelists/monbus_group.f')[0],
        os.path.join(rtl_dict['rtl_shared'],   "monbus_axil_axi4_group.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_arbiter.sv"),
        # Per-cycle valid/ready bucket counter (moved into shared)
        os.path.join(rtl_dict['rtl_shared'],   "axi_bus_meter.sv"),
        # Per-transaction latency histograms (RFC Stage E.3)
        os.path.join(rtl_dict['rtl_shared'],   "axi_perf_latency_hist.sv"),
        # The observer itself
        os.path.join(rtl_dict['rtl_shared'],   f"{dut_name}.sv"),
    ]
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
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
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
