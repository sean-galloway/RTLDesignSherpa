# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: Axi4DmaObserverTB
# Purpose: Testbench for axi4_dma_observer
# Subsystem: framework
#
# Extracted from val/amba/test_axi4_dma_observer.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from typing import List
from cocotb.triggers import RisingEdge, ReadOnly, Combine
from TBClasses.shared.tbbase import TBBase


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
