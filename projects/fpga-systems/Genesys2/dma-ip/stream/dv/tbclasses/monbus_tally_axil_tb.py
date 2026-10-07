# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for monbus_tally_axil -- the monbus packet BINNING engine.

This block is the primary test vehicle for the monitor stack: it is sized to
count 100,000+ packets across many types, routing each to a bin via a
CAM-programmed legal set with everything else landing in UNEXPECTED. Until now
it had no component test at all -- it lived only inside stream_harness.f, so
the only way to exercise it was a ~21 minute full-system build that pushed six
packets through it. Six packets does not test a binning engine, and a 21
minute turnaround is not a way to develop one.

Record format on rec_* is RAW 3-beat, 192 bits total:
    beat0 = {tag[3:0]=0, source_ts[59:0]}
    beat1 = packet[127:64]
    beat2 = packet[63:0]
A mod-3 counter on accepted rec_w beats reassembles the 128-bit packet.
"""

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.shared.tbbase import TBBase

# cfg (cfgw_*) register offsets -- see monbus_tally_axil.sv REG_CAM_*
CAM_CLEAR = 0x100
CAM_KEY   = 0x108
CAM_LOAD  = 0x110


def cam_key(agent, proto, ptype, evc):
    """Legal-set key. Same packing the host tools use -- do not re-derive."""
    return (((agent & 0xFFFF) << 16) | ((proto & 0xF) << 12)
            | ((ptype & 0xF) << 8) | (evc & 0xFF))


def make_packet(agent, proto, ptype, evc, channel=0, unit=0, data=0):
    """Build a 128-bit monbus packet.

    Layout is NOT guessable -- taken from monitor_common_pkg.sv:
        [127:124] packet_type   [123:109] reserved    [108:105] protocol
        [104: 97] event_code    [ 96: 88] channel_id  [ 87: 72] agent_id
        [ 71: 64] unit_id       [ 63:  0] event_data
    My first version invented a layout and every packet missed the CAM and
    landed in UNEXPECTED -- which looks identical to "the tally is broken".
    """
    return (((ptype   & 0xF)    << 124)
            | ((proto & 0xF)    << 105)
            | ((evc   & 0xFF)   << 97)
            | ((channel & 0x1FF) << 88)
            | ((agent & 0xFFFF) << 72)
            | ((unit  & 0xFF)   << 64)
            | (data & ((1 << 64) - 1)))


class MonbusTallyTB(TBBase):
    """Drives records at full rate and reads the bins back."""

    def __init__(self, dut):
        super().__init__(dut)
        self.sent = 0

    # ---- the three mandatory methods -------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock("aclk", freq=10, units="ns")
        d = self.dut
        for sig in ("rec_awvalid", "rec_wvalid", "rec_bready",
                    "cnt_arvalid", "cnt_rready",
                    "cfgw_awvalid", "cfgw_wvalid", "cfgw_bready",
                    "cfgr_arvalid", "cfgr_rready",
                    "tally_freeze", "tally_flush", "tally_clear"):
            if hasattr(d, sig):
                getattr(d, sig).value = 0
        await self.assert_reset()
        await self.wait_clocks("aclk", 10)
        await self.deassert_reset()
        await self.wait_clocks("aclk", 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- config writes ---------------------------------------------------
    async def cfg_write(self, addr, data):
        """One AXIL config write. ONE.

        Sampling ready AFTER the edge is wrong and not merely imprecise: the
        handshake completes on that edge, ready then drops, the loop spins
        with valid still asserted, and when ready returns high a SECOND
        duplicate transaction fires. That is how 2000 records became 2050
        counts and how the CAM legal set ended up shifted by a bin.
        """
        d = self.dut
        d.cfgw_awaddr.value = addr
        d.cfgw_awvalid.value = 1
        d.cfgw_wdata.value = data
        d.cfgw_wstrb.value = 0xFF
        d.cfgw_wvalid.value = 1
        d.cfgw_bready.value = 1
        aw_done = w_done = False
        while not (aw_done and w_done):
            await ReadOnly()                       # settled values for THIS edge
            aw_hs = (not aw_done) and int(d.cfgw_awready.value)
            w_hs  = (not w_done)  and int(d.cfgw_wready.value)
            await RisingEdge(d.aclk)               # the transfer happens here
            if aw_hs:
                aw_done = True
                d.cfgw_awvalid.value = 0
            if w_hs:
                w_done = True
                d.cfgw_wvalid.value = 0
        for _ in range(3):
            await RisingEdge(d.aclk)
            if int(d.cfgw_awready.value) and int(d.cfgw_wready.value):
                break
        d.cfgw_awvalid.value = 0
        d.cfgw_wvalid.value = 0
        for _ in range(2):
            await RisingEdge(d.aclk)

    async def program_legal_set(self, legal):
        """Load the CAM. Bin index == position in this list; misses -> UNEXPECTED."""
        await self.cfg_write(CAM_CLEAR, 0)
        for i, key in enumerate(legal):
            await self.cfg_write(CAM_KEY, cam_key(*key))
            await self.cfg_write(CAM_LOAD, (1 << 31) | i)

    # ---- record ingest, at rate -----------------------------------------
    async def send_records(self, packets, ts_start=1):
        """Push 3-beat records back-to-back, holding valid across beats.

        No per-packet gaps on purpose: the point of this block is sustained
        binning, so the test must actually saturate the ingest path rather
        than trickle.
        """
        d = self.dut
        d.rec_bready.value = 1
        ts = ts_start
        for pkt in packets:
            beats = (ts & ((1 << 60) - 1),
                     (pkt >> 64) & ((1 << 64) - 1),
                     pkt & ((1 << 64) - 1))
            d.rec_awaddr.value = 0
            d.rec_awvalid.value = 1
            for b in beats:
                d.rec_wdata.value = b
                d.rec_wstrb.value = 0xFF
                d.rec_wvalid.value = 1
                while True:
                    await RisingEdge(d.aclk)
                    if int(d.rec_wready.value):
                        break
            d.rec_awvalid.value = 0
            d.rec_wvalid.value = 0
            ts += 1
            self.sent += 1
        await self.wait_clocks("aclk", 20)

    # ---- bin readback ----------------------------------------------------
    async def read_bin(self, index):
        """One bin count, sampled with SETTLED values.

        The count port registers the address (r_cnt_rd_addr) and presents data
        a cycle later. Sampling cnt_rdata on the rvalid edge without ReadOnly
        returns the PREVIOUS bin -- which read as a clean one-bin shift across
        the whole histogram and looked exactly like the tally mis-binning.
        It was not: the tally was exact, the reader was off by one.
        """
        d = self.dut
        d.cnt_rready.value = 1
        d.cnt_araddr.value = index * 8       # 8-byte stride, one bin per beat
        d.cnt_arvalid.value = 1
        while True:
            await ReadOnly()
            hs = int(d.cnt_arready.value)
            await RisingEdge(d.aclk)
            if hs:
                d.cnt_arvalid.value = 0
                break
        v = None
        for _ in range(64):
            await ReadOnly()
            if int(d.cnt_rvalid.value):
                v = int(d.cnt_rdata.value)
                await RisingEdge(d.aclk)
                break
            await RisingEdge(d.aclk)
        assert v is not None, f"bin {index}: no cnt_rvalid within 64 cycles"
        return v

    async def read_bins(self, n, unexpected_index):
        bins = {}
        for i in range(n):
            v = await self.read_bin(i)
            if v:
                bins[i] = v
        bins["UNEXPECTED"] = await self.read_bin(unexpected_index)
        return bins
