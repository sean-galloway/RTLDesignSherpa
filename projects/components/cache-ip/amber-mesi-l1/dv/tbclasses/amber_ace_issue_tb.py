"""
amber_ace_issue unit-side row suite

Task 12 Step 1: per MAS ch02/08 Table 2.8.1 ROW, drive the cache event at
the block's event inputs and capture the transaction on the wrapper-side
pins: ARSNOOP/AWSNOOP value, address, burst length, AW-only behavior (no W
beats follow CleanUnique/MakeUnique/Evict), and the B-response swallow that
keeps the drain engine from seeing AW-only write responses.

The DUT is the dv/tb/amber_ace_issue_th wrapper (pure wiring): the block's
engine-side and wrapper-side pins are top-level ports.

Author: RTL Design Sherpa
Created: 2026-10-09
"""

import os

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

# Table 2.8.1 snoop-field encodings (the block's localparams, mirrored here
# as the golden). ARSNOOP[3:0] / AWSNOOP[2:0]; framework ACETransactionType
# values where they fit the wire width (READ_SHARED=0x1, READ_UNIQUE=0x7,
# WRITE_BACK=0x3, EVICT=0x5, MAKE_UNIQUE=0xC -> low-3 0x4); CleanUnique's
# framework value (0xB) collides with WriteBack under 3-bit truncation so
# the family AWSNOOP assigns the next free code 0x6.
ARSNOOP_READ_SHARED = 0x1
ARSNOOP_READ_UNIQUE = 0x7
AWSNOOP_CLEAN_UNIQUE = 0x6
AWSNOOP_MAKE_UNIQUE = 0x4
AWSNOOP_WRITE_BACK = 0x3
AWSNOOP_EVICT = 0x5

# amber_ace_req_t (amber_pkg)
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE, ACE_MAKE_UNIQUE, \
    ACE_WRITE_BACK, ACE_EVICT = range(6)

# the block's default AW-only AWID (parameter AWONLY_ID)
AWONLY_ID = 0x01


class AmberAceIssueTB(TBBase):
    """Drives the Table 2.8.1 rows and scores the wrapper-side pins."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.ADDR_WIDTH = 32
        self.BUS_WIDTH = int(os.environ.get('BUS_WIDTH', '64'))
        self.STRB_W = self.BUS_WIDTH // 8
        self.checks = 0
        self.mismatches = 0
        self.cyc = 0

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            self.log.error(f"CHECK FAIL: {what}: got {got!r} "
                           f"expected {exp!r}")

    async def _negedge_settled(self):
        await FallingEdge(self.dut.clk)
        await Timer(500, units='ps')

    def _defaults(self):
        """Benign quiescent input state (engine idle, wrappers ready)."""
        d = self.dut
        d.ace_rd_req.value = 0
        d.ace_rd_type.value = 0
        d.ace_rd_addr.value = 0
        d.ace_rd_len.value = 0
        d.ace_wr_req.value = 0
        d.ace_wr_type.value = 0
        d.ace_wr_addr.value = 0
        d.ace_wr_len.value = 0
        d.eng_arid.value = 0
        d.eng_araddr.value = 0
        d.eng_arlen.value = 0
        d.eng_arsize.value = 0
        d.eng_arburst.value = 0
        d.eng_arlock.value = 0
        d.eng_arcache.value = 0
        d.eng_arprot.value = 0
        d.eng_arqos.value = 0
        d.eng_arregion.value = 0
        d.eng_aruser.value = 0
        d.eng_arvalid.value = 0
        d.eng_awid.value = 0
        d.eng_awaddr.value = 0
        d.eng_awlen.value = 0
        d.eng_awsize.value = 0
        d.eng_awburst.value = 0
        d.eng_awlock.value = 0
        d.eng_awcache.value = 0
        d.eng_awprot.value = 0
        d.eng_awqos.value = 0
        d.eng_awregion.value = 0
        d.eng_awuser.value = 0
        d.eng_awvalid.value = 0
        d.eng_bready.value = 0
        d.fub_arready.value = 1
        d.fub_awready.value = 1
        d.fub_bid.value = 0
        d.fub_bresp.value = 0
        d.fub_buser.value = 0
        d.fub_bvalid.value = 0

    async def setup(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self._defaults()
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 3)
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 2)

    # ------------------------------------------------------------------
    # read-side rows: ReadShared / ReadUnique on arsnoop[3:0]
    # ------------------------------------------------------------------
    async def _read_row(self, name, req_type, exp_snoop):
        d = self.dut
        addr = 0x0002_4000
        arlen = 7
        # the cache event (fill launch) pulses one cycle before the fill
        # engine raises AR -- the block latches the class and stamps it on
        # the engine's AR
        d.ace_rd_addr.value = addr
        d.ace_rd_len.value = arlen
        d.ace_rd_type.value = req_type
        d.ace_rd_req.value = 1
        await self._negedge_settled()
        d.ace_rd_req.value = 0
        # engine raises AR the next cycle(s); hold it under backpressure
        # for 3 cycles and check the snoop field is stable throughout
        d.eng_araddr.value = addr
        d.eng_arlen.value = arlen
        d.eng_arvalid.value = 1
        d.fub_arready.value = 0
        for _ in range(3):
            await self._negedge_settled()
            self._score(f"{name}: arvalid held under backpressure",
                        int(d.fub_arvalid.value), 1)
            self._score(f"{name}: arsnoop", int(d.fub_arsnoop.value),
                        exp_snoop)
            self._score(f"{name}: araddr passthrough",
                        int(d.fub_araddr.value), addr)
            self._score(f"{name}: arlen passthrough",
                        int(d.fub_arlen.value), arlen)
            self._score(f"{name}: arid passthrough", int(d.fub_arid.value),
                        int(d.eng_arid.value))
        d.fub_arready.value = 1
        await self._negedge_settled()
        self._score(f"{name}: engine sees the accept",
                    int(d.eng_arready.value), 1)
        d.eng_arvalid.value = 0
        await self._negedge_settled()

    # ------------------------------------------------------------------
    # AW-only rows: CleanUnique / MakeUnique / Evict on awsnoop[2:0]
    # ------------------------------------------------------------------
    async def _awonly_row(self, name, req_type, exp_snoop):
        d = self.dut
        addr = 0x0003_8000
        awlen = 7
        d.ace_wr_addr.value = addr
        d.ace_wr_len.value = awlen
        d.ace_wr_type.value = req_type
        d.ace_wr_req.value = 1
        await self._negedge_settled()
        d.ace_wr_req.value = 0
        # the block originates the AW (engine AW is low): hold under
        # backpressure, check the full payload + snoop
        d.fub_awready.value = 0
        for _ in range(3):
            await self._negedge_settled()
            self._score(f"{name}: awvalid held under backpressure",
                        int(d.fub_awvalid.value), 1)
            self._score(f"{name}: awsnoop", int(d.fub_awsnoop.value),
                        exp_snoop)
            self._score(f"{name}: awaddr", int(d.fub_awaddr.value), addr)
            self._score(f"{name}: awlen", int(d.fub_awlen.value), awlen)
            self._score(f"{name}: awid is the AW-only tag",
                        int(d.fub_awid.value), AWONLY_ID)
            self._score(f"{name}: INCR burst", int(d.fub_awburst.value), 1)
            self._score(f"{name}: full-line size",
                        int(d.fub_awsize.value),
                        (self.STRB_W - 1).bit_length())
            self._score(f"{name}: engine AW untouched",
                        int(d.eng_awready.value), 0)
        d.fub_awready.value = 1
        await self._negedge_settled()
        self._score(f"{name}: AW-only accepted", int(d.fub_awvalid.value), 0)
        # the manager returns B with bid = AWONLY_ID: the block swallows it
        # (fub_bready high, eng_bvalid low) -- the drain engine never sees
        # an AW-only response
        d.fub_bid.value = AWONLY_ID
        d.fub_bvalid.value = 1
        d.eng_bready.value = 0
        await self._negedge_settled()
        self._score(f"{name}: AW-only B swallowed (eng_bvalid)",
                    int(d.eng_bvalid.value), 0)
        self._score(f"{name}: AW-only B swallowed (fub_bready)",
                    int(d.fub_bready.value), 1)
        d.fub_bvalid.value = 0
        await self._negedge_settled()

    # ------------------------------------------------------------------
    # WriteBack row: engine AW passes through with awsnoop = WriteBack
    # ------------------------------------------------------------------
    async def _writeback_row(self):
        d = self.dut
        name = 'WriteBack'
        addr = 0x0004_C000
        # the event fires (dirty eviction launch) but the drain engine
        # carries the AW: the module stamps WriteBack, no AW originates
        d.ace_wr_addr.value = addr
        d.ace_wr_len.value = 7
        d.ace_wr_type.value = ACE_WRITE_BACK
        d.ace_wr_req.value = 1
        await self._negedge_settled()
        d.ace_wr_req.value = 0
        await self._negedge_settled()
        self._score(f"{name}: no AW originates for WriteBack",
                    int(d.fub_awvalid.value), 0)
        d.eng_awaddr.value = addr
        d.eng_awlen.value = 7
        d.eng_awvalid.value = 1
        await self._negedge_settled()
        self._score(f"{name}: awsnoop", int(d.fub_awsnoop.value),
                    AWSNOOP_WRITE_BACK)
        self._score(f"{name}: awaddr passthrough",
                    int(d.fub_awaddr.value), addr)
        self._score(f"{name}: awid passthrough", int(d.fub_awid.value),
                    int(d.eng_awid.value))
        d.fub_awready.value = 0
        await self._negedge_settled()
        self._score(f"{name}: awvalid held under backpressure",
                    int(d.fub_awvalid.value), 1)
        self._score(f"{name}: engine sees the hold",
                    int(d.eng_awready.value), 0)
        d.fub_awready.value = 1
        await self._negedge_settled()
        self._score(f"{name}: engine sees the accept",
                    int(d.eng_awready.value), 1)
        d.eng_awvalid.value = 0
        # the drain engine's own B (bid 0) passes straight through
        d.fub_bid.value = 0
        d.fub_bresp.value = 0
        d.fub_bvalid.value = 1
        d.eng_bready.value = 0
        await self._negedge_settled()
        self._score(f"{name}: engine B visible (eng_bvalid)",
                    int(d.eng_bvalid.value), 1)
        self._score(f"{name}: engine B held by eng_bready",
                    int(d.fub_bready.value), 0)
        d.eng_bready.value = 1
        await self._negedge_settled()
        self._score(f"{name}: engine B accepted", int(d.eng_bvalid.value), 1)
        d.fub_bvalid.value = 0
        d.eng_bready.value = 0
        await self._negedge_settled()

    # ------------------------------------------------------------------
    # run
    # ------------------------------------------------------------------
    async def run(self):
        await self._read_row('ReadShared', ACE_READ_SHARED,
                             ARSNOOP_READ_SHARED)
        await self._read_row('ReadUnique', ACE_READ_UNIQUE,
                             ARSNOOP_READ_UNIQUE)
        await self._awonly_row('CleanUnique', ACE_CLEAN_UNIQUE,
                               AWSNOOP_CLEAN_UNIQUE)
        await self._awonly_row('MakeUnique', ACE_MAKE_UNIQUE,
                               AWSNOOP_MAKE_UNIQUE)
        await self._writeback_row()
        await self._awonly_row('Evict', ACE_EVICT, AWSNOOP_EVICT)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
