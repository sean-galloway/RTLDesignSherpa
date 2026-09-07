"""Testbench for axi4_subtractive_slave.

The property under test is NOT "does it return the right data" -- it returns
deliberate garbage. It is:

    an access this fabric cannot route COMPLETES, with an error, instead of
    hanging the master forever.

That distinction drives every check here. A hang is the failure mode the
module exists to remove (BRIDGE-009), so every phase is written so that a
regression shows up as a timeout or a missing beat, never as a silently
tolerated stall.
"""

import os

import cocotb
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


class AXI4SubtractiveSlaveTB(TBBase):
    """Drives the catch-all slave and checks it always answers."""

    DECERR = 0b11
    FILL32 = 0xDEADBEEF

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.aclk = dut.aclk
        self.aresetn = dut.aresetn
        self.IW = int(os.environ.get('TEST_ID_WIDTH', 8))
        self.AW = int(os.environ.get('TEST_ADDR_WIDTH', 32))
        self.DW = int(os.environ.get('TEST_DATA_WIDTH', 32))
        self.fill = self._fill_for_width()

    def _fill_for_width(self):
        reps = (self.DW + 31) // 32
        wide = 0
        for i in range(reps):
            wide |= self.FILL32 << (32 * i)
        return wide & ((1 << self.DW) - 1)

    # ---- the three mandatory TB methods --------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)

    async def assert_reset(self):
        self.aresetn.value = 0
        self._idle_inputs()

    async def deassert_reset(self):
        self.aresetn.value = 1

    def _idle_inputs(self):
        d = self.dut
        for sig, val in (('s_axi_awvalid', 0), ('s_axi_wvalid', 0),
                         ('s_axi_bready', 0), ('s_axi_arvalid', 0),
                         ('s_axi_rready', 0), ('monbus_ready', 1)):
            getattr(d, sig).value = val
        for sig in ('s_axi_awid', 's_axi_awaddr', 's_axi_awlen',
                    's_axi_wdata', 's_axi_wlast',
                    's_axi_arid', 's_axi_araddr', 's_axi_arlen'):
            getattr(d, sig).value = 0

    # ---- phases ---------------------------------------------------------
    async def write_burst(self, addr, wid, beats, w_before_aw=False):
        """One write. Returns (bid, bresp). Times out rather than hanging."""
        d = self.dut

        async def drive_w():
            for i in range(beats):
                d.s_axi_wdata.value = 0xA5A5_0000 + i
                d.s_axi_wlast.value = 1 if i == beats - 1 else 0
                d.s_axi_wvalid.value = 1
                await RisingEdge(self.aclk)
                # BOUNDED. An unbounded wait turns a deadlock into a test
                # timeout with no message, which is how a hang gets written
                # off as "slow" instead of diagnosed.
                for _ in range(200):
                    if d.s_axi_wready.value == 1:
                        break
                    await RisingEdge(self.aclk)
                else:
                    d.s_axi_wvalid.value = 0
                    raise AssertionError(
                        f"WREADY never rose for beat {i} of {beats} -- the slave "
                        "is gating write data on having seen AW, which deadlocks "
                        "any master that issues its data phase first")
            d.s_axi_wvalid.value = 0
            d.s_axi_wlast.value = 0

        async def drive_aw():
            d.s_axi_awid.value = wid
            d.s_axi_awaddr.value = addr
            d.s_axi_awlen.value = beats - 1
            d.s_axi_awvalid.value = 1
            await RisingEdge(self.aclk)
            while d.s_axi_awready.value != 1:
                await RisingEdge(self.aclk)
            d.s_axi_awvalid.value = 0

        # W-before-AW is legal AXI and is the classic way to deadlock a slave
        # that gates WREADY on having seen the address.
        #
        # The data phase must complete BEFORE the address is issued, and be
        # awaited. An earlier version started W in the background and sent AW
        # anyway a few cycles later: that unblocks a gated WREADY, so it
        # passed against a deliberately broken slave. A test that cannot fail
        # is not evidence.
        if w_before_aw:
            await drive_w()
            await drive_aw()
        else:
            await drive_aw()
            await drive_w()

        d.s_axi_bready.value = 1
        for _ in range(200):
            await RisingEdge(self.aclk)
            if d.s_axi_bvalid.value == 1:
                bid = int(d.s_axi_bid.value)
                bresp = int(d.s_axi_bresp.value)
                await RisingEdge(self.aclk)
                d.s_axi_bready.value = 0
                return bid, bresp
        raise AssertionError(
            f"no B response within 200 cycles for addr=0x{addr:x} id={wid} -- "
            "this is the hang BRIDGE-009 exists to prevent")

    async def read_burst(self, addr, rid, beats):
        """One read. Returns list of (rid, rdata, rresp, rlast)."""
        d = self.dut
        d.s_axi_arid.value = rid
        d.s_axi_araddr.value = addr
        d.s_axi_arlen.value = beats - 1
        d.s_axi_arvalid.value = 1
        await RisingEdge(self.aclk)
        for _ in range(200):
            if d.s_axi_arready.value == 1:
                break
            await RisingEdge(self.aclk)
        else:
            raise AssertionError(f"AR never accepted for addr=0x{addr:x}")
        d.s_axi_arvalid.value = 0

        out = []
        d.s_axi_rready.value = 1
        for _ in range(200 + beats * 4):
            await RisingEdge(self.aclk)
            if d.s_axi_rvalid.value == 1:
                out.append((int(d.s_axi_rid.value), int(d.s_axi_rdata.value),
                            int(d.s_axi_rresp.value), int(d.s_axi_rlast.value)))
                if out[-1][3]:
                    break
        d.s_axi_rready.value = 0
        if not out or not out[-1][3]:
            raise AssertionError(
                f"read of {beats} beat(s) at 0x{addr:x} never returned RLAST "
                f"(got {len(out)} beat(s)) -- burst masters would hang here")
        return out
