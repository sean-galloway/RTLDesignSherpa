# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for axis4_intf_observer.

EXTENDS the AXI4 observer TB rather than copying it. The three observers share
obs_regs.rdl, the APB chain, the AXIL egress framing and the monbus record
format, so register access, the egress sink, the packet tally and the framing
check are inherited unchanged -- they are precisely what must not drift
between the flavours. What differs is the observed bus: this one is a single
AXI4-Stream channel per port, driven here by the shared AXIS master BFM
against a TB-owned tready (every obs_axis_* pin is an INPUT, tready included,
so the TB plays the sink).

Protocol VIOLATIONS cannot come from a compliant BFM. The one injected here
(TVALID dropping before the handshake, AXIS_ERR_VALID_TIMING) is driven on
the pins directly, in the one helper that says so; everything else goes
through the BFM.
"""

import os

import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.axis4.axis_factories import create_axis_master

from projects.components.misc.dv.tbclasses.axi4_intf_observer_tb import AXI4IntfObserverTB


class AXIS4IntfObserverTB(AXI4IntfObserverTB):
    """APB/register + AXIS observation TB for axis4_intf_observer."""

    def __init__(self, dut):
        super().__init__(dut)
        self.data_width = int(os.environ.get("P_DATA_WIDTH", 64))
        self.strb_all = (1 << (self.data_width // 8)) - 1
        # A stall long enough to trip MON_TIMEOUT (microseconds, so hundreds
        # of cycles) must not trip the BFM's own ready timeout first.
        self.axis = create_axis_master(
            dut=dut,
            clock=dut.aclk,
            prefix="obs_axis_",
            log=self.log,
            data_width=self.data_width,
            id_width=8,
            dest_width=4,
            user_width=1,
            timeout_cycles=20000,
        )["interface"]

    # ---- the three mandatory methods -------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock("aclk", freq=10, units="ns")
        await self.assert_reset()
        await self.wait_clocks("aclk", 10)
        await self.deassert_reset()
        await self.wait_clocks("aclk", 5)
        await self.apb.reset_bus()
        assert self.apb.is_signal_present("PSTRB"), (
            "PSTRB did not bind; every APB write would carry zero byte-strobes")
        # The TB is the stream's sink: always ready unless a scenario stalls.
        self.dut.obs_axis_tready.value = 1
        self.dut.i_meter_clear.value = 0
        self.dut.i_meter_freeze.value = 0
        self.dut.cam_clear.value = 0
        await self.wait_clocks("aclk", 5)

    # ---- AXIS stimulus, through the BFM ----------------------------------
    async def send_packet(self, beats=4, tid=0, tdest=0, gap=0, strb=None, seed=0):
        """One AXIS packet of `beats` beats, TLAST on the final one.

        gap > 0 idles the master between beats, which is what opens an
        in-packet bubble (Stream/PAUSE then RESUME) when that cone is built.
        """
        for i in range(beats):
            await self.axis.send_single_beat(
                data=(0xA5A5_0000 + seed * 0x100 + i) & ((1 << self.data_width) - 1),
                last=1 if i == beats - 1 else 0,
                id=tid, dest=tdest, user=0,
                strb=self.strb_all if strb is None else strb)
            if gap and i != beats - 1:
                await self.wait_clocks("aclk", gap)

    async def send_beat(self, last=0, tid=0, tdest=0, strb=None, data=0x1234):
        await self.axis.send_single_beat(
            data=data & ((1 << self.data_width) - 1), last=last,
            id=tid, dest=tdest, user=0,
            strb=self.strb_all if strb is None else strb)

    async def stalled_beat(self, stall_cycles, last=1, tid=0):
        """Hold tready LOW while the BFM presents a beat, for `stall_cycles`.

        The BFM keeps TVALID asserted through the stall, as AXIS requires, so
        this exercises the stall cones (Credit/BACKPRESSURE, Timeout/HANDSHAKE)
        without any protocol violation.
        """
        self.dut.obs_axis_tready.value = 0
        await self.wait_clocks("aclk", 2)
        sender = cocotb.start_soon(self.send_beat(last=last, tid=tid))
        await self.wait_clocks("aclk", stall_cycles)
        self.dut.obs_axis_tready.value = 1
        await sender
        await self.wait_clocks("aclk", 2)

    async def inject_valid_drop(self, hold=3):
        """PROTOCOL VIOLATION, pins driven directly on purpose.

        TVALID asserted, no TREADY, then TVALID withdrawn. A compliant BFM
        cannot do this, and it is the stimulus AXIS_ERR_VALID_TIMING exists
        for. The BFM is idle (tvalid low) around this, and re-drives the pin
        on its next send, so nothing is left behind.
        """
        d = self.dut
        d.obs_axis_tready.value = 0
        d.obs_axis_tvalid.value = 1
        d.obs_axis_tlast.value = 0
        for _ in range(hold):
            await RisingEdge(d.aclk)
        d.obs_axis_tvalid.value = 0
        await RisingEdge(d.aclk)
        d.obs_axis_tready.value = 1
        await self.wait_clocks("aclk", 4)

    def codes_seen(self, class_name):
        """{event_code} for one packet class, over everything captured."""
        return {code for (name, code) in self.packet_tally() if name == class_name}
