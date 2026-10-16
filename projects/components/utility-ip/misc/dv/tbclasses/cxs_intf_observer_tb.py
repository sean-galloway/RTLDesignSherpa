# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for cxs_intf_observer.

EXTENDS the AXI4 observer TB, as the AXIS observer TB does: obs_regs, the APB
chain, the egress sink, the packet tally and the record-framing check are
inherited unchanged, because they are what must not drift between the
observer flavours. What differs is the observed bus: one credited CXS link per
port, played end to end by the RDS-DV CXSTransmitter and CXSReceiver on the
obs_cxs_* pins (every one an observer INPUT, the receiver's CRDGNT and
ACTIVEACK included).

A compliant BFM pair cannot commit a protocol violation. The one injected here
(CXSVALID with no credit held) is forced on the pins directly, in the one
helper that says so.
"""

import os

from cocotb.triggers import ReadOnly, RisingEdge, Timer

from CocoTBFramework.components.cxs import (CXSConfig, CXSPacket, CXSPacketizer,
                                            create_cxs_receiver, create_cxs_transmitter)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

from projects.components.utility_ip.misc.dv.tbclasses.axi4_intf_observer_tb import AXI4IntfObserverTB


class CXSIntfObserverTB(AXI4IntfObserverTB):
    """APB/register + CXS link observation TB for cxs_intf_observer."""

    def __init__(self, dut):
        super().__init__(dut)
        self.data_width = int(os.environ.get("P_DATA_WIDTH", 512))
        self.max_credit = int(os.environ.get("P_MAX_CREDIT", 15))
        self.cfg = CXSConfig(issue='D', data_width=self.data_width, max_pkt_per_flit=2,
                             start_align=16, srcid_width=8, tgtid_width=4,
                             max_credit=self.max_credit,
                             credit_beyond_spec=self.max_credit > 63,
                             link_control=True).validate()
        self.tx = create_cxs_transmitter(dut, 'CXS TX', 'obs_cxs_', dut.aclk, self.cfg,
                                         reset=dut.aresetn, idle_deactivate=16, log=self.log)
        self.rx = create_cxs_receiver(dut, 'CXS RX', 'obs_cxs_', dut.aclk, self.cfg,
                                      reset=dut.aresetn, log=self.log)

    # ---- the three mandatory methods -------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock("aclk", freq=10, units="ns")
        self.dut.obs_cxs_prcltype.value = 0       # no CXSPRCLTYPE on this link
        await self.assert_reset()
        await self.wait_clocks("aclk", 10)
        await self.deassert_reset()
        await self.wait_clocks("aclk", 5)
        await self.apb.reset_bus()
        assert self.apb.is_signal_present("PSTRB"), (
            "PSTRB did not bind; every APB write would carry zero byte-strobes")
        self.dut.i_meter_clear.value = 0
        self.dut.i_meter_freeze.value = 0
        self.dut.cam_clear.value = 0
        await self.wait_clocks("aclk", 5)

    # ---- CXS stimulus, through the BFMs ----------------------------------
    def flits_for(self, srcid, nbytes, seed=0):
        """The flits one packet of nbytes (a multiple of 4) on stream srcid becomes."""
        payload = bytes((seed + i) & 0xFF for i in range(nbytes))
        p = CXSPacketizer(self.cfg)
        p.add(CXSPacket(payload, srcid=srcid))
        return p.flush()

    async def send_flits(self, flits, timeout=200000):
        target = self.tx.stats['flits'] + len(flits)
        for f in flits:
            self.tx.send_flit(f)
        for _ in range(timeout):
            if self.tx.stats['flits'] >= target:
                return True
            await RisingEdge(self.dut.aclk)
        return False

    def throttle(self, grant_gap):
        """Space the receiver's grants: with credits exhausted the link sits
        in RUN with none held, which the observer meters as backpressure."""
        self.rx.set_randomizer(FlexRandomizer({'grant_gap': ([(grant_gap, grant_gap)], [1]),
                                               'drain_gap': ([(0, 0)], [1]),
                                               'ack_delay': ([(0, 0)], [1])}))

    async def inject_valid_without_credit(self):
        """PROTOCOL VIOLATION, pins forced directly on purpose: CXSVALID for
        one cycle with the link idle and no credit held. A compliant
        transmitter cannot do this."""
        d = self.dut
        await RisingEdge(d.aclk)
        credits = await self.read_stat(metric=17)
        self.log.info(f"violation: link {self.tx.link_state}, snoop credits={credits} before the forced flit")
        # A deposit 1 ns after the edge, not a Force: Verilator ignores a
        # Force on this pin (it read back 0). The DUT samples the deposit at
        # the next edge; the BFM is idle in STOP and the pin is cleared after.
        await Timer(1, 'ns')
        d.obs_cxs_valid.value = 1
        await ReadOnly()
        seen = int(d.obs_cxs_valid.value)        # what the next edge samples
        await RisingEdge(d.aclk)
        await Timer(1, 'ns')
        d.obs_cxs_valid.value = 0
        self.log.info(f"violation: obs_cxs_valid presented {seen} into the sampling edge")
        await self.wait_clocks("aclk", 4)

    def codes_seen(self, class_name):
        return {code for (name, code) in self.packet_tally() if name == class_name}
