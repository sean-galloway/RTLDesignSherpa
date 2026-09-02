# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for axi4_intf_{master,slave}_observer.

ONE TB for BOTH observers on purpose. They share obs_regs.rdl, consume an
identical 17-register set and carry identical parameter lists; the only
difference is which monitor flavour they instantiate
(axi4_master_{rd,wr}_mon vs axi4_slave_{rd,wr}_mon). A second TB would be a
second thing to keep in sync, and the register map is exactly what must not
drift between them.

WHY THIS EXISTS AT ALL: until now neither observer had any component-level DV.
Both were exercised only through a 20-minute full-harness simulation in another
project, which is why the following all survived unnoticed:

  - ENABLE_MON_TAPS hardcoded 1'b0, so the monitors were built DISABLED
  - the reporter cones compiled out, so cfg_compl_enable=1 drove nothing
  - N_ADDR_RANGES=0, making ADDR_MATCH packets structurally impossible
  - 26 config inputs tied to constants and reachable from nowhere
  - nothing ever writing the observer's own APB

Every one of those is a register-layer fact this TB can assert in seconds.
"""

import os
import sys
from pathlib import Path

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_packet import APBPacket
from TBClasses.monbus import parse as monbus_parse
from TBClasses.monbus.monbus_types import PktType


def _regmap_offsets() -> dict:
    """name -> byte offset, from the SAME generated regmap the host tools use.

    Never hardcode an offset here. The regblock is shared with Genesys 2 stream
    and NexysA7 pumice; a pasted constant is how a register move becomes a
    silent readback of the wrong thing.
    """
    here = Path(__file__).resolve()
    gen = here.parents[2] / "rtl" / "regs" / "generated"
    sys.path.insert(0, str(gen))
    import obs_regs_top_regmap as rm  # noqa: E402

    out = {}
    for name, body in rm.top_block.items():
        if not isinstance(body, dict) or body.get("type") != "reg":
            continue
        addr = body.get("address", body.get("offset"))
        out[name] = int(str(addr), 0)
    if not out:
        raise RuntimeError("no register offsets parsed from obs_regs_top_regmap")
    return out


class AXI4IntfObserverTB(TBBase):
    """APB/register-layer TB for either observer flavour."""

    def __init__(self, dut):
        super().__init__(dut)
        self.regs = _regmap_offsets()
        self.apb = APBMaster(
            entity=dut,
            title="OBS APB Master",
            prefix="s_apb_",
            clock=dut.aclk,
            bus_width=32,
            addr_width=12,
            log=self.log,
        )

    # ---- the three mandatory methods -------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock("aclk", freq=10, units="ns")
        await self.assert_reset()
        await self.wait_clocks("aclk", 10)
        await self.deassert_reset()
        await self.wait_clocks("aclk", 5)
        await self.apb.reset_bus()
        # These monitors are PASS-THROUGHS, not passive taps. They re-drive
        # m_axi_* through a skid, and the handshake the transaction manager
        # tracks is the DOWNSTREAM one: cmd_valid = m_axi_awvalid (the
        # monitor's own output), cmd_ready = m_axi_awready (obs_wr_awready).
        # Pulsing ready for one cycle alongside valid meant the monitor
        # asserted its output after the ready had already gone -- cmd_valid
        # stuck high forever, the AW never handshook, and every write's data
        # had no entry to attach to. That surfaced as AXI_ERR_PROTOCOL on the
        # master and looked exactly like a DUT bug. Behave like a real
        # always-ready downstream slave instead.
        self.dut.obs_rd_arready.value = 1
        self.dut.obs_wr_awready.value = 1
        self.dut.obs_wr_wready.value = 1
        # No manual PSTRB drive here on purpose. cocotb_bus binds OPTIONAL
        # signals with a case-SENSITIVE hasattr while required ones are
        # case-insensitive, so on this lowercase DUT PSTRB used to vanish and
        # every write went out with zero byte-strobes. Fixed in the BFM
        # (APBSignalMixin._match_optional_case); this asserts that fix holds.
        for _sig in ("PSTRB", "PPROT", "PSLVERR"):
            bound = self.apb.is_signal_present(_sig)
            self.log.info(f"APB optional signal {_sig} bound: {bound}")
        assert self.apb.is_signal_present("PSTRB"), (
            "PSTRB did not bind. This DUT names its APB ports lowercase; "
            "cocotb_bus gates OPTIONAL signals on a case-sensitive hasattr, so "
            "PSTRB silently disappears and every write carries zero byte-strobes "
            "-- writes are accepted and do nothing.")
        await self.wait_clocks("aclk", 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- register access, BY NAME ----------------------------------------
    def off(self, name: str) -> int:
        if name not in self.regs:
            raise KeyError(f"unknown observer register {name!r}; "
                           f"have {len(self.regs)}: {sorted(self.regs)[:8]}...")
        return self.regs[name]

    async def _xfer(self, pwrite: int, addr: int, data: int = 0) -> int:
        pkt = APBPacket(pwrite=pwrite, paddr=addr, pwdata=data, pstrb=0xF,
                        pprot=0, data_width=32, addr_width=12, strb_width=4)
        pkt.direction = "WRITE" if pwrite else "READ"
        if not hasattr(self.apb, "transmit_coroutine"):
            self.apb.transmit_coroutine = None
        await self.apb.send(pkt)
        for _ in range(100):
            await RisingEdge(self.dut.aclk)
            if (self.dut.s_apb_psel.value and self.dut.s_apb_penable.value
                    and self.dut.s_apb_pready.value):
                break
        rd = int(self.dut.s_apb_prdata.value)
        await RisingEdge(self.dut.aclk)
        return rd

    async def write_reg(self, name: str, value: int):
        await self._xfer(1, self.off(name), value)

    async def read_reg(self, name: str) -> int:
        return await self._xfer(0, self.off(name))

    # ---- traffic + egress ------------------------------------------------
    # obs_rd_*/obs_wr_* are pure INPUTS -- observation taps, not a pass-through
    # -- so the TB plays the bus being watched. There is no AXI slave here to
    # drive with a BFM; these signals only need to look like a real handshake.

    async def start_egress_sink(self):
        """Accept the monbus group's AXIL writes and DECODE the records.

        Counting beats is not verification -- it cannot tell a completion from
        an error, and it cannot explain why two observers emit different
        totals. Records are RAW 3-beat (ts, packet[127:64], packet[63:0]);
        beats 1 and 2 reassemble the 128-bit packet, which the SHARED decoder
        turns into fields. Never hand-shift monbus bits in a TB.

        Without a sink the group's write FIFO fills and the taps back-pressure,
        which looks exactly like "the monitors never emitted".
        """
        self.egress_beats = 0
        self.packets = []           # decoded MonitorPacket objects
        self.records = []           # full 192-bit wire records
        self._rec = []              # partial 3-beat record
        self.dut.m_axil_awready.value = 1
        self.dut.m_axil_wready.value = 1
        self.dut.m_axil_bvalid.value = 0
        self.dut.m_axil_bresp.value = 0

        async def _sink():
            while True:
                await RisingEdge(self.dut.aclk)
                if int(self.dut.m_axil_wvalid.value) and int(self.dut.m_axil_wready.value):
                    self._rec.append(int(self.dut.m_axil_wdata.value))
                    if len(self._rec) == 3:
                        # 192-bit wire record: beat0 = {tag[3:0], source_ts[59:0]},
                        # beat1 = packet[127:64], beat2 = packet[63:0]. Keep all
                        # three -- the framing is as much a contract as the
                        # packet, and it must be IDENTICAL on both observers.
                        self.records.append(tuple(self._rec))
                        pkt = (self._rec[1] << 64) | self._rec[2]
                        self.packets.append(monbus_parse(pkt))
                        self._rec = []
                if int(self.dut.m_axil_awvalid.value) and int(self.dut.m_axil_awready.value):
                    self.egress_beats += 1
                    self.dut.m_axil_bvalid.value = 1
                elif int(self.dut.m_axil_bready.value) and int(self.dut.m_axil_bvalid.value):
                    self.dut.m_axil_bvalid.value = 0
        cocotb.start_soon(_sink())

    async def drive_read_burst(self, addr=0x1000, arid=0, beats=4, rresp=0, gap=3):
        """AR, then a gap, then the R beats.

        The gap is not cosmetic. Driving R in the cycle after AR made the
        MASTER observer report AXI_ERR_DATA_ORPHAN and AXI_ERR_PROTOCOL on
        otherwise clean traffic -- the monitor had not finished registering
        the address when the data arrived, which is a real protocol
        complaint about the stimulus, not a DUT fault.
        """
        d = self.dut
        d.obs_rd_araddr.value = addr; d.obs_rd_arid.value = arid
        d.obs_rd_arlen.value = beats - 1; d.obs_rd_arsize.value = 3
        d.obs_rd_arburst.value = 1; d.obs_rd_arvalid.value = 1
        await RisingEdge(d.aclk)
        d.obs_rd_arvalid.value = 0
        for _ in range(gap):
            await RisingEdge(d.aclk)
        for i in range(beats):
            d.obs_rd_rid.value = arid; d.obs_rd_rdata.value = 0xA5A5_0000 + i
            d.obs_rd_rresp.value = rresp
            d.obs_rd_rlast.value = 1 if i == beats - 1 else 0
            d.obs_rd_rvalid.value = 1; d.obs_rd_rready.value = 1
            await RisingEdge(d.aclk)
        d.obs_rd_rvalid.value = 0; d.obs_rd_rready.value = 0
        d.obs_rd_rlast.value = 0; d.obs_rd_rresp.value = 0
        for _ in range(gap):
            await RisingEdge(d.aclk)

    async def drive_write_burst(self, addr=0x2000, awid=0, beats=4, bresp=0, gap=3):
        """AW, gap, W beats, gap, B -- never W before AW."""
        d = self.dut
        d.obs_wr_awaddr.value = addr; d.obs_wr_awid.value = awid
        d.obs_wr_awlen.value = beats - 1; d.obs_wr_awsize.value = 3
        d.obs_wr_awburst.value = 1; d.obs_wr_awvalid.value = 1
        await RisingEdge(d.aclk)
        d.obs_wr_awvalid.value = 0
        for _ in range(gap):
            await RisingEdge(d.aclk)
        for i in range(beats):
            d.obs_wr_wdata.value = 0x5A5A_0000 + i; d.obs_wr_wstrb.value = 0xFF
            d.obs_wr_wlast.value = 1 if i == beats - 1 else 0
            d.obs_wr_wvalid.value = 1
            await RisingEdge(d.aclk)
        d.obs_wr_wvalid.value = 0; d.obs_wr_wlast.value = 0
        for _ in range(gap):
            await RisingEdge(d.aclk)
        d.obs_wr_bid.value = awid; d.obs_wr_bresp.value = bresp
        d.obs_wr_bvalid.value = 1; d.obs_wr_bready.value = 1
        await RisingEdge(d.aclk)
        d.obs_wr_bvalid.value = 0; d.obs_wr_bready.value = 0; d.obs_wr_bresp.value = 0
        for _ in range(gap):
            await RisingEdge(d.aclk)

    async def read_stat(self, tap=0, channel=0, metric=0, is_write=0):
        """OBS_STAT_SEL / OBS_STAT_DATA indexed telemetry read."""
        sel = (tap & 0xFF) | ((channel & 0xFF) << 8) | ((metric & 0xFF) << 16) \
              | ((is_write & 1) << 24)
        await self.write_reg("OBS_STAT_SEL", sel)
        return await self.read_reg("OBS_STAT_DATA")

    def packet_tally(self):
        """{(packet_type_name, event_code): count} over everything captured."""
        tally = {}
        for pk in self.packets:
            try:
                name = PktType(pk.packet_type).name.replace("PktType", "")
            except ValueError:
                name = f"type{pk.packet_type}"
            key = (name, pk.event_code)
            tally[key] = tally.get(key, 0) + 1
        return tally

    def types_seen(self):
        return {k[0] for k in self.packet_tally()}

    def log_tally(self, label):
        tally = self.packet_tally()
        self.log.info(f"[{label}] {len(self.packets)} packets, "
                      f"{self.egress_beats} beats")
        for (name, code), n in sorted(tally.items()):
            self.log.info(f"    {name:<12} event_code={code:<3} x{n}")
        return tally

    def check_record_framing(self):
        """Validate the 192-bit wire record, not just the packet.

        beat0 = {tag[3:0]=0, source_ts[59:0]}. The framing is a contract both
        observers must honour identically -- a flavour that framed records
        differently would still decode into plausible packets, so checking
        only the 128-bit payload would miss it.
        """
        assert self.records, "no records captured"
        # NOT strictly monotonic, and requiring that was my error: the read and
        # write monitors are independent sources merged by an arbiter, each
        # stamping at its own event time. A slightly older record legitimately
        # follows a newer one out of the merge. Check what IS contractual --
        # the tag nibble and a running, plausible timestamp -- and report the
        # reordering depth instead of failing on it.
        max_back = 0
        last_ts = -1
        for i, (b0, _hi, _lo) in enumerate(self.records):
            tag = (b0 >> 60) & 0xF
            ts = b0 & ((1 << 60) - 1)
            assert tag == 0, f"record {i}: beat0 tag={tag}, expected 0"
            assert ts > 0, f"record {i}: source_ts is 0 -- timebase not running"
            if ts < last_ts:
                max_back = max(max_back, last_ts - ts)
            last_ts = max(last_ts, ts)
        self.log.info(f"framing OK: {len(self.records)} records, "
                      f"max out-of-order timestamp depth {max_back}")
        assert max_back < 64, (
            f"records reordered by {max_back} ticks -- far beyond arbiter "
            f"interleave; the timebase or the merge is wrong")
        return len(self.records)
