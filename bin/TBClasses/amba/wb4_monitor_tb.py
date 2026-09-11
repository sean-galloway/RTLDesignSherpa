# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for wb4_monitor (rtl/amba/wb4/wb4_monitor.sv).

The monitor only watches, so the TB owns both sides of both queues: a GAXI
master + GAXI slave pair on cmd_* (producer and consumer) and the same pair
on rsp_* (a responder coroutine answers accepted commands in order, with a
configurable latency and hold). Packets come back through the shared
MonbusSlave/parse path (TBClasses.monbus) tagged PROTOCOL_WB, and every
phase checks the packet stream against what the stimulus implies: one
completion or error per transfer, in command order, with the right address
and direction; timeouts once per stall / per entry; a latency perf packet
only over the threshold; orphan and tracking-lost errors when provoked.
"""
import os
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ACK, WB4_STATUS_ERR, WB4_STATUS_RTY
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from TBClasses.monbus import (ProtocolType, PktType, WBErrorCode, WBTimeoutCode,
                              WBCompletionCode, WBPerformanceCode, WBDebugCode)
from TBClasses.monbus.monbus_slave import MonbusSlave

ERR_WINDOW = (0x0000_E000, 0x0000_EFFF)
RTY_WINDOW = (0x0000_F000, 0x0000_FFFF)


def _status_for(adr):
    if ERR_WINDOW[0] <= adr <= ERR_WINDOW[1]:
        return WB4_STATUS_ERR
    if RTY_WINDOW[0] <= adr <= RTY_WINDOW[1]:
        return WB4_STATUS_RTY
    return WB4_STATUS_ACK


class WB4MonitorTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.AW = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DW = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.SW = self.DW // 8
        self.max_transactions = self.convert_to_int(os.environ.get('MAX_TRANSACTIONS', '8'))
        self.n_addr_ranges = self.convert_to_int(os.environ.get('N_ADDR_RANGES', '0'))
        # USE_BURST_HINTS=1 puts the transfer's CTI in aux_data[7:5]. With it
        # off those bits must read zero whatever cmd_cti was driven to, which
        # is what every consumer written before the hints existed decodes.
        self.burst_hints = os.environ.get('USE_BURST_HINTS', '0') == '1' 
        self.unit_id = self.convert_to_int(os.environ.get('UNIT_ID', '1'))
        self.agent_id = self.convert_to_int(os.environ.get('AGENT_ID', '11'))
        self.errors = []
        self.accepted = deque()       # commands taken on cmd_*, in order (responder input)
        self.expected = deque()       # (adr, we, sel, status, cti) per accepted command, in order
        self.rsp_latency = 1          # responder clocks between accept and response
        self.hold = False             # responder paused
        self.clock_count = 0          # clocks since reset release (i_mon_time)
        self.hints_seen = 0           # transfers whose reported CTI was non-classic
        self.done = False

        self.cmd_fc = FieldConfig()
        self.cmd_fc.add_field(FieldDefinition(name="we", bits=1, default=0, format="bin", display_width=1))
        self.cmd_fc.add_field(FieldDefinition(name="adr", bits=self.AW, default=0, format="hex",
                                              display_width=(self.AW + 3) // 4))
        self.cmd_fc.add_field(FieldDefinition(name="dat", bits=self.DW, default=0, format="hex",
                                              display_width=(self.DW + 3) // 4))
        self.cmd_fc.add_field(FieldDefinition(name="sel", bits=self.SW, default=(1 << self.SW) - 1,
                                              format="bin", display_width=self.SW))
        # cmd_cti is a port whatever USE_BURST_HINTS is, so it is always
        # driven: an undriven input would sit at X and the DUT would carry
        # that X into its tracking queue.
        self.cmd_fc.add_field(FieldDefinition(name="cti", bits=3, default=0, format="bin",
                                              display_width=3))
        self.rsp_fc = FieldConfig()
        self.rsp_fc.add_field(FieldDefinition(name="status", bits=2, default=0, format="dec", display_width=1))
        self.rsp_fc.add_field(FieldDefinition(name="dat", bits=self.DW, default=0, format="hex",
                                              display_width=(self.DW + 3) // 4))

        self.cmd = create_gaxi_master(
            dut, 'CMD', '', self.clk, field_config=self.cmd_fc, pkt_prefix='cmd',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            memory_model=None, log=self.log, multi_sig=True)
        self.cmd_sink = create_gaxi_slave(
            dut, 'CMD Sink', '', self.clk, field_config=self.cmd_fc, pkt_prefix='cmd',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=None, log=self.log, multi_sig=True)
        self.cmd_sink.add_callback(self._on_cmd)
        self.rsp = create_gaxi_master(
            dut, 'RSP', '', self.clk, field_config=self.rsp_fc, pkt_prefix='rsp',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            memory_model=None, log=self.log, multi_sig=True)
        self.rsp_sink = create_gaxi_slave(
            dut, 'RSP Sink', '', self.clk, field_config=self.rsp_fc, pkt_prefix='rsp',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=None, log=self.log, multi_sig=True)
        # The response side drains faster than the command side fills, so the
        # tracking queue never overflows unless a phase holds the responder.
        self.rsp_sink.ready_policy = 'always'
        # A consumer that keeps up: the event FIFO is lossy by design (the
        # family's one-write-per-clock, drop-when-full contract), so the
        # scoreboard needs the bus drained faster than events are produced.
        self.monbus = MonbusSlave(dut, 'MonBus', '', self.clk, bus_name='monbus', pkt_prefix='',
                                  expected_unit_id=self.unit_id, expected_agent_id=self.agent_id,
                                  expected_protocol=ProtocolType.PROTOCOL_WB, log=self.log,
                                  randomizer=FlexRandomizer({'ready_delay': ([(0, 0)], [1])}),
                                  ready_policy='always')
        self.monbus.add_packet_callback(self._on_packet)

    # ---- mandatory ------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        self._init_config()
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        cocotb.start_soon(self._mon_time())
        self._responder = cocotb.start_soon(self._respond())

    async def assert_reset(self):
        self.rst_n.value = 0
        await self.cmd.reset_bus()
        await self.rsp.reset_bus()

    async def deassert_reset(self):
        self.rst_n.value = 1

    def _init_config(self):
        d = self.dut
        d.i_mon_time.value = 0
        d.cfg_error_enable.value = 1
        d.cfg_timeout_enable.value = 0
        d.cfg_protocol_enable.value = 1
        d.cfg_slverr_enable.value = 1
        d.cfg_perf_enable.value = 0
        d.cfg_latency_enable.value = 0
        d.cfg_throughput_enable.value = 0
        d.cfg_debug_enable.value = 0
        d.cfg_trans_debug_enable.value = 0
        d.cfg_debug_level.value = 0
        d.cfg_cmd_timeout_cnt.value = 0
        d.cfg_rsp_timeout_cnt.value = 0
        d.cfg_latency_threshold.value = 0xFFFF_FFFF
        d.cfg_throughput_threshold.value = 0
        d.cfg_addr_check_enable.value = 0
        d.cfg_addr_range_enable.value = 0
        d.cfg_addr_range_low.value = 0
        d.cfg_addr_range_high.value = 0

    # ---- plumbing -------------------------------------------------------
    async def _mon_time(self):
        self.clock_count = 0
        while not self.done:
            await RisingEdge(self.clk)
            self.clock_count += 1
            self.dut.i_mon_time.value = self.clock_count

    def _on_cmd(self, pkt):
        adr, we, sel = int(pkt.adr), int(pkt.we), int(pkt.sel)
        status = _status_for(adr)
        # What the aux byte must report: the hint only when the DUT carries it.
        cti = int(pkt.cti) if self.burst_hints else 0
        self.accepted.append((self.clock_count, adr, we, sel, status))
        self.expected.append((adr, we, sel, status, cti))

    def _on_packet(self, p):
        self.log.info(f"MONBUS t={self.clock_count} type={p.pkt_type} code={p.event_code} "
                      f"data=0x{p.data:010X}")

    async def _respond(self):
        """Answer everything accepted so far as one burst, rsp_latency clocks
        after the first of them was taken. A per-packet send() would pace
        responses at the GAXI driver's drain rate (~3 clocks each), slower
        than the command side, and the queue would fill on its own."""
        while not self.done:
            await RisingEdge(self.clk)
            if self.hold:
                continue
            pkts = []
            while self.accepted and self.clock_count - self.accepted[0][0] >= self.rsp_latency:
                _, adr, we, sel, status = self.accepted.popleft()
                pkt = GAXIPacket(self.rsp_fc)
                pkt.status = status
                pkt.dat = adr & ((1 << self.DW) - 1)
                pkts.append(pkt)
            if pkts:
                self.log.info(f"RSP t={self.clock_count} burst of {len(pkts)}: "
                              f"{['0x%X' % int(p.dat) for p in pkts]}")
                await self.rsp.send_burst(pkts)

    async def send_orphan(self, status=WB4_STATUS_ACK):
        """A response with nothing outstanding: the responder is bypassed."""
        pkt = GAXIPacket(self.rsp_fc)
        pkt.status = status
        pkt.dat = 0xDEAD
        await self.rsp.send(pkt)

    def _cmd(self, adr, we, sel=None, dat=0, cti=0):
        pkt = GAXIPacket(self.cmd_fc)
        pkt.we, pkt.adr, pkt.dat = we, adr, dat
        pkt.sel = (1 << self.SW) - 1 if sel is None else sel
        pkt.cti = cti
        return pkt

    async def send_cmds(self, cmds):
        await self.cmd.send_burst([self._cmd(*c) for c in cmds])

    async def wait_quiet(self, clocks=40, limit=20000):
        """Wait until nothing is outstanding and the monitor bus has been idle."""
        idle = 0
        for _ in range(limit):
            await RisingEdge(self.clk)
            busy = self.accepted or int(self.dut.active_count.value) != 0 or int(self.dut.monbus_valid.value)
            idle = 0 if busy else idle + 1
            if idle >= clocks:
                return True
        self.errors.append(f"wait_quiet: still busy after {limit} clocks "
                           f"(active={int(self.dut.active_count.value)}, queued={len(self.accepted)})")
        return False

    async def trace_wires(self, cycles):
        """Per-clock view of both queues and the packet output (debug aid)."""
        d = self.dut
        for i in range(cycles):
            await RisingEdge(self.clk)
            self.log.info(
                f"T{i:04d} cmd v{int(d.cmd_valid.value)}r{int(d.cmd_ready.value)} "
                f"we{int(d.cmd_we.value)} adr 0x{int(d.cmd_adr.value):05X} | "
                f"rsp v{int(d.rsp_valid.value)}r{int(d.rsp_ready.value)} st{int(d.rsp_status.value)} | "
                f"act {int(d.active_count.value)} tc {int(d.transaction_count.value)} "
                f"ec {int(d.error_count.value)} | mon v{int(d.monbus_valid.value)}r{int(d.monbus_ready.value)}")

    # ---- packet views ---------------------------------------------------
    def take_packets(self):
        pk = list(self.monbus.received_packets)
        self.monbus.received_packets.clear()
        return pk

    @staticmethod
    def of_type(pk, ptype):
        return [p for p in pk if p.pkt_type == int(ptype)]

    @staticmethod
    def addr_of(p):
        return p.data & 0xFFFF_FFFF

    @staticmethod
    def aux_of(p):
        return (p.data >> 32) & 0xFF

    # ---- checks ---------------------------------------------------------
    def check_transfers(self, pk, expected, tag):
        """Every transfer yields one completion (ACK -> READ/WRITE, RTY) or
        one error (ERR), in command order, carrying the address and we/sel."""
        got = [p for p in pk if p.pkt_type in (int(PktType.PktTypeCompletion), int(PktType.PktTypeError))
               and not (p.pkt_type == int(PktType.PktTypeError)
                        and p.event_code in (int(WBErrorCode.WB_ERR_ORPHAN_RSP), int(WBErrorCode.WB_ERR_TRACK_LOST),
                                             int(WBErrorCode.WB_ERR_ADDR_RANGE)))]
        if len(got) != len(expected):
            self.errors.append(f"{tag}: {len(got)} transfer packets for {len(expected)} transfers")
        for i, (p, (adr, we, sel, status, cti)) in enumerate(zip(got, expected)):
            if status == WB4_STATUS_ERR:
                want = (int(PktType.PktTypeError), int(WBErrorCode.WB_ERR_ERR))
            elif status == WB4_STATUS_RTY:
                want = (int(PktType.PktTypeCompletion), int(WBCompletionCode.WB_COMPL_RTY))
            else:
                want = (int(PktType.PktTypeCompletion),
                        int(WBCompletionCode.WB_COMPL_WRITE if we else WBCompletionCode.WB_COMPL_READ))
            # aux_data = {cti[2:0], sel[3:0], we}: the hint rides in the
            # tracking entry, so a completion must carry the CTI of ITS OWN
            # transfer even with several open at once.
            aux = ((cti & 0x7) << 5) | ((sel & 0xF) << 1) | we
            self.hints_seen += int(cti != 0 and self.aux_of(p) == aux)
            have = (p.pkt_type, p.event_code)
            if have != want or self.addr_of(p) != (adr & 0xFFFF_FFFF) or self.aux_of(p) != aux:
                self.errors.append(f"{tag}[{i}]: got type/code {have} addr 0x{self.addr_of(p):X} aux 0x{self.aux_of(p):X}, "
                                   f"want {want} addr 0x{adr:X} aux 0x{aux:X}")
                if len(self.errors) > 12:
                    break

    def report(self):
        st = self.monbus.monbus_stats
        self.log.info(f"monbus: received={len(self.monbus.received_packets)} raw={st['raw_gaxi_packets']} "
                      f"verification_errors={st['verification_errors']} wb={st.get('wb_packets', 0)}")
        if st['verification_errors']:
            self.errors.append(f"MonbusSlave verification errors: {st['verification_error_list'][:4]}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
