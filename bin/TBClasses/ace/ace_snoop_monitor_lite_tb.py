# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: AXI4ACESnoopMonitorLiteTB
# Purpose: Testbench for axi4ace_snoop_monitor_lite through the fixture
#          tb_axi4ace_snoop_monitor_lite.
"""AXI4-ACE snoop-channel lite-monitor testbench.

Drives a shared m_axi_* snoop bus with AXI4ACESnoopMaster (issue) and
AXI4ACESnoopSlave (responder) both bound with prefix='m_axi_'.  A MonbusSlave
collects every packet and the TB checks completion/error/timeout packets
against the ACE issue order and the CRRESP/ACSNOOP encodings documented in
rtl/amba/monitor/axi4ace_snoop_monitor_lite.sv.
"""
import os
import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import PktType, AXIErrorCode, AXITimeoutCode
from CocoTBFramework.components.ace.ace_interfaces import (
    AXI4ACESnoopMaster,
    AXI4ACESnoopSlave,
)
from CocoTBFramework.components.ace.ace_transaction import (
    CRRESP,
    CacheState,
    SnoopType,
)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

PKT_ERROR = PktType.PktTypeError
PKT_TIMEOUT = PktType.PktTypeTimeout
PKT_COMPL = PktType.PktTypeCompletion
ERR_PROTOCOL = AXIErrorCode.AXI_ERR_PROTOCOL
ERR_RESP_ORPHAN = AXIErrorCode.AXI_ERR_RESP_ORPHAN
ERR_DATA_ORPHAN = AXIErrorCode.AXI_ERR_DATA_ORPHAN
TMO_RESP = AXITimeoutCode.AXI_TIMEOUT_RESP


def _make_snoop_handler(data_seed: int = 0xDEAD_BEEF):
    """Deterministic MESI snoop handler with non-zero data (matches BFM test)."""

    def handler(addr: int, snoop_type: SnoopType, state: CacheState):
        if state == CacheState.INVALID:
            return CRRESP(0), None

        if state == CacheState.SHARED:
            if snoop_type in (SnoopType.READ_SHARED, SnoopType.READ_ONCE):
                return CRRESP.from_bits(is_shared=True), None
            return CRRESP(0), None

        if state == CacheState.EXCLUSIVE:
            data = (addr ^ data_seed) & 0xFFFF_FFFF
            if snoop_type in (SnoopType.READ_SHARED, SnoopType.READ_ONCE):
                return CRRESP.from_bits(
                    data_transfer=True, is_shared=True, was_unique=True
                ), data
            if snoop_type == SnoopType.READ_UNIQUE:
                return CRRESP.from_bits(data_transfer=True, was_unique=True), data
            if snoop_type == SnoopType.CLEAN_SHARED:
                return CRRESP.from_bits(is_shared=True, was_unique=True), None
            return CRRESP(0), None

        if state == CacheState.MODIFIED:
            data = (addr ^ 0xBEEF_CAFE) & 0xFFFF_FFFF
            if snoop_type == SnoopType.READ_SHARED:
                return CRRESP.from_bits(
                    data_transfer=True, pass_dirty=True, is_shared=True
                ), data
            if snoop_type == SnoopType.READ_UNIQUE:
                return CRRESP.from_bits(data_transfer=True, pass_dirty=True), data
            if snoop_type in (SnoopType.CLEAN_SHARED, SnoopType.CLEAN_INVALID):
                return CRRESP.from_bits(
                    data_transfer=True, pass_dirty=True, is_shared=True
                ), data
            if snoop_type == SnoopType.MAKE_INVALID:
                return CRRESP(0), None
            if snoop_type == SnoopType.READ_ONCE:
                return CRRESP.from_bits(data_transfer=True, pass_dirty=True), data
            return CRRESP(0), None

        if state == CacheState.OWNED:
            data = (addr ^ 0xCAFE_BABE) & 0xFFFF_FFFF
            if snoop_type in (SnoopType.READ_SHARED, SnoopType.READ_ONCE):
                return CRRESP.from_bits(
                    data_transfer=True, pass_dirty=True, is_shared=True
                ), data
            if snoop_type == SnoopType.READ_UNIQUE:
                return CRRESP.from_bits(
                    data_transfer=True, pass_dirty=True, is_shared=True
                ), data
            if snoop_type in (SnoopType.CLEAN_SHARED, SnoopType.CLEAN_INVALID):
                return CRRESP.from_bits(
                    data_transfer=True, pass_dirty=True, is_shared=True
                ), data
            if snoop_type == SnoopType.MAKE_INVALID:
                return CRRESP(0), None
            return CRRESP(0), None

        return CRRESP(0), None

    return handler


class AXI4ACESnoopMonitorLiteTB(TBBase):
    """Testbench for the ACE snoop lite monitor."""

    ADDR_MAP = {
        'invalid':   0x0000_0000,
        'shared':    0x0000_1000,
        'exclusive': 0x0000_2000,
        'modified':  0x0000_3000,
        'owned':     0x0000_4000,
    }

    def __init__(self, dut):
        super().__init__(dut)
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.addr_width = int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.data_width = int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.clk_period = int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.max_snoops = int(os.environ.get('TEST_MAX_SNOOPS', '8'))
        self.errors = []
        self.master = None
        self.slave = None
        self.mon = None
        self._mon_time = 0
        self._mon_time_task = None
        self._total_completions = 0
        self._total_errors = 0

    def _fail(self, msg):
        self.log.error(msg)
        self.errors.append(msg)

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', self.clk_period, 'ns')
        d = self.dut
        d.clear.value = 0
        d.i_mon_time.value = 0
        d.cfg_monitor_enable.value = 1
        d.cfg_error_enable.value = 1
        d.cfg_compl_enable.value = 1
        d.cfg_timeout_enable.value = 0
        d.cfg_timeout_cycles.value = 0
        d.cfg_freq_sel.value = 0
        d.monbus_ready.value = 1
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 10)

        self.master = AXI4ACESnoopMaster(
            dut=d,
            clock=d.aclk,
            prefix='m_axi_',
            log=self.log,
            ifc_name='init',
            data_width=self.data_width,
            addr_width=self.addr_width,
        )
        self.slave = AXI4ACESnoopSlave(
            dut=d,
            clock=d.aclk,
            prefix='m_axi_',
            log=self.log,
            ifc_name='resp',
            data_width=self.data_width,
            addr_width=self.addr_width,
        )
        self.slave.set_line_behavior(self.ADDR_MAP['shared'], CacheState.SHARED)
        self.slave.set_line_behavior(self.ADDR_MAP['exclusive'], CacheState.EXCLUSIVE)
        self.slave.set_line_behavior(self.ADDR_MAP['modified'], CacheState.MODIFIED)
        self.slave.set_line_behavior(self.ADDR_MAP['owned'], CacheState.OWNED)
        self.slave.set_handler(_make_snoop_handler())

        self.mon = MonbusSlave(
            dut=d,
            title='MonBus',
            prefix='',
            clock=d.aclk,
            bus_name='monbus',
            pkt_prefix='',
            log=self.log,
        )
        self._set_monbus_ready_profile('fast')
        self._mon_time_task = cocotb.start_soon(self._mon_time_counter())
        await self.wait_clocks('aclk', 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def _mon_time_counter(self):
        """Free-running i_mon_time counter (cycles)."""
        try:
            while True:
                await RisingEdge(self.dut.aclk)
                self._mon_time += 1
                self.dut.i_mon_time.value = self._mon_time
        except Exception as e:
            self.log.debug(f"i_mon_time counter stopped: {e}")

    def _set_monbus_ready_profile(self, profile):
        # Keep the monbus always ready for deterministic packet accounting.
        # FUNC backpressure is applied on the CR/CD ready signals only.
        self.mon.set_ready_randomizer(
            FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))

    def _set_cr_cd_backpressure(self, enable: bool):
        if enable:
            profile = FlexRandomizer({'ready_delay': ([(0, 0), (2, 5)], [1, 2])})
            self.master.cr_channel.set_randomizer(profile)
            self.master.cd_channel.set_randomizer(profile)
        else:
            profile = FlexRandomizer({'ready_delay': ([(0, 0)], [1])})
            self.master.cr_channel.set_randomizer(profile)
            self.master.cd_channel.set_randomizer(profile)

    async def _issue_and_check(self, addr, snoop_type, handler, expect_error=False,
                               data_beats=0):
        """Issue one snoop and verify the monitor emits exactly one new packet."""
        before = len(self.mon.received_packets)
        state = self.slave.line_behaviors.get(addr, CacheState.INVALID)
        exp_crresp, _ = handler(addr, snoop_type, state)
        result = await self.master.issue_snoop(addr, snoop_type)

        # Wait for exactly one new monitor packet to arrive.
        for _ in range(200):
            if len(self.mon.received_packets) >= before + 1:
                break
            await self.wait_clocks('aclk', 1)
        got = self.mon.received_packets[before:]
        self.mon.received_packets = self.mon.received_packets[:before]

        if expect_error:
            if len(got) != 1 or not got[0].is_error_packet():
                self._fail(
                    f"addr=0x{addr:08X} {snoop_type.name}: expected one ERROR packet, "
                    f"got {[p.format_for_display() for p in got]}"
                )
                return
            p = got[0]
            if p.event_code != int(ERR_PROTOCOL):
                self._fail(
                    f"addr=0x{addr:08X} {snoop_type.name}: expected ERROR/AXI_ERR_PROTOCOL, "
                    f"got event_code=0x{p.event_code:02X}"
                )
            if p.channel_id != (int(snoop_type) & 0xF):
                self._fail(
                    f"addr=0x{addr:08X} {snoop_type.name}: ERROR channel_id 0x{p.channel_id:03X} "
                    f"!= ACSNOOP 0x{int(snoop_type) & 0xF:03X}"
                )
            if (p.data & ((1 << self.addr_width) - 1)) != (addr & ((1 << self.addr_width) - 1)):
                self._fail(
                    f"addr=0x{addr:08X} {snoop_type.name}: ERROR data address mismatch"
                )
            return

        if len(got) != 1 or not got[0].is_completion_packet():
            self._fail(
                f"addr=0x{addr:08X} {snoop_type.name}: expected one COMPLETION packet, "
                f"got {[p.format_for_display() for p in got]}"
            )
            return
        p = got[0]
        exp_code = ((int(exp_crresp) & 0xF) << 4) | (int(snoop_type) & 0xF)
        if p.event_code != exp_code:
            self._fail(
                f"addr=0x{addr:08X} {snoop_type.name}: event_code 0x{p.event_code:02X} "
                f"!= expected 0x{exp_code:02X} (CRRESP[3:0]=0x{int(exp_crresp) & 0xF:X}, "
                f"ACSNOOP=0x{int(snoop_type) & 0xF:X})"
            )
        if p.channel_id != data_beats:
            self._fail(
                f"addr=0x{addr:08X} {snoop_type.name}: channel_id {p.channel_id} "
                f"!= expected beat count {data_beats}"
            )

    async def phase_gate_smoke(self):
        """GATE: small deterministic MESI subset."""
        self.log.info("PHASE gate: small MESI subset")
        handler = _make_snoop_handler()
        cases = [
            (self.ADDR_MAP['invalid'],   SnoopType.READ_SHARED,  0),
            (self.ADDR_MAP['shared'],    SnoopType.READ_SHARED,  0),
            (self.ADDR_MAP['exclusive'], SnoopType.READ_SHARED,  1),
            (self.ADDR_MAP['modified'],  SnoopType.READ_UNIQUE,  1),
        ]
        for addr, stype, beats in cases:
            await self._issue_and_check(addr, stype, handler, data_beats=beats)
        self._total_completions = len(cases)
        self._check_transaction_count(self._total_completions)
        self.log.info(f"PHASE gate: {len(cases)} snoops, all completions exact")

    async def phase_func_matrix(self):
        """FUNC: full MESI x snoop-type matrix + one forced-error snoop."""
        self.log.info("PHASE func: MESI x snoop-type matrix + error injection")
        handler = _make_snoop_handler()
        states = [
            (self.ADDR_MAP['invalid'],   CacheState.INVALID),
            (self.ADDR_MAP['shared'],    CacheState.SHARED),
            (self.ADDR_MAP['exclusive'], CacheState.EXCLUSIVE),
            (self.ADDR_MAP['modified'],  CacheState.MODIFIED),
            (self.ADDR_MAP['owned'],     CacheState.OWNED),
        ]
        snoops = [
            SnoopType.READ_ONCE,
            SnoopType.READ_SHARED,
            SnoopType.READ_UNIQUE,
            SnoopType.CLEAN_SHARED,
            SnoopType.CLEAN_INVALID,
            SnoopType.MAKE_INVALID,
        ]
        for addr, state in states:
            for stype in snoops:
                exp_crresp, _ = handler(addr, stype, state)
                beats = 1 if exp_crresp.data_transfer else 0
                await self._issue_and_check(addr, stype, handler, data_beats=beats)
                self._total_completions += 1

        # Backpressure on CR/CD.
        self._set_cr_cd_backpressure(True)
        for addr, state in states[:3]:
            for stype in snoops[:3]:
                exp_crresp, _ = handler(addr, stype, state)
                beats = 1 if exp_crresp.data_transfer else 0
                await self._issue_and_check(addr, stype, handler, data_beats=beats)
                self._total_completions += 1
        self._set_cr_cd_backpressure(False)

        # Forced-error snoop: handler returns Error bit set.
        error_addr = self.ADDR_MAP['modified']
        self.slave.set_handler(
            lambda addr, stype, state: (
                CRRESP.from_bits(error=True),
                None,
            )
        )
        await self._issue_and_check(error_addr, SnoopType.READ_SHARED, handler,
                                    expect_error=True)
        self._total_errors += 1
        self.slave.set_handler(_make_snoop_handler())

        self._check_transaction_count(self._total_completions)
        self._check_error_count(self._total_errors)
        self.log.info(
            f"PHASE func: {self._total_completions} completions + "
            f"{self._total_errors} error(s), all exact"
        )

    async def phase_full_timeout(self):
        """FULL: timeout cone via delayed CR (orphan error is a natural by-product)."""
        self.log.info("PHASE full: timeout with delayed CR")
        d = self.dut
        # Enable timeout at 1 us; at 100 MHz that is 100 cycles.
        d.cfg_timeout_enable.value = 1
        d.cfg_timeout_cycles.value = 1
        # Hold CR ready low for >100 cycles so the slave's response cannot handshake.
        self.master.cr_channel.set_randomizer(
            FlexRandomizer({'ready_delay': ([(150, 150)], [1])}))

        addr = self.ADDR_MAP['exclusive']
        stype = SnoopType.READ_UNIQUE
        await self.master.ac_channel.send(
            self.master.ac_channel.create_packet(addr=addr, snoop=int(stype), prot=0)
        )
        # Wait long enough for the timeout to fire and for the delayed CR ready to release.
        await self.wait_clocks('aclk', 250)
        self.master.cr_channel.set_randomizer(
            FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        # Drain whatever else arrives (the delayed CR becomes an orphan error).
        await self.wait_clocks('aclk', 50)

        got = list(self.mon.received_packets)
        self.mon.clear_received_packets()
        timeouts = [p for p in got if p.is_timeout_packet()]
        orphans = [p for p in got
                   if p.is_error_packet() and p.event_code == int(ERR_RESP_ORPHAN)]
        if len(timeouts) != 1:
            self._fail(
                f"full: expected one TIMEOUT packet, got {len(timeouts)}: "
                f"{[p.format_for_display() for p in got]}"
            )
        else:
            p = timeouts[0]
            if p.event_code != int(TMO_RESP):
                self._fail(
                    f"full: TIMEOUT event_code 0x{p.event_code:02X} != AXI_TIMEOUT_RESP"
                )
        if len(orphans) != 1:
            self._fail(
                f"full: expected one RESP_ORPHAN after timeout, got {len(orphans)}: "
                f"{[p.format_for_display() for p in got]}"
            )

        d.cfg_timeout_enable.value = 0
        d.cfg_timeout_cycles.value = 0
        self.log.info("PHASE full: timeout + orphan error observed")

    def _check_transaction_count(self, expected):
        actual = int(self.dut.transaction_count.value)
        if actual != expected:
            self._fail(f"transaction_count {actual} != expected {expected}")

    def _check_error_count(self, expected):
        actual = int(self.dut.error_count.value)
        if actual != expected:
            self._fail(f"error_count {actual} != expected {expected}")

    async def _pulse_clear(self):
        """Pulse the monitor clear input to reset internal table/counters."""
        self.dut.clear.value = 1
        await self.wait_clocks('aclk', 1)
        self.dut.clear.value = 0
        await self.wait_clocks('aclk', 5)

    async def run_suite(self):
        await self.phase_gate_smoke()
        if self.level in ('func', 'full'):
            await self.phase_func_matrix()
        if self.level == 'full':
            # The forced-error snoop leaves its table entry in place (the RTL
            # does not free the head on an error response).  Pulse clear so the
            # timeout phase starts with an empty outstanding-snoop table.
            await self._pulse_clear()
            self._total_completions = 0
            self._total_errors = 0
            await self.phase_full_timeout()
        if self.errors:
            self.log.error(f"{len(self.errors)} violation(s):")
            for e in self.errors:
                self.log.error(f"  {e}")
        return not self.errors
