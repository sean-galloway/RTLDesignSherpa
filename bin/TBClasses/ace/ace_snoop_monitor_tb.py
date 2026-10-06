# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ace_snoop_monitor_tb
# Purpose: ACE snoop-channel monitor-lite integration testbench.
#
# Subsystem: framework

"""ACE snoop-channel monitor-lite integration testbench.

``AXI4ACESnoopMonitorTB`` wraps ``AXI4ACESnoopTransportTB`` and adds a
``MonbusSlave`` on the wrapper's monbus.  For every issued snoop it asserts
that exactly one monitor packet is produced:

* Normal completion -> ``PktTypeCompletion``, event_code = ``{CRRESP[3:0], ACSNOOP[3:0]}``,
  channel_id = number of CDLAST beats, data low bits = AC address.
* Error injection (CRRESP[1] forced) -> ``PktTypeError`` / ``AXI_ERR_PROTOCOL``,
  completion suppressed, ``error_count`` increments.

The class works for both ``axi4ace_snoop_slave_monlite`` (master_prefix="m_axi_",
slave_prefix="fub_") and ``axi4ace_snoop_master_monlite`` (master_prefix="fub_",
slave_prefix="m_axi_").
"""

import random
from typing import List, Optional, Tuple

from CocoTBFramework.components.ace.ace_transaction import (
    CRRESP,
    CacheState,
    SnoopType,
    CRRESP_ERROR,
)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

from TBClasses.ace.ace_snoop_transport_tb import AXI4ACESnoopTransportTB
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import ProtocolType, AXIErrorCode


class AXI4ACESnoopMonitorTB:
    """Testbench for ACE snoop-channel *_monlite wrappers with packet checks."""

    # Deterministic MESI subset used at GATE level (matches BFM acceptance test).
    GATE_MESI_CASES: List[Tuple[CacheState, SnoopType]] = [
        (CacheState.INVALID,   SnoopType.READ_SHARED),
        (CacheState.INVALID,   SnoopType.READ_UNIQUE),
        (CacheState.SHARED,    SnoopType.READ_SHARED),
        (CacheState.SHARED,    SnoopType.READ_UNIQUE),
        (CacheState.EXCLUSIVE, SnoopType.READ_SHARED),
        (CacheState.EXCLUSIVE, SnoopType.READ_UNIQUE),
        (CacheState.MODIFIED,  SnoopType.READ_SHARED),
        (CacheState.MODIFIED,  SnoopType.READ_UNIQUE),
        (CacheState.MODIFIED,  SnoopType.CLEAN_INVALID),
        (CacheState.MODIFIED,  SnoopType.MAKE_INVALID),
    ]

    def __init__(
        self,
        dut,
        aclk=None,
        aresetn=None,
        master_prefix: str = "m_axi_",
        slave_prefix: str = "fub_",
        addr_width: Optional[int] = None,
        data_width: Optional[int] = None,
        unit_id: int = 1,
        agent_id: int = 10,
    ):
        self.dut = dut
        self.unit_id = unit_id
        self.agent_id = agent_id

        # Build the base transport TB (BFM master + deterministic MESI responder).
        self.base_tb = AXI4ACESnoopTransportTB(
            dut=dut,
            aclk=aclk,
            aresetn=aresetn,
            master_prefix=master_prefix,
            slave_prefix=slave_prefix,
            addr_width=addr_width,
            data_width=data_width,
        )

        # Expose common attributes from the base TB.
        self.log = self.base_tb.log
        self.aclk = self.base_tb.aclk
        self.aresetn = self.base_tb.aresetn

        self.mon_slave: Optional[MonbusSlave] = None

    async def initialize(self):
        """Start clock, apply reset, configure monitor, and bind MonbusSlave."""
        await self.base_tb.start_clock("aclk", self.base_tb.TEST_CLK_PERIOD, "ns")

        d = self.dut
        # Lite-wrapper cfg: every write is hasattr-guarded so this TB can drive
        # both the lite wrappers and any future full-monitor wrapper.
        if hasattr(d, "cfg_monitor_enable"):
            d.cfg_monitor_enable.value = 1
        if hasattr(d, "cfg_error_enable"):
            d.cfg_error_enable.value = 1
        if hasattr(d, "cfg_timeout_enable"):
            d.cfg_timeout_enable.value = 1
        if hasattr(d, "cfg_compl_enable"):
            d.cfg_compl_enable.value = 1
        if hasattr(d, "cfg_timeout_cycles"):
            # 0 = never timeout (the wrapper remaps 0 -> 0xFFFF internally).
            d.cfg_timeout_cycles.value = 0
        if hasattr(d, "cfg_freq_sel"):
            d.cfg_freq_sel.value = 0
        if hasattr(d, "clear"):
            d.clear.value = 0
        if hasattr(d, "i_mon_time"):
            # Same static timestamp pattern as axis_monitor_lite fixture.
            d.i_mon_time.value = 0

        await self.base_tb.assert_reset()
        await self.base_tb.wait_clocks("aclk", 10)
        await self.base_tb.deassert_reset()
        await self.base_tb.wait_clocks("aclk", 10)

        # Monitor bus slave: always-ready so packets drain immediately.
        self.mon_slave = MonbusSlave(
            dut=d,
            title="MonBus",
            prefix="",
            clock=self.aclk,
            bus_name="monbus",
            pkt_prefix="",
            signal_map={
                "valid": "monbus_valid",
                "ready": "monbus_ready",
                "data": "monbus_packet",
            },
            expected_unit_id=self.unit_id,
            expected_agent_id=self.agent_id,
            expected_protocol=ProtocolType.PROTOCOL_AXI.value,
            log=self.log,
        )
        self.mon_slave.set_ready_randomizer(
            FlexRandomizer({"ready_delay": ([(0, 0)], [1])})
        )

        await self.base_tb.wait_clocks("aclk", 5)
        self.log.info("AXI4ACESnoopMonitorTB initialized")

    # -------------------------------------------------------------------------
    # Public scenario suite
    # -------------------------------------------------------------------------

    async def run_monitor_tests(self, test_level: str = "gate"):
        """Run the monitor-aware scenario suite for the requested test level."""
        test_level = test_level.lower()
        valid = ("gate", "func", "full")
        if test_level not in valid:
            self.log.warning(
                f"Invalid TEST_LEVEL '{test_level}', using 'gate'. Valid: {valid}"
            )
            test_level = "gate"

        self.log.info("=" * 70)
        self.log.info(
            f"ACE Snoop Monitor Integration Tests: level={test_level.upper()}"
        )
        self.log.info("=" * 70)

        if test_level == "gate":
            await self.scenario_mesi_subset()
            await self.scenario_back_to_back(count=5)
        elif test_level == "func":
            await self.scenario_mesi_matrix(iterations=1)
            await self.scenario_back_to_back(count=12)
            await self.scenario_backpressure(deep=False)
            await self.scenario_error()
        else:  # full
            await self.scenario_mesi_matrix(iterations=2)
            await self.scenario_back_to_back(count=25)
            await self.scenario_backpressure(deep=True)
            await self.scenario_stress(count=50)
            await self.scenario_error()

        await self.base_tb._wait_quiescent()
        await self._assert_no_stray_packets()
        self.log.info("=" * 70)
        self.log.info("ALL ACE SNOOP MONITOR TESTS PASSED")
        self.log.info("=" * 70)

    async def scenario_mesi_subset(self):
        """GATE-level deterministic MESI subset."""
        self.log.info("Scenario: GATE MESI subset")
        self.base_tb.set_timing_profile("normal")
        for state, snoop_type in self.GATE_MESI_CASES:
            addr = self.base_tb._addr_for_state(state)
            await self.issue_snoop_and_assert_packet(addr, snoop_type)
        self.log.info("GATE MESI subset completed")

    async def scenario_mesi_matrix(self, iterations: int = 1):
        """Full CacheState x SnoopType matrix."""
        self.log.info(
            f"Scenario: full MESI x snoop-type matrix ({iterations} iteration(s))"
        )
        self.base_tb.set_timing_profile("normal")
        count = 0
        for _ in range(iterations):
            for state in CacheState:
                for snoop_type in SnoopType:
                    addr = self.base_tb._addr_for_state(state)
                    await self.issue_snoop_and_assert_packet(addr, snoop_type)
                    count += 1
        self.log.info(f"MESI matrix completed: {count} snoops")

    async def scenario_back_to_back(self, count: int = 10):
        """In-order back-to-back snoops mixing states and snoop types."""
        self.log.info(f"Scenario: back-to-back in-order snoops ({count})")
        self.base_tb.set_timing_profile("backtoback")
        states = list(CacheState)
        snoops = list(SnoopType)
        for i in range(count):
            state = states[i % len(states)]
            snoop_type = snoops[(i * 3) % len(snoops)]
            addr = self.base_tb._addr_for_state(state)
            await self.issue_snoop_and_assert_packet(addr, snoop_type)
        self.log.info(f"Back-to-back sequence completed: {count} snoops")

    async def scenario_backpressure(self, deep: bool = False):
        """Snoops under CR/CD ready backpressure."""
        self.log.info("Scenario: CR/CD backpressure")
        if deep:
            backpressure = FlexRandomizer({
                "ready_delay": ([(0, 0), (3, 8), (9, 16)], [0.3, 0.4, 0.3])
            })
        else:
            backpressure = FlexRandomizer({
                "ready_delay": ([(0, 0), (2, 5)], [1, 2])
            })
        self.base_tb.master.cr_channel.set_randomizer(backpressure)
        self.base_tb.master.cd_channel.set_randomizer(backpressure)

        bp_cases = [
            (self.base_tb.ADDR_MODIFIED,  SnoopType.READ_SHARED),
            (self.base_tb.ADDR_EXCLUSIVE, SnoopType.READ_SHARED),
            (self.base_tb.ADDR_SHARED,    SnoopType.READ_SHARED),
            (self.base_tb.ADDR_MODIFIED,  SnoopType.READ_UNIQUE),
            (self.base_tb.ADDR_OWNED,     SnoopType.CLEAN_INVALID),
            (self.base_tb.ADDR_INVALID,   SnoopType.MAKE_INVALID),
        ]
        for addr, snoop_type in bp_cases:
            await self.issue_snoop_and_assert_packet(addr, snoop_type)

        self.base_tb.set_timing_profile("normal")
        self.log.info("Backpressure scenario completed")

    async def scenario_stress(self, count: int = 50):
        """Randomized stress mix of states, snoop types, and timing."""
        self.log.info(f"Scenario: stress mix ({count} snoops)")
        self.base_tb.set_timing_profile("stress")
        states = list(CacheState)
        snoops = list(SnoopType)
        for _ in range(count):
            state = random.choice(states)
            snoop_type = random.choice(snoops)
            addr = self.base_tb._addr_for_state(state)
            await self.issue_snoop_and_assert_packet(addr, snoop_type)
        self.base_tb.set_timing_profile("normal")
        self.log.info(f"Stress mix completed: {count} snoops")

    async def scenario_error(self):
        """Force CRRESP[1] and assert an ERROR packet + error_count increment."""
        self.log.info("Scenario: error injection")
        addr = self.base_tb.ADDR_MODIFIED
        snoop_type = SnoopType.READ_SHARED

        # Save and override the responder handler to set the Error bit.
        original_handler = self.base_tb.slave.user_handler
        error_handler = self._make_error_handler()
        self.base_tb.slave.set_handler(error_handler)

        packets_before = len(self.mon_slave.received_packets)
        txn_before = int(self.dut.transaction_count.value)
        err_before = int(self.dut.error_count.value)

        result = await self.base_tb.master.issue_snoop(addr, snoop_type)
        if not result.crresp.error:
            self.base_tb.slave.set_handler(original_handler)
            raise AssertionError(
                f"addr=0x{addr:08X} {snoop_type.name}: expected CRRESP Error bit set"
            )

        # Wait for the protocol-error packet and a short drain window.
        await self._wait_for_error_code(
            packets_before, AXIErrorCode.AXI_ERR_PROTOCOL.value
        )
        await self.base_tb.wait_clocks("aclk", 20)

        new_packets = self.mon_slave.received_packets[packets_before:]
        protocol_errors = [
            p for p in new_packets
            if p.is_error_packet() and p.event_code == AXIErrorCode.AXI_ERR_PROTOCOL.value
        ]
        completions = [p for p in new_packets if p.is_completion_packet()]

        if len(protocol_errors) != 1:
            types = [(p.pkt_type, p.event_code) for p in new_packets]
            self.base_tb.slave.set_handler(original_handler)
            raise AssertionError(
                f"addr=0x{addr:08X} {snoop_type.name}: expected exactly 1 "
                f"AXI_ERR_PROTOCOL packet, got {len(protocol_errors)} among "
                f"{len(new_packets)} new packet(s): {types[:10]}"
            )
        if completions:
            self.base_tb.slave.set_handler(original_handler)
            raise AssertionError(
                "completion packet emitted for an error snoop; completion was not suppressed"
            )

        self._assert_error_packet(protocol_errors[0], addr, snoop_type)

        # Completion must be suppressed; error_count advances instead.
        if int(self.dut.transaction_count.value) != txn_before:
            self.base_tb.slave.set_handler(original_handler)
            raise AssertionError(
                "transaction_count advanced for an error snoop; completion was not suppressed"
            )
        if int(self.dut.error_count.value) != err_before + 1:
            self.base_tb.slave.set_handler(original_handler)
            raise AssertionError(
                f"error_count {int(self.dut.error_count.value)} != expected {err_before + 1}"
            )

        self.base_tb.slave.set_handler(original_handler)
        self.log.info("Error injection scenario completed")

    # -------------------------------------------------------------------------
    # Per-snoop helpers
    # -------------------------------------------------------------------------

    async def issue_snoop_and_assert_packet(
        self, addr: int, snoop_type: SnoopType
    ):
        """Issue one snoop, run base checks, and assert one monitor completion."""
        packets_before = len(self.mon_slave.received_packets)
        txn_before = int(self.dut.transaction_count.value)

        ok = await self.base_tb.issue_and_check(addr, snoop_type)
        if not ok:
            raise AssertionError(
                f"base transport check failed for addr=0x{addr:08X} {snoop_type.name}"
            )

        # Wait for the completion packet and a short drain window so any
        # AXI_ERR_DATA_ORPHAN that lags the completion (CDLAST after CR) is
        # also captured without being mistaken for the completion.
        await self._wait_for_completion(packets_before)
        await self.base_tb.wait_clocks("aclk", 20)

        new_packets = self.mon_slave.received_packets[packets_before:]
        completions = [p for p in new_packets if p.is_completion_packet()]
        if len(completions) != 1:
            types = [(p.pkt_type, p.event_code) for p in new_packets]
            raise AssertionError(
                f"addr=0x{addr:08X} {snoop_type.name}: expected exactly 1 "
                f"completion packet, got {len(completions)} completion(s) among "
                f"{len(new_packets)} new packet(s): {types[:10]}"
            )

        exp_crresp, exp_data = self.base_tb.expected(addr, snoop_type)
        self._assert_completion_packet(completions[0], addr, snoop_type, exp_crresp, exp_data)

        if int(self.dut.transaction_count.value) != txn_before + 1:
            raise AssertionError(
                f"transaction_count {int(self.dut.transaction_count.value)} != "
                f"expected {txn_before + 1}"
            )

    def _assert_completion_packet(
        self, pkt, addr: int, snoop_type: SnoopType, exp_crresp: CRRESP, exp_data
    ):
        """Validate a completion packet against the RTL encoding."""
        if not pkt.is_completion_packet():
            raise AssertionError(f"expected completion packet, got {pkt}")
        if pkt.protocol != ProtocolType.PROTOCOL_AXI.value:
            raise AssertionError(
                f"expected AXI protocol, got protocol={pkt.protocol}"
            )

        exp_event_code = ((int(exp_crresp) & 0xF) << 4) | (int(snoop_type) & 0xF)
        if pkt.event_code != exp_event_code:
            raise AssertionError(
                f"addr=0x{addr:08X} {snoop_type.name}: event_code mismatch "
                f"got 0x{pkt.event_code:02X}, expected 0x{exp_event_code:02X}"
            )

        # channel_id is the CDLAST beat count seen up to the CR handshake.
        # In ACE the CR handshake can occur before the CD data beat, so a
        # data-transfer snoop may legitimately report 0 beats at completion time.
        exp_beats = 1 if exp_data is not None else 0
        if not (0 <= pkt.channel_id <= exp_beats):
            raise AssertionError(
                f"addr=0x{addr:08X} {snoop_type.name}: channel_id out of range "
                f"got {pkt.channel_id}, expected 0..{exp_beats}"
            )

        exp_addr = addr & self.base_tb.addr_mask
        if (pkt.data & self.base_tb.addr_mask) != exp_addr:
            raise AssertionError(
                f"addr=0x{addr:08X} {snoop_type.name}: packet address mismatch "
                f"data=0x{pkt.data:016X}, expected addr low bits=0x{exp_addr:08X}"
            )

        if pkt.unit_id != self.unit_id:
            raise AssertionError(
                f"unit_id mismatch: got 0x{pkt.unit_id:02X}, expected 0x{self.unit_id:02X}"
            )
        if pkt.agent_id != self.agent_id:
            raise AssertionError(
                f"agent_id mismatch: got 0x{pkt.agent_id:04X}, expected 0x{self.agent_id:04X}"
            )

    def _assert_error_packet(self, pkt, addr: int, snoop_type: SnoopType):
        """Validate an ERROR/AXI_ERR_PROTOCOL packet."""
        if not pkt.is_error_packet():
            raise AssertionError(f"expected error packet, got {pkt}")
        if pkt.protocol != ProtocolType.PROTOCOL_AXI.value:
            raise AssertionError(
                f"expected AXI protocol, got protocol={pkt.protocol}"
            )
        if pkt.event_code != AXIErrorCode.AXI_ERR_PROTOCOL.value:
            raise AssertionError(
                f"expected AXI_ERR_PROTOCOL (0x{AXIErrorCode.AXI_ERR_PROTOCOL.value:02X}), "
                f"got 0x{pkt.event_code:02X}"
            )
        if pkt.channel_id != (int(snoop_type) & 0xF):
            raise AssertionError(
                f"error packet channel_id mismatch: got {pkt.channel_id}, "
                f"expected 0x{int(snoop_type) & 0xF:X}"
            )
        exp_addr = addr & self.base_tb.addr_mask
        if (pkt.data & self.base_tb.addr_mask) != exp_addr:
            raise AssertionError(
                f"error packet address mismatch: data=0x{pkt.data:016X}, "
                f"expected addr low bits=0x{exp_addr:08X}"
            )

    async def _wait_for_new_packets(
        self, before_count: int, count: int = 1, timeout_cycles: int = 200
    ):
        """Wait until ``count`` new packets have been collected."""
        for _ in range(timeout_cycles):
            if len(self.mon_slave.received_packets) >= before_count + count:
                return
            await self.base_tb.wait_clocks("aclk", 1)
        raise TimeoutError(
            f"Timed out waiting for {count} new packet(s); "
            f"had {before_count}, now {len(self.mon_slave.received_packets)}"
        )

    async def _wait_for_completion(
        self, before_count: int, timeout_cycles: int = 200
    ):
        """Wait until at least one completion packet has been collected."""
        for _ in range(timeout_cycles):
            new_packets = self.mon_slave.received_packets[before_count:]
            if any(p.is_completion_packet() for p in new_packets):
                return
            await self.base_tb.wait_clocks("aclk", 1)
        raise TimeoutError(
            f"Timed out waiting for completion packet; "
            f"had {before_count}, now {len(self.mon_slave.received_packets)}"
        )

    async def _wait_for_error_code(
        self, before_count: int, event_code: int, timeout_cycles: int = 200
    ):
        """Wait until at least one error packet with the given code arrives."""
        for _ in range(timeout_cycles):
            new_packets = self.mon_slave.received_packets[before_count:]
            if any(
                p.is_error_packet() and p.event_code == event_code
                for p in new_packets
            ):
                return
            await self.base_tb.wait_clocks("aclk", 1)
        raise TimeoutError(
            f"Timed out waiting for error packet code 0x{event_code:02X}; "
            f"had {before_count}, now {len(self.mon_slave.received_packets)}"
        )

    async def _assert_no_stray_packets(self, settle_cycles: int = 50):
        """After quiescence, ensure no additional packets appear."""
        count = len(self.mon_slave.received_packets)
        for _ in range(settle_cycles):
            await self.base_tb.wait_clocks("aclk", 1)
            if len(self.mon_slave.received_packets) != count:
                new = self.mon_slave.received_packets[count:]
                raise AssertionError(
                    f"Stray packet(s) after quiescence: {[str(p) for p in new[:4]]}"
                )

    def _make_error_handler(self):
        """Return a responder handler that sets CRRESP[1] on top of the base model."""
        base_handler = self.base_tb.handler

        def handler(addr: int, snoop_type: SnoopType, state: CacheState):
            crresp, data = base_handler(addr, snoop_type, state)
            return CRRESP(crresp.value | CRRESP_ERROR), data

        return handler
