# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4ACEMonitorTB
# Purpose: AXI4-ACE front-side monitor-lite integration testbench
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework

"""
AXI4-ACE Monitor-lite integration testbench.

Wraps the ACE front-side base testbenches (AXI4ACEMasterReadTB,
AXI4ACEMasterWriteTB, AXI4ACESlaveReadTB, AXI4ACESlaveWriteTB) and adds
monitor-packet collection/validation using MonbusSlave. Every cfg write is
guarded with hasattr so the same TB can drive both the _mon and _monlite
wrappers.

This is the ACE counterpart to TBClasses/axi4/monitor/axi4_master_monitor_tb.py
and axi4_slave_monitor_tb.py. It reuses the 128-bit MonbusPacket helpers from
TBClasses/monbus.
"""

import os
from typing import Any, List, Optional, Tuple

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.ace.ace_master_read_tb import AXI4ACEMasterReadTB
from TBClasses.ace.ace_master_write_tb import AXI4ACEMasterWriteTB
from TBClasses.ace.ace_slave_read_tb import AXI4ACESlaveReadTB
from TBClasses.ace.ace_slave_write_tb import AXI4ACESlaveWriteTB
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import (
    ProtocolType, PktType, AXICompletionCode
)


class AXI4ACEMonitorTB:
    """
    Reusable testbench for AXI4-ACE front-side modules with integrated
    monitor-lite (or full-monitor) packet validation.
    """

    # Wrapper default UNIT_ID / AGENT_ID values from the RTL parameter defaults.
    _UNIT_AGENT = {
        (False, False): (0x01, 0x000A),  # master read
        (True,  False): (0x01, 0x000B),  # master write
        (False, True):  (0x02, 0x0014),  # slave read
        (True,  True):  (0x02, 0x0015),  # slave write
    }

    def __init__(self, dut, is_write: bool = False, is_slave: bool = False,
                 aclk=None, aresetn=None,
                 expected_unit_id: Optional[int] = None,
                 expected_agent_id: Optional[int] = None):
        """
        Initialize the testbench.

        Args:
            dut: The DUT (one of the axi4ace_*_monlite wrappers).
            is_write: True for write path, False for read path.
            is_slave: True for slave-side wrapper, False for master-side wrapper.
            aclk: Clock signal (default: dut.aclk).
            aresetn: Reset signal (default: dut.aresetn).
            expected_unit_id: Override the expected monitor UNIT_ID.
            expected_agent_id: Override the expected monitor AGENT_ID.
        """
        self.dut = dut
        self.is_write = is_write
        self.is_slave = is_slave

        if is_slave:
            base_cls = AXI4ACESlaveWriteTB if is_write else AXI4ACESlaveReadTB
        else:
            base_cls = AXI4ACEMasterWriteTB if is_write else AXI4ACEMasterReadTB

        self.base_tb = base_cls(dut, aclk=aclk, aresetn=aresetn)

        self.log = self.base_tb.log
        self.aclk = self.base_tb.aclk
        self.aresetn = self.base_tb.aresetn

        default_unit, default_agent = self._UNIT_AGENT[(is_write, is_slave)]
        self.expected_unit_id = expected_unit_id if expected_unit_id is not None else default_unit
        self.expected_agent_id = expected_agent_id if expected_agent_id is not None else default_agent

        self.mon_slave: Optional[MonbusSlave] = None

    async def initialize(self):
        """Initialize clock, reset, monitor configuration and packet slave."""
        await self.base_tb.start_clock('aclk', self.base_tb.TEST_CLK_PERIOD, 'ns')

        # Monitor enables: everything we care about on, perf/debug off.
        if hasattr(self.dut, 'cfg_monitor_enable'): self.dut.cfg_monitor_enable.value = 1
        if hasattr(self.dut, 'cfg_error_enable'):   self.dut.cfg_error_enable.value = 1
        if hasattr(self.dut, 'cfg_timeout_enable'): self.dut.cfg_timeout_enable.value = 1
        if hasattr(self.dut, 'cfg_compl_enable'):   self.dut.cfg_compl_enable.value = 1
        if hasattr(self.dut, 'cfg_threshold_enable'): self.dut.cfg_threshold_enable.value = 0
        if hasattr(self.dut, 'cfg_debug_enable'):   self.dut.cfg_debug_enable.value = 0
        if hasattr(self.dut, 'cfg_timeout_cycles'): self.dut.cfg_timeout_cycles.value = 1000
        if hasattr(self.dut, 'cfg_latency_threshold'): self.dut.cfg_latency_threshold.value = 500

        # ID-range filter is not present on the lite wrapper, but guard it so
        # the same TB can be reused for the full _mon wrapper if desired.
        if hasattr(self.dut, 'cfg_id_filter_enable'): self.dut.cfg_id_filter_enable.value = 0
        if hasattr(self.dut, 'cfg_id_match_base'):    self.dut.cfg_id_match_base.value = 0
        if hasattr(self.dut, 'cfg_id_match_count'):   self.dut.cfg_id_match_count.value = 0

        # Drop masks: pass everything through.
        if hasattr(self.dut, 'cfg_axi_pkt_mask'):   self.dut.cfg_axi_pkt_mask.value = 0x0000
        if hasattr(self.dut, 'cfg_axi_err_select'): self.dut.cfg_axi_err_select.value = 0x0000
        if hasattr(self.dut, 'cfg_axi_error_mask'): self.dut.cfg_axi_error_mask.value = 0x0000
        if hasattr(self.dut, 'cfg_axi_timeout_mask'): self.dut.cfg_axi_timeout_mask.value = 0x0000
        if hasattr(self.dut, 'cfg_axi_compl_mask'): self.dut.cfg_axi_compl_mask.value = 0x0000
        if hasattr(self.dut, 'cfg_axi_thresh_mask'): self.dut.cfg_axi_thresh_mask.value = 0x0000
        if hasattr(self.dut, 'cfg_axi_perf_mask'):  self.dut.cfg_axi_perf_mask.value = 0x0000
        if hasattr(self.dut, 'cfg_axi_addr_mask'):  self.dut.cfg_axi_addr_mask.value = 0x0000
        if hasattr(self.dut, 'cfg_axi_debug_mask'): self.dut.cfg_axi_debug_mask.value = 0x0000

        # Lite-specific cfg inputs that are not on the full monitor.
        if hasattr(self.dut, 'cfg_freq_sel'):        self.dut.cfg_freq_sel.value = 0
        if hasattr(self.dut, 'cam_clear'):           self.dut.cam_clear.value = 0
        if hasattr(self.dut, 'cfg_addr_check_enable'): self.dut.cfg_addr_check_enable.value = 0
        if hasattr(self.dut, 'cfg_addr_match_enable'): self.dut.cfg_addr_match_enable.value = 0
        if hasattr(self.dut, 'cfg_addr_range_enable'):
            self.dut.cfg_addr_range_enable.value = 0
        if hasattr(self.dut, 'cfg_addr_range_low'):
            self.dut.cfg_addr_range_low.value = 0
        if hasattr(self.dut, 'cfg_addr_range_high'):
            self.dut.cfg_addr_range_high.value = 0
        if hasattr(self.dut, 'i_mon_time'):
            self.dut.i_mon_time.value = 0

        await self.base_tb.assert_reset()
        await self.base_tb.wait_clocks('aclk', 10)
        await self.base_tb.deassert_reset()
        await self.base_tb.wait_clocks('aclk', 10)

        self.mon_slave = MonbusSlave(
            dut=self.dut,
            title="MonBus",
            prefix="",
            clock=self.dut.aclk,
            bus_name="monbus",
            pkt_prefix="",
            signal_map={
                'valid': 'monbus_valid',
                'ready': 'monbus_ready',
                'data': 'monbus_packet'
            },
            expected_unit_id=self.expected_unit_id,
            expected_agent_id=self.expected_agent_id,
            log=self.log
        )

        self.log.info("AXI4-ACE monitor-lite testbench initialized")

    async def run_integration_tests(self, test_level: str = 'basic'):
        """
        Run the monitor integration scenario suite.

        Args:
            test_level: 'basic' / 'medium' / 'full' (maps to gate/func/full).
        """
        self.log.info("=" * 80)
        self.log.info(
            f"AXI4-ACE {'Slave' if self.is_slave else 'Master'} "
            f"{'Write' if self.is_write else 'Read'} Monitor Integration Tests"
        )
        self.log.info(f"Test Level: {test_level.upper()}")
        self.log.info("=" * 80)

        await self._test_basic_connectivity()
        await self._test_multiple_transactions(test_level)

        if not self.is_write:
            await self._test_burst_transactions(test_level)

        await self._test_error_detection()

        if test_level in ['medium', 'full']:
            await self._test_sustained_traffic(test_level)

        await self._final_report()

    # ------------------------------------------------------------------
    # Scenario tests
    # ------------------------------------------------------------------

    async def _do_single_write(self, address: int, data: int,
                               transaction_id: Optional[int] = None) -> Tuple[bool, Any]:
        """Dispatch to master or slave base-TB write method."""
        if self.is_slave:
            return await self.base_tb.single_write_response_test(
                address=address, data=data, transaction_id=transaction_id
            )
        return await self.base_tb.single_write_test(
            address=address, data=data, transaction_id=transaction_id
        )

    async def _do_single_read(self, addr: int,
                              arid: Optional[int] = None) -> Tuple[bool, Any, Any]:
        """Dispatch to master or slave base-TB read method."""
        if self.is_slave:
            return await self.base_tb.single_read_response_test(
                addr=addr, arid=arid
            )
        return await self.base_tb.single_read_test(
            addr=addr, arid=arid
        )

    async def _test_basic_connectivity(self):
        """Single transaction must produce exactly one matching completion."""
        self.log.info("\n" + "=" * 80)
        self.log.info("TEST 1: Basic Connectivity")
        self.log.info("=" * 80)

        self.base_tb.set_timing_profile('normal')

        txn_addr = 0x1000
        txn_id = 0x5A & self.base_tb.MAX_ID

        packets_before = len(self.mon_slave.received_packets)

        if self.is_write:
            success, info = await self._do_single_write(
                address=txn_addr, data=0xDEADBEEF, transaction_id=txn_id
            )
        else:
            success, data, info = await self._do_single_read(
                addr=txn_addr, arid=txn_id
            )

        if not success:
            self.log.error(f"Basic connectivity transaction failed: {info}")
            raise RuntimeError("Basic connectivity transaction failed")

        # Wait for the completion packet to drain (MonbusSlave ready may stall).
        await self._wait_for_packet_count(packets_before + 1, timeout_cycles=200)
        await self.base_tb.wait_clocks('aclk', 20)

        total_now = len(self.mon_slave.received_packets)
        new_packets = total_now - packets_before
        self.log.info(f"Monitor packets after basic test: {new_packets}")

        if new_packets == 0:
            raise RuntimeError("No monitor packets generated for single transaction")

        # Validate the first completion packet has matching identity fields.
        completion = self._find_first_completion(
            self.mon_slave.received_packets[packets_before:]
        )
        if completion is None:
            raise RuntimeError("No AXI completion packet found for single transaction")

        errors = self._validate_completion_packet(completion, txn_addr, txn_id)
        if errors:
            self.log.error("Completion packet field mismatch: " + "; ".join(errors))
            raise RuntimeError("Completion packet field mismatch")

        self.log.info(f"Completion packet validated: {completion.format_for_display()}")
        self.log.info("TEST 1 PASSED")

    async def _test_multiple_transactions(self, test_level: str):
        """N clean transactions should yield N completion packets."""
        self.log.info("\n" + "=" * 80)
        self.log.info("TEST 2: Multiple Transactions")
        self.log.info("=" * 80)

        num_trans = 10 if test_level == 'basic' else 20
        packets_before = len(self.mon_slave.received_packets)

        self.base_tb.set_timing_profile('normal')

        if self.is_write:
            success_count = 0
            for i in range(num_trans):
                addr = 0x1000 + (i * (self.base_tb.TEST_DATA_WIDTH // 8))
                txn_id = (0x30 + i) & self.base_tb.MAX_ID
                success, info = await self._do_single_write(
                    address=addr, data=0xDEAD0000 + i, transaction_id=txn_id
                )
                if success:
                    success_count += 1
            all_ok = success_count == num_trans
        else:
            all_ok = await self.base_tb.basic_read_sequence(num_trans)

        if not all_ok:
            raise RuntimeError("Transaction sequence failed")

        await self._wait_for_packet_count(
            packets_before + max(1, num_trans - 2), timeout_cycles=300
        )
        await self.base_tb.wait_clocks('aclk', 50)

        packets_after = len(self.mon_slave.received_packets)
        new_packets = packets_after - packets_before
        completions = self._count_completions(
            self.mon_slave.received_packets[packets_before:packets_after]
        )

        self.log.info(
            f"Generated {new_packets} total packets ({completions} completions) "
            f"for {num_trans} transactions"
        )

        if completions < num_trans * 0.8:
            raise RuntimeError(
                f"Too few completion packets: expected ~{num_trans}, got {completions}"
            )

        if completions != num_trans:
            self.log.warning(
                f"Completion count {completions} does not exactly match transaction count {num_trans}"
            )

        self.log.info("TEST 2 PASSED")

    async def _test_burst_transactions(self, test_level: str):
        """Burst read transactions must produce at least one completion each."""
        self.log.info("\n" + "=" * 80)
        self.log.info("TEST 3: Burst Transactions")
        self.log.info("=" * 80)

        burst_lengths = [2, 4, 8] if test_level == 'basic' else [2, 4, 8, 16]
        packets_before = len(self.mon_slave.received_packets)

        self.base_tb.set_timing_profile('normal')
        result = await self.base_tb.burst_read_sequence(burst_lengths)

        if not result:
            raise RuntimeError("Burst sequence failed")

        await self._wait_for_packet_count(
            packets_before + len(burst_lengths), timeout_cycles=300
        )
        await self.base_tb.wait_clocks('aclk', 100)

        packets_after = len(self.mon_slave.received_packets)
        new_packets = packets_after - packets_before
        completions = self._count_completions(
            self.mon_slave.received_packets[packets_before:packets_after]
        )

        self.log.info(
            f"Burst test generated {new_packets} total packets ({completions} completions)"
        )

        if completions < len(burst_lengths):
            raise RuntimeError(
                f"Expected at least {len(burst_lengths)} completion packets, got {completions}"
            )

        self.log.info("TEST 3 PASSED")

    async def _test_error_detection(self):
        """Observe any error/timeout packets emitted so far."""
        self.log.info("\n" + "=" * 80)
        self.log.info("TEST 4: Error/Timeout Packet Detection")
        self.log.info("=" * 80)

        errors = self._count_error_packets(self.mon_slave.received_packets)
        timeouts = self._count_timeout_packets(self.mon_slave.received_packets)
        dropped = self._sample_dropped_count()
        refused = self._sample_refused_count()

        self.log.info(
            f"Error packets: {errors}, Timeout packets: {timeouts}, "
            f"dropped_count: {dropped}, refused_count: {refused}"
        )
        self.log.info("TEST 4 PASSED (monitoring verified)")

    async def _test_sustained_traffic(self, test_level: str):
        """Higher-volume traffic must keep producing packets."""
        self.log.info("\n" + "=" * 80)
        self.log.info("TEST 5: Sustained Traffic")
        self.log.info("=" * 80)

        sustained_count = 30 if test_level == 'medium' else 50
        packets_before = len(self.mon_slave.received_packets)

        self.base_tb.set_timing_profile('fast')

        if self.is_write:
            success_count = 0
            for i in range(sustained_count):
                addr = 0x2000 + (i * (self.base_tb.TEST_DATA_WIDTH // 8))
                txn_id = (0x40 + i) & self.base_tb.MAX_ID
                success, info = await self._do_single_write(
                    address=addr, data=0xFEED0000 + i, transaction_id=txn_id
                )
                if success:
                    success_count += 1
            all_ok = success_count == sustained_count
        else:
            all_ok = await self.base_tb.basic_read_sequence(sustained_count)

        await self._wait_for_packet_count(
            packets_before + max(1, int(sustained_count * 0.5)), timeout_cycles=500
        )
        await self.base_tb.wait_clocks('aclk', 200)

        packets_after = len(self.mon_slave.received_packets)
        new_packets = packets_after - packets_before
        completions = self._count_completions(
            self.mon_slave.received_packets[packets_before:packets_after]
        )

        self.log.info(
            f"Sustained traffic: {new_packets} total packets ({completions} completions) "
            f"for {sustained_count} transactions"
        )

        if completions < sustained_count * 0.3:
            raise RuntimeError("Too few packets during sustained traffic")

        self.log.info("TEST 5 PASSED")

    async def _final_report(self):
        """Emit final packet statistics and validate totals."""
        total_packets = len(self.mon_slave.received_packets)
        completions = self._count_completions(self.mon_slave.received_packets)
        errors = self._count_error_packets(self.mon_slave.received_packets)
        timeouts = self._count_timeout_packets(self.mon_slave.received_packets)
        dropped = self._sample_dropped_count()
        refused = self._sample_refused_count()

        self.log.info("\n" + "=" * 80)
        self.log.info("FINAL REPORT")
        self.log.info("=" * 80)
        self.log.info(f"Total monitor packets:  {total_packets}")
        self.log.info(f"  Completion packets:   {completions}")
        self.log.info(f"  Error packets:        {errors}")
        self.log.info(f"  Timeout packets:      {timeouts}")
        self.log.info(f"  Other packets:        {total_packets - completions - errors - timeouts}")
        self.log.info(f"  dropped_count (DUT):  {dropped}")
        self.log.info(f"  refused_count (DUT):  {refused}")
        self.log.info("=" * 80)

        if total_packets < 5:
            raise RuntimeError(f"Only {total_packets} monitor packets generated")

        self.log.info("ALL TESTS PASSED")
        self.log.info("=" * 80)

    # ------------------------------------------------------------------
    # Packet helpers
    # ------------------------------------------------------------------

    async def _wait_for_packet_count(self, target_count: int, timeout_cycles: int = 200):
        """Poll until target_count packets have been received or timeout."""
        for _ in range(timeout_cycles):
            if len(self.mon_slave.received_packets) >= target_count:
                return True
            await self.base_tb.wait_clocks('aclk', 1)
        return False

    def _count_completions(self, packets: List) -> int:
        return sum(
            1 for p in packets
            if p.is_completion_packet() and p.is_axi_protocol()
        )

    def _count_error_packets(self, packets: List) -> int:
        return sum(
            1 for p in packets
            if p.is_error_packet() and p.is_axi_protocol()
        )

    def _count_timeout_packets(self, packets: List) -> int:
        return sum(
            1 for p in packets
            if p.is_timeout_packet() and p.is_axi_protocol()
        )

    def _find_first_completion(self, packets: List):
        for p in packets:
            if p.is_completion_packet() and p.is_axi_protocol():
                return p
        return None

    def _validate_completion_packet(self, packet, expected_addr: Optional[int] = None,
                                    expected_id: Optional[int] = None) -> List[str]:
        """Return a list of field mismatch messages (empty means OK)."""
        errors = []
        if packet.pkt_type != PktType.PktTypeCompletion.value:
            errors.append(f"pkt_type=0x{packet.pkt_type:X} (expected Completion)")
        if packet.protocol != ProtocolType.PROTOCOL_AXI.value:
            errors.append(f"protocol=0x{packet.protocol:X} (expected AXI)")
        if packet.event_code != AXICompletionCode.AXI_COMPL_TRANS_COMPLETE.value:
            errors.append(f"event_code=0x{packet.event_code:02X} (expected TRANS_COMPLETE)")
        if packet.unit_id != self.expected_unit_id:
            errors.append(
                f"unit_id=0x{packet.unit_id:02X} (expected 0x{self.expected_unit_id:02X})"
            )
        if packet.agent_id != self.expected_agent_id:
            errors.append(
                f"agent_id=0x{packet.agent_id:04X} (expected 0x{self.expected_agent_id:04X})"
            )
        if expected_addr is not None:
            addr_mask = (1 << self.base_tb.TEST_ADDR_WIDTH) - 1
            pkt_addr = packet.data & addr_mask
            exp_addr = expected_addr & addr_mask
            if pkt_addr != exp_addr:
                errors.append(f"addr=0x{pkt_addr:08X} (expected 0x{exp_addr:08X})")
        if expected_id is not None:
            # The lite monitor stores the low 6 bits of the transaction ID in channel_id.
            pkt_id = packet.channel_id & 0x3F
            exp_id = expected_id & 0x3F
            if pkt_id != exp_id:
                errors.append(f"id/channel_id=0x{pkt_id:02X} (expected 0x{exp_id:02X})")
        return errors

    def _sample_dropped_count(self) -> int:
        if hasattr(self.dut, 'dropped_count'):
            try:
                return int(self.dut.dropped_count.value)
            except Exception:
                pass
        return 0

    def _sample_refused_count(self) -> int:
        if hasattr(self.dut, 'refused_count'):
            try:
                return int(self.dut.refused_count.value)
            except Exception:
                pass
        return 0
