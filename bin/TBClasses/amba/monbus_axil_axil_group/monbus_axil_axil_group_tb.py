# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MonbusAxilAxilGroupTB
# Purpose: MonBus AXIL/AXIL Group testbench. Drives the AXIL-slave-read +
#          AXIL-master-write member of the monbus_<p1>_<p2>_group family.
#
# Documentation: rtl/amba/PRD.md
# Subsystem: amba (shared)
#
# Author: sean galloway
# Created: 2025-10-19 (originally STREAM-local); moved to bin/TBClasses
#          2026-06-08; renamed 2026-06-10 to track the family refactor.

"""
MonBus AXIL/AXIL Group testbench — covers the AXIL-slave-read +
AXIL-master-write member of the monbus_<p1>_<p2>_group family
(`rtl/amba/shared/monbus_axil_axil_group.sv`). The other family
members (axil_axi4, axi4_axil, axi4_axi4) have separate TBs / tests
because their port surfaces differ.

Scope (AXI protocol only — matches what the shared module supports):
- Monitor bus packet aggregation from data paths
- AXI protocol packet filtering and validation
- Error/Interrupt FIFO testing via AXI-Lite slave read interface
- Master write FIFO testing via AXI-Lite master write interface
- Configuration register testing
- Stress testing with concurrent packet streams

Originally written as STREAM's simplified port of the RAPIDS TB; lifted
here so val/amba tests can reuse it without crossing project areas.
"""

import os
import random
import time
from typing import List, Dict, Any, Tuple, Optional
from collections import defaultdict, deque

import cocotb
from cocotb.triggers import Combine

# Framework imports
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXIL4 imports for slave/master interfaces
from CocoTBFramework.components.axil4.axil4_factories import (
    create_axil4_master_rd, create_axil4_master_wr
)

# MonBus imports
from TBClasses.monbus.monbus_types import (
    ProtocolType, PktType, ARBErrorCode, ARBCompletionCode
)
from TBClasses.monbus.monbus_packet import create_monbus_field_config

# GAXI for monitor bus driving
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from TBClasses.scoreboards.monbus_group import (
    MonbusGroupHarness, BeatLayout, BeatOrder,
)


class MonbusAxilAxilGroupTB(TBBase):
    """
    MonBus AXIL/AXIL Group testbench.

    Tests:
    - Monitor bus packet ingestion via the input stream (single-input;
      upstream arbitration if any is the caller's responsibility).
    - AXI protocol packet filtering (AXIS / CORE also supported by the
      RTL but not exercised here).
    - Error / interrupt FIFO drain via the AXIL slave-read interface.
    - The master-write side is allowed to flush via watermark / timeout
      but is not consumed at the test layer in this minimal TB (the
      AXIL master outputs are tied off in the test wrapper). A
      dedicated AXIL/AXI4 burst test covers the master-write path
      with a real consumer.
    """

    def __init__(self, dut, axi_aclk=None, axi_aresetn=None):
        super().__init__(dut)

        # Test configuration from environment.
        # FIFO_DEPTH_WRITE is now in BEATS (one queue entry == one 64-bit beat).
        self.TEST_FIFO_DEPTH_ERR     = int(os.environ.get('TEST_FIFO_DEPTH_ERR', '64'))
        self.TEST_FIFO_DEPTH_WRITE   = int(os.environ.get('TEST_FIFO_DEPTH_WRITE', '96'))
        self.TEST_ADDR_WIDTH         = int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_NUM_PROTOCOLS      = int(os.environ.get('TEST_NUM_PROTOCOLS', '3'))
        self.TEST_FLUSH_WATERMARK    = int(os.environ.get('TEST_FLUSH_WATERMARK', '24'))   # beats
        self.TEST_FLUSH_TIMEOUT_CYC  = int(os.environ.get('TEST_FLUSH_TIMEOUT_CYC', '1024'))
        # Err-FIFO drain AXIL data width (S_AXIL_DATA_WIDTH on the DUT). 64 = one
        # beat per record slice; 32 = the 2:1 read serializer (low/high halves,
        # 6 beats/record). The harness handles the recombination transparently.
        self.TEST_S_AXIL_DATA_WIDTH  = int(os.environ.get('TEST_S_AXIL_DATA_WIDTH', '64'))
        self.SEED = int(os.environ.get('SEED', '12345'))

        random.seed(self.SEED)

        # Setup clock and reset signals
        self.axi_aclk = axi_aclk or dut.axi_aclk
        self.axi_aresetn = axi_aresetn or dut.axi_aresetn
        self.clk_name = self.axi_aclk._name if hasattr(self.axi_aclk, '_name') else 'axi_aclk'
        self.rst_n = self.axi_aresetn

        # Test statistics (simplified from RAPIDS)
        self.stats = {
            'packets_sent': 0,
            'packets_filtered': {'dropped': 0, 'to_err_fifo': 0, 'to_write_fifo': 0},
            'protocol_stats': defaultdict(int),
            'error_fifo_reads': 0,
            'master_writes': 0,
            'test_start_time': 0,
            'test_end_time': 0
        }

        # Packet queues
        self.expected_error_packets = deque()
        self.received_error_packets = deque()

        # Components (initialized in setup)
        self.monbus_master = None
        # Shared monbus-group harness: err-FIFO drain reads + master-write
        # sink (replaces the framework error_fifo_reader BFM + the hand-rolled
        # _drive_master_write_sink). Ctor only stores signal handles.
        self.mon = MonbusGroupHarness(
            self.dut, self.axi_aclk,
            drain_proto="axil", trace_proto="axil",
            drain_prefix="s_axil_", trace_prefix="m_axil_",
            drain_data_width=self.TEST_S_AXIL_DATA_WIDTH,
            group_node=self.dut, irq_sig=self.dut.irq_out, log=self.log,
            # Drain + trace both emit {tag,ts}, packet[127:64], packet[63:0]
            # per docs/markdown/RTLAmba/includes/monitor_package_spec.md.
            layout_drain=BeatLayout(order=BeatOrder.TS_HI_LO),
            layout_trace=BeatLayout(order=BeatOrder.TS_HI_LO),
        )

        # Optional monbus sniffer for offline analysis with monbus_compressor.
        # Activated when MONBUS_CAPTURE is set in the environment; output is
        # written to that path (.json or .csv extension). Behavior is
        # otherwise unchanged so existing tests are unaffected by default.
        self.monbus_sniffer = None
        self._monbus_capture_path = os.environ.get('MONBUS_CAPTURE', '').strip()

    # ========================================================================
    # MANDATORY: Clock and Reset Control Methods
    # ========================================================================

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks and performs reset sequence."""
        self.log.info("Starting clocks and reset sequence...")

        await self.start_clock(self.clk_name, freq=10, units='ns')  # 100 MHz

        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        self.log.info("✅ Clocks started and reset sequence completed")

    async def assert_reset(self):
        """Assert reset signal (active-low)."""
        self.axi_aresetn.value = 0

    async def deassert_reset(self):
        """Deassert reset signal (active-low)."""
        self.axi_aresetn.value = 1

    # ========================================================================
    # Interface Setup
    # ========================================================================

    async def setup_interfaces(self):
        """Setup all interface components"""
        self.log.info("Setting up MonBus AXIL/AXIL Group interfaces...")

        # Initialize configuration signals
        await self.initialize_config_signals()

        # MonBus field configuration
        monbus_config = create_monbus_field_config()

        # Monitor bus master (single input - STREAM has no source/sink separation)
        self.monbus_master = create_gaxi_master(
            dut=self.dut,
            title="MonBus Master",
            prefix="monbus",
            clock=self.axi_aclk,
            field_config=monbus_config,
            signal_map={'data': 'monbus_packet'},
            log=self.log
        )

        # Err-FIFO drain is handled by the shared MonbusGroupHarness
        # (self.mon.drain_read_beat); no separate reader BFM needed.

        # Optional monbus sniffer (gated on MONBUS_CAPTURE env var).
        if self._monbus_capture_path:
            from TBClasses.monbus.sniffer import MonbusSniffer
            self.monbus_sniffer = MonbusSniffer(
                valid_sig     = self.dut.monbus_valid,
                ready_sig     = self.dut.monbus_ready,
                packet_sig    = self.dut.monbus_packet,
                timestamp_sig = self.dut.monbus_timestamp,
                clk_sig       = self.axi_aclk,
                label         = "monbus_axil_group_tb",
            )
            self.monbus_sniffer.start()
            self.log.info(
                f"✅ MonbusSniffer started (will dump to {self._monbus_capture_path})"
            )

        self.log.info("✅ All interfaces setup completed")

    def finalize_monbus_capture(self):
        """Call at end-of-test to flush the sniffer's records to disk.
        No-op if MONBUS_CAPTURE env var was not set."""
        if self.monbus_sniffer is None:
            return
        self.monbus_sniffer.stop()
        path = self._monbus_capture_path
        ext = os.path.splitext(path)[1].lower()
        meta = {
            "test": "test_monbus_axil_axil_group",
            "fifo_depth_err":   self.TEST_FIFO_DEPTH_ERR,
            "fifo_depth_write": self.TEST_FIFO_DEPTH_WRITE,    # beats
            "addr_width":       self.TEST_ADDR_WIDTH,
            "flush_watermark":  self.TEST_FLUSH_WATERMARK,
            "seed":             self.SEED,
        }
        if ext == ".csv":
            self.monbus_sniffer.dump_csv(path)
        else:
            self.monbus_sniffer.dump_json(path, extra_meta=meta)
        self.log.info(
            f"✅ MonbusSniffer captured {self.monbus_sniffer.count} records → {path}"
        )

    async def initialize_config_signals(self):
        """Initialize RTL configuration signals"""
        self.log.info("Initializing configuration signals...")

        # AXI protocol: Route errors to error FIFO
        self.dut.cfg_axi_pkt_mask.value = 0x0000  # Don't drop packets
        self.dut.cfg_axi_err_select.value = 0x0001  # Route ERROR packets to error FIFO

        # Master-write window. Default to a 16 KiB scratch range starting
        # at 0x0000_1000 -- well within ADDR_WIDTH=32 and aligned for
        # 8-byte beats. Watermark default 24 beats (= 8 records in raw
        # mode) keeps the writer relatively eager so tests don't have to
        # wait for the timeout to see master-write activity.
        self.dut.cfg_base_addr.value       = 0x0000_1000
        self.dut.cfg_limit_addr.value      = 0x0000_5000 - 1
        self.dut.cfg_flush_watermark.value = self.TEST_FLUSH_WATERMARK

        # Master-write side is unconsumed in this minimal TB. The shared
        # harness's trace consumer drives awready/wready/bvalid (single
        # outstanding) so the burst writer drains freely into the void --
        # replaces the hand-rolled awvalid->bvalid mirror sink.
        self.mon.start_trace_consumer()

        await self.wait_clocks(self.clk_name, 1)
        self.log.info("✅ Configuration signals initialized")

    # ========================================================================
    # Test Methods
    # ========================================================================

    def create_monbus_packet_dict(self, pkt_type: PktType, event_code: int,
                                 channel_id: int = 0, data: int = 0) -> Dict[str, Any]:
        """Create MonBus packet dictionary for AXI protocol"""
        return {
            'pkt_type': pkt_type.value,
            'protocol': ProtocolType.PROTOCOL_AXI.value,  # STREAM uses AXI only
            'event_code': event_code,
            'channel_id': channel_id,
            'unit_id': 0,
            'agent_id': 0x10,
            'data': data & ((1 << 64) - 1)  # 64-bit event_data field
        }

    async def send_packet(self, packet_dict: Dict[str, Any]) -> bool:
        """Send packet via monitor bus"""
        try:
            packet = self.monbus_master.create_packet(**packet_dict)
            await self.monbus_master.send(packet)
            self.stats['packets_sent'] += 1
            return True
        except Exception as e:
            self.log.error(f"Failed to send packet: {e}")
            return False

    async def read_error_fifo(self, address: int = 0x0) -> Optional[int]:
        """Read one 64-bit beat from the error FIFO via the shared harness."""
        try:
            data = await self.mon.drain_read_beat(address)
            self.stats['error_fifo_reads'] += 1
            return data
        except Exception as e:
            self.log.error(f"Failed to read error FIFO: {e}")
            return None

    async def test_basic_packet_flow(self, count: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """Test basic packet flow (AXI protocol only)"""
        self.log.info(f"Testing basic packet flow with {count} AXI packets...")

        success_count = 0

        for i in range(count):
            pkt_type = random.choice([PktType.PktTypeError, PktType.PktTypeCompletion])
            event_code = 0x1 if pkt_type == PktType.PktTypeError else 0x0

            packet_dict = self.create_monbus_packet_dict(
                pkt_type=pkt_type,
                event_code=event_code,
                channel_id=i % 8,  # STREAM has 8 channels
                data=0x1000 + i
            )

            if await self.send_packet(packet_dict):
                success_count += 1

            await self.wait_clocks(self.clk_name, random.randint(1, 5))

        success_rate = success_count / count if count > 0 else 0.0
        return success_rate > 0.9, {'success_rate': success_rate, 'packets_sent': success_count}

    async def test_error_fifo_functionality(self, count: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test error FIFO functionality"""
        self.log.info(f"Testing error FIFO with {count} error packets...")

        # Send error packets
        for i in range(count):
            packet_dict = self.create_monbus_packet_dict(
                pkt_type=PktType.PktTypeError,
                event_code=0x1,
                channel_id=i,
                data=0x2000 + i
            )
            await self.send_packet(packet_dict)
            await self.wait_clocks(self.clk_name, 2)

        # Wait for packets to propagate
        await self.wait_clocks(self.clk_name, 50)

        # Read from error FIFO
        packets_read = 0
        for i in range(count + 2):
            data = await self.read_error_fifo()
            if data is not None and data != 0:
                packets_read += 1
            await self.wait_clocks(self.clk_name, 2)

        success_rate = packets_read / count if count > 0 else 0.0
        return success_rate > 0.5, {'packets_read': packets_read, 'success_rate': success_rate}

    async def test_error_fifo_decode(self, count: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Drive known error packets, drain via the AXIL slave-read port, and
        verify every drained record DECODES correctly (packet_type, protocol,
        channel_id, event_data). Unlike test_error_fifo_functionality (which
        only counts non-zero beats), this reassembles full 24-byte records via
        the harness, so it exercises the err-FIFO drain datapath end to end --
        in particular the 2:1 read serializer when S_AXIL_DATA_WIDTH==32, which
        must preserve the upper 32 bits of every slice (packet_type lives at
        bit 127). A naive 32-bit truncation would silently corrupt the type."""
        self.log.info(f"Decoding {count} error packets via "
                      f"{self.TEST_S_AXIL_DATA_WIDTH}-bit err-FIFO drain...")

        # Distinct channel_id + event_data per packet so order/content is checked.
        expected = []
        for i in range(count):
            ch = i & 0x1FF
            data = (0x5A5A_0000 + (i << 8) + i) & ((1 << 64) - 1)
            await self.send_packet(self.create_monbus_packet_dict(
                pkt_type=PktType.PktTypeError, event_code=0x1,
                channel_id=ch, data=data))
            expected.append((ch, data))
            await self.wait_clocks(self.clk_name, 2)

        await self.wait_clocks(self.clk_name, 50)

        # Drain exactly `count` records (harness recombines 32-bit sub-beats).
        drained = await self.mon.drain_records(count)

        ok = True
        if len(drained) != count:
            self.log.error(f"drained {len(drained)} records, expected {count}")
            ok = False
        for idx, p in enumerate(drained):
            exp_ch, exp_data = expected[idx] if idx < count else (None, None)
            if p.packet_type != PktType.PktTypeError:
                self.log.error(f"[{idx}] type={p.get_packet_type_name()} != PktTypeError")
                ok = False
            if int(p.protocol) != ProtocolType.PROTOCOL_AXI.value:
                self.log.error(f"[{idx}] protocol={int(p.protocol)} != AXI")
                ok = False
            if exp_ch is not None and p.channel_id != exp_ch:
                self.log.error(f"[{idx}] channel_id=0x{p.channel_id:x} != 0x{exp_ch:x}")
                ok = False
            if exp_data is not None and p.event_data != exp_data:
                self.log.error(f"[{idx}] event_data=0x{p.event_data:x} != 0x{exp_data:x}")
                ok = False
        self.log.info(f"{'✅' if ok else '❌'} decoded {len(drained)}/{count} error "
                      f"records via {self.TEST_S_AXIL_DATA_WIDTH}-bit drain")
        return ok, {'records': len(drained), 'expected': count,
                    'drain_width': self.TEST_S_AXIL_DATA_WIDTH}

    def finalize_test(self):
        """Generate final test statistics"""
        self.stats['test_end_time'] = time.time()
        duration = self.stats['test_end_time'] - self.stats['test_start_time']

        self.log.info("="*60)
        self.log.info("MONBUS AXIL/AXIL GROUP TEST STATISTICS")
        self.log.info("="*60)
        self.log.info(f"Test duration: {duration:.2f} seconds")
        self.log.info(f"Total packets sent: {self.stats['packets_sent']}")
        self.log.info(f"Error FIFO reads: {self.stats['error_fifo_reads']}")
        self.log.info("="*60)
