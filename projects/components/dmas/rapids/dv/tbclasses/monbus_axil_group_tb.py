# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MonbusAxilGroupTB
# Purpose: MonBus AXIL Group Testbench - v1.0
#
# Documentation: projects/components/dmas/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
MonBus AXIL Group Testbench - v1.0

Comprehensive testbench for the monbus_axil_group module following the established
datapath testbench methodology. Tests monitor bus aggregation, filtering,
and AXI-Lite interface functionality.

Features:
- Monitor bus packet injection and validation
- Protocol-specific filtering validation (AXI, Network, ARB)
- Error/Interrupt FIFO testing via AXI-Lite slave read interface
- Master write FIFO testing via AXI-Lite master write interface
- Configuration register testing
- Stress testing with concurrent packet streams
- Error injection and boundary condition testing
- Comprehensive statistics and reporting

Based on datapath TB patterns with real AXIL4 and MonBus component integration.
"""

import os
import random
import asyncio
from typing import List, Dict, Any, Tuple, Optional, Union
import time
from collections import defaultdict, deque

# CocoTB imports
import cocotb
from cocotb.triggers import Combine, RisingEdge, FallingEdge, ReadOnly

# Framework imports
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXIL4 imports for slave/master interfaces
from CocoTBFramework.components.axil4.axil4_factories import (
    create_axil4_master_rd, create_axil4_master_wr,
    create_axil4_slave_wr, create_axil4_slave_rd,
    print_unified_compliance_reports
)
from CocoTBFramework.components.axil4.axil4_packet import AXIL4Packet
from CocoTBFramework.components.axil4.axil4_compliance_checker import AXIL4ComplianceChecker

# MonBus imports for packet generation and validation - ONLY EXISTING IMPORTS
from TBClasses.monbus.monbus_types import (
    ProtocolType, PktType,
    ARBErrorCode, ARBTimeoutCode, ARBCompletionCode, ARBThresholdCode,
    ARBPerformanceCode, ARBDebugCode
)
from TBClasses.monbus.monbus_packet import MonbusPacket, create_monbus_field_config
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_validators import (
    validate_packet_consistency, validate_arb_protocol_packet,
    create_packet_matcher
)

# GAXI for monitor bus driving
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_monitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket


class MonbusAxilGroupTB(TBBase):
    """
    Complete MonBus AXIL Group testbench for monitor bus aggregation and filtering.

    Tests:
    - Monitor bus packet arbitration between source and sink
    - Protocol-specific packet filtering and routing
    - Error/Interrupt FIFO via AXI-Lite slave read interface
    - Master write operations via AXI-Lite master write interface
    - Configuration register functionality
    - Multi-protocol packet validation (AXI, Network, ARB only)
    """

    def __init__(self, dut, axi_aclk=None, axi_aresetn=None):
        super().__init__(dut)

        # Test configuration from environment
        self.TEST_ADDR_WIDTH = int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_DATA_WIDTH = int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_FIFO_DEPTH_ERR = int(os.environ.get('TEST_FIFO_DEPTH_ERR', '64'))
        self.TEST_FIFO_DEPTH_WRITE = int(os.environ.get('TEST_FIFO_DEPTH_WRITE', '32'))
        self.TEST_NUM_PROTOCOLS = int(os.environ.get('TEST_NUM_PROTOCOLS', '3'))
        self.SEED = int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.axi_aclk = axi_aclk or dut.axi_aclk
        self.axi_aresetn = axi_aresetn or dut.axi_aresetn
        self.clk_name = self.axi_aclk._name if hasattr(self.axi_aclk, '_name') else 'axi_aclk'
        self.rst_n = self.axi_aresetn  # Alias for consistency

        # Test statistics
        self.stats = {
            'packets_sent': {'source': 0, 'sink': 0},
            'packets_filtered': {'dropped': 0, 'to_err_fifo': 0, 'to_write_fifo': 0},
            'protocol_stats': defaultdict(lambda: defaultdict(int)),
            'error_fifo_reads': 0,
            'master_writes': 0,
            'config_operations': 0,
            'test_start_time': 0,
            'test_end_time': 0
        }

        # Packet queues for validation
        self.expected_error_packets = deque()
        self.expected_write_packets = deque()
        self.received_error_packets = deque()
        self.received_write_packets = deque()

        # Test timing profiles
        self.timing_profiles = {
            'fast': {'ready_prob': 0.95, 'valid_prob': 0.95, 'idle_cycles': (0, 2)},
            'normal': {'ready_prob': 0.85, 'valid_prob': 0.8, 'idle_cycles': (1, 5)},
            'slow': {'ready_prob': 0.7, 'valid_prob': 0.65, 'idle_cycles': (2, 10)},
            'stress': {'ready_prob': 0.9, 'valid_prob': 0.9, 'idle_cycles': (0, 1)}
        }
        self.current_timing = 'normal'

        # Initialize components (will be set in setup)
        self.source_monbus_master = None
        self.sink_monbus_master = None
        self.error_fifo_reader = None
        self.master_write_slave = None
        self.config_interface = None

        # Randomizer for test generation (using simple timing constraints)
        self.randomizer = FlexRandomizer({
            'packet_delay': ([(1, 5), (10, 20)], [0.7, 0.3]),
            'operation_delay': ([(2, 8), (15, 25)], [0.8, 0.2])
        })

    # ========================================================================
    # MANDATORY: Clock and Reset Control Methods
    # ========================================================================

    async def setup_clocks_and_reset(self):
        """
        Complete initialization - starts clocks and performs reset sequence.

        MANDATORY METHOD: Required by testbench methodology.
        """
        self.log.info("Starting clocks and reset sequence...")

        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')  # 100 MHz

        # Set any config signals that must be valid BEFORE reset
        # (For this module, config can be set after reset)

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)  # Hold reset for 10 cycles
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)   # Stabilization time

        self.log.info("✅ Clocks started and reset sequence completed")

    async def assert_reset(self):
        """
        Assert reset signal (active-low).

        MANDATORY METHOD: Required by testbench methodology.
        """
        self.axi_aresetn.value = 0
        self.log.debug("Reset asserted (aresetn=0)")

    async def deassert_reset(self):
        """
        Deassert reset signal (active-low).

        MANDATORY METHOD: Required by testbench methodology.
        """
        self.axi_aresetn.value = 1
        self.log.debug("Reset deasserted (aresetn=1)")

    # ========================================================================
    # Interface Setup
    # ========================================================================

    async def setup_interfaces(self):
        """Setup all interface components following datapath patterns"""
        self.log.info("Setting up MonBus AXIL Group interfaces...")

        # Initialize all configuration signals to safe defaults
        await self.initialize_config_signals()

        # Create MonBus field configuration
        monbus_config = create_monbus_field_config()

        # Source monitor bus master (for injecting source packets)
        # Use explicit signal_map because RTL has 'packet' not 'data'
        self.source_monbus_master = create_gaxi_master(
            dut=self.dut,
            title="Source MonBus Master",
            timeout_cycles=20000,   # the AXIL write path drains ~1 beat per handshake; sends legitimately wait
            prefix="source_monbus",
            clock=self.axi_aclk,
            field_config=monbus_config,
            # The framework requires the full valid/data/ready triple in an
            # explicit signal_map; it used to accept 'data' alone. RTL names
            # the payload 'packet', which is why the map exists at all.
            signal_map={'valid': 'source_monbus_valid',
                        'ready': 'source_monbus_ready',
                        'data': 'source_monbus_packet'},
            log=self.log
        )

        # Sink monitor bus master (for injecting sink packets)
        # Use explicit signal_map because RTL has 'packet' not 'data'
        self.sink_monbus_master = create_gaxi_master(
            dut=self.dut,
            title="Sink MonBus Master",
            timeout_cycles=20000,   # the AXIL write path drains ~1 beat per handshake; sends legitimately wait
            prefix="sink_monbus",
            clock=self.axi_aclk,
            field_config=monbus_config,
            signal_map={'valid': 'sink_monbus_valid',
                        'ready': 'sink_monbus_ready',
                        'data': 'sink_monbus_packet'},
            log=self.log
        )

        # AXI-Lite slave read interface for error FIFO access
        # Use multi_sig=True because AXIL4 uses separate signals (araddr, arprot, rdata, etc.)
        # The drain is 64 bits wide (S_AXIL_DATA_WIDTH); the factory defaults to
        # 32 and silently truncated every slice to its low half, which is why
        # the record compare saw packet[127:96] as zero (rapids TASK-003).
        self.error_fifo_reader = create_axil4_master_rd(
            dut=self.dut,
            clock=self.axi_aclk,
            prefix="s_axil",
            multi_sig=True,
            data_width=self.TEST_DATA_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
            log=self.log
        )

        # AXI-Lite master write interface slave (receives master writes)
        # Use multi_sig=True because AXIL4 uses separate signals (awaddr, awprot, wdata, etc.)
        self.master_write_slave = create_axil4_slave_wr(
            dut=self.dut,
            clock=self.axi_aclk,
            prefix="m_axil",
            multi_sig=True,
            data_width=64,
            addr_width=self.TEST_ADDR_WIDTH,
            log=self.log
        )
        # Scoreboard taps (rapids TASK-003): every scenario used to count its own
        # BFM sends as "received" and could not fail. Observe the DUT instead --
        # the 2:1 arbiter output (every accepted packet passes it before the
        # filters), and the AW/W handshakes the master-write slave sees.
        self.arb_seen = []          # parsed MonitorPackets at arb_monbus_valid && arb_monbus_ready
        self.aw_seen = []
        self.w_seen = []
        # The slave BFM drives its ready signals only after reset_bus(); the old
        # TB never called it, so m_axil_awready sat low and the write path was
        # never exercised -- invisible while nothing checked for writes.
        for chn in ('AW', 'W', 'B'):
            comp = self.master_write_slave.get(chn)
            if comp is not None and hasattr(comp, 'reset_bus'):
                await comp.reset_bus()
        self.master_write_slave['AW'].add_callback(lambda pkt: self.aw_seen.append(pkt))
        self.master_write_slave['W'].add_callback(lambda pkt: self.w_seen.append(pkt))
        self.in_seen = {'source': 0, 'sink': 0}
        # Framework monitors, not hand-rolled samplers: the GAXI monitor samples the
        # handshake in the right phase, and the arbiter output is one more
        # valid/ready/packet interface (internal wires of the group top).
        self.arb_monitor = create_gaxi_monitor(
            dut=self.dut, title="Arbiter MonBus Monitor", prefix="arb_monbus", clock=self.axi_aclk,
            field_config=monbus_config, is_slave=True, log=self.log,
            signal_map={'valid': 'arb_monbus_valid', 'ready': 'arb_monbus_ready', 'data': 'arb_monbus_packet'})
        self.arb_monitor.add_callback(self._on_arb_packet)
        self.source_in_monitor = create_gaxi_monitor(
            dut=self.dut, title="Source Input Monitor", prefix="source_monbus", clock=self.axi_aclk,
            field_config=monbus_config, is_slave=True, log=self.log,
            signal_map={'valid': 'source_monbus_valid', 'ready': 'source_monbus_ready', 'data': 'source_monbus_packet'})
        self.source_in_monitor.add_callback(lambda pkt: self.in_seen.__setitem__('source', self.in_seen['source'] + 1))
        self.sink_in_monitor = create_gaxi_monitor(
            dut=self.dut, title="Sink Input Monitor", prefix="sink_monbus", clock=self.axi_aclk,
            field_config=monbus_config, is_slave=True, log=self.log,
            signal_map={'valid': 'sink_monbus_valid', 'ready': 'sink_monbus_ready', 'data': 'sink_monbus_packet'})
        self.sink_in_monitor.add_callback(lambda pkt: self.in_seen.__setitem__('sink', self.in_seen['sink'] + 1))

        # Initialize timing profiles
        self.set_timing_profile('normal')

        self.log.info("✅ All interfaces setup completed")

    async def initialize_config_signals(self):
        """Initialize all RTL configuration signals to safe defaults"""
        self.log.info("Initializing configuration signals to defaults...")

        # Set configuration base/limit addresses for master writes
        self.dut.cfg_base_addr.value = 0x10000000
        self.dut.cfg_flush_watermark.value = 1   # flush the write FIFO as soon as it holds a beat
        self.dut.cfg_compress_en.value = 0
        self.dut.cam_clear.value = 0
        self.dut.cfg_limit_addr.value = 0x1000FFFF

        # AXI protocol (protocol 0): Allow all packets, route errors to error FIFO
        self.dut.cfg_axi_pkt_mask.value = 0x0000  # Don't drop any packets
        self.dut.cfg_axi_err_select.value = 0x0001  # Route ERROR packets to error FIFO
        self.dut.cfg_axi_error_mask.value = 0x0000  # Don't mask any error events
        self.dut.cfg_axi_timeout_mask.value = 0x0000
        self.dut.cfg_axi_compl_mask.value = 0x0000
        self.dut.cfg_axi_thresh_mask.value = 0x0000
        self.dut.cfg_axi_perf_mask.value = 0x0000
        self.dut.cfg_axi_addr_mask.value = 0x0000
        self.dut.cfg_axi_debug_mask.value = 0x0000

        # AXIS protocol (protocol 1): Allow all packets, none to error FIFO
        self.dut.cfg_axis_pkt_mask.value = 0x0000
        self.dut.cfg_axis_err_select.value = 0x0000
        self.dut.cfg_axis_error_mask.value = 0x0000
        self.dut.cfg_axis_timeout_mask.value = 0x0000
        self.dut.cfg_axis_compl_mask.value = 0x0000
        self.dut.cfg_axis_credit_mask.value = 0x0000
        self.dut.cfg_axis_channel_mask.value = 0x0000
        self.dut.cfg_axis_stream_mask.value = 0x0000

        # CORE protocol (protocol 2 - used for ARB): Allow all packets, none to error FIFO
        self.dut.cfg_core_pkt_mask.value = 0x0000
        self.dut.cfg_core_err_select.value = 0x0000
        self.dut.cfg_core_error_mask.value = 0x0000
        self.dut.cfg_core_timeout_mask.value = 0x0000
        self.dut.cfg_core_compl_mask.value = 0x0000
        self.dut.cfg_core_thresh_mask.value = 0x0000
        self.dut.cfg_core_perf_mask.value = 0x0000
        self.dut.cfg_core_debug_mask.value = 0x0000

        await self.wait_clocks(self.clk_name, 1)  # Let defaults settle
        self.log.info("✅ Configuration signals initialized")

    def set_timing_profile(self, profile_name: str):
        """Set timing profile for test components"""
        if profile_name not in self.timing_profiles:
            self.log.warning(f"Unknown timing profile: {profile_name}, using 'normal'")
            profile_name = 'normal'

        self.current_timing = profile_name
        profile = self.timing_profiles[profile_name]

        # Apply to components if they exist
        # TODO: GAXIMaster doesn't currently support set_ready_probability()
        # This would need to be added to the GAXI framework if needed
        # For now, components use default timing

        self.log.info(f"Set timing profile to: {profile_name} (timing control not yet implemented)")

    def _on_arb_packet(self, pkt):
        """One packet left the source/sink arbiter; keep it in the decoded shape
        the checks use (protocol, packet_type, event_code, channel_id, event_data)."""
        from types import SimpleNamespace
        try:
            raw = int(pkt.pack()) if hasattr(pkt, 'pack') else 0
        except Exception:
            raw = 0
        self.arb_seen.append(SimpleNamespace(
            protocol=int(pkt.protocol), packet_type=int(pkt.pkt_type), event_code=int(pkt.event_code),
            channel_id=int(pkt.channel_id), event_data=int(pkt.data), raw_packet=raw))

    @staticmethod
    def _key(d):
        """(protocol, pkt_type) of a packet dict, for multiset comparison."""
        return (int(d['protocol']), int(d['pkt_type']))

    def _arb_keys(self, start):
        return sorted((p.protocol, p.packet_type) for p in self.arb_seen[start:])

    def create_monbus_packet_dict(self, protocol: ProtocolType, pkt_type: PktType,
                                 event_code: int, channel_id: int = 0, unit_id: int = 0,
                                 agent_id: int = 0x10, data: int = 0) -> Dict[str, Any]:
        """Create MonBus packet dictionary for GAXI"""
        return {
            'pkt_type': pkt_type.value,
            'protocol': protocol.value,
            'event_code': event_code,
            'channel_id': channel_id,
            'unit_id': unit_id,
            'agent_id': agent_id,
            'data': data & ((1 << 64) - 1)  # 64-bit event_data field
        }

    async def send_source_packet(self, packet_dict: Dict[str, Any]) -> bool:
        """Send packet via source monitor bus"""
        try:
            # Create GAXIPacket from dictionary using master's create_packet method
            packet = self.source_monbus_master.create_packet(**packet_dict)
            await self.source_monbus_master.send(packet)
            self.stats['packets_sent']['source'] += 1
            return True
        except Exception as e:
            self.log.error(f"Failed to send source packet: {e}")
            return False

    async def send_sink_packet(self, packet_dict: Dict[str, Any]) -> bool:
        """Send packet via sink monitor bus"""
        try:
            # Create GAXIPacket from dictionary using master's create_packet method
            packet = self.sink_monbus_master.create_packet(**packet_dict)
            await self.sink_monbus_master.send(packet)
            self.stats['packets_sent']['sink'] += 1
            return True
        except Exception as e:
            self.log.error(f"Failed to send sink packet: {e}")
            return False

    async def check_error_fifo_status(self) -> Dict[str, Any]:
        """Check error FIFO status signals.

        Derived entirely from the DUT's own port list -- no hierarchical
        reach-through. err_fifo_empty / err_fifo_rd_valid are internal
        signals of monbus_group_core (dut -> u_group -> u_core), and
        being plain continuous assigns they are not guaranteed to survive
        Verilator's optimizer, so probing them by path is both fragile
        against hierarchy changes and simulator-dependent.

        monbus_group_core defines:
            err_fifo_empty = !err_fifo_rd_valid
            irq_out        = !err_fifo_empty
        so irq_out is an exact, port-visible mirror of FIFO occupancy."""
        irq_out = int(self.dut.irq_out.value)
        status = {
            'empty': 0 if irq_out else 1,
            'full': int(self.dut.err_fifo_full.value),
            'count': int(self.dut.err_fifo_count.value),
            'rd_valid': irq_out,
            'irq_out': irq_out
        }
        return status

    async def read_error_fifo(self, address: int = 0x0) -> Optional[int]:
        """Read from error FIFO via AXI-Lite slave interface"""
        try:
            # Check FIFO status before reading
            status = await self.check_error_fifo_status()
            self.log.debug(f"Error FIFO status before read: {status}")

            if status['empty']:
                self.log.warning("Error FIFO is empty, read will likely fail")

            # AXIL4 simple_read returns int directly, not a dict
            data = await self.error_fifo_reader['simple_read'](address)

            # Update statistics
            self.stats['error_fifo_reads'] += 1
            self.log.debug(f"Successfully read from error FIFO: 0x{data:016X}")
            return data

        except Exception as e:
            self.log.error(f"Failed to read error FIFO: {e}")
            return None

    async def configure_protocol_filtering(self, protocol: ProtocolType,
                                         pkt_mask: int = 0x0000,
                                         err_select: int = 0xFFFF) -> bool:
        """Configure protocol-specific filtering by driving RTL config signals"""
        self.log.info(f"Configuring {protocol.name}: pkt_mask=0x{pkt_mask:04X}, err_select=0x{err_select:04X}")

        # Drive RTL configuration signals based on protocol
        if protocol == ProtocolType.PROTOCOL_AXI:
            self.dut.cfg_axi_pkt_mask.value = pkt_mask
            self.dut.cfg_axi_err_select.value = err_select
        elif protocol == ProtocolType.PROTOCOL_AXIS:
            self.dut.cfg_axis_pkt_mask.value = pkt_mask
            self.dut.cfg_axis_err_select.value = err_select
        elif protocol == ProtocolType.PROTOCOL_CORE:
            # ARB is protocol 2 (CORE in RTL)
            self.dut.cfg_core_pkt_mask.value = pkt_mask
            self.dut.cfg_core_err_select.value = err_select

        self.stats['config_operations'] += 1
        await self.wait_clocks(self.clk_name, 1)  # Let configuration settle
        return True

    async def wait_for_interrupt(self, timeout_cycles: int = 1000) -> bool:
        """Wait for interrupt signal assertion"""
        for _ in range(timeout_cycles):
            if hasattr(self.dut, 'interrupt') and self.dut.interrupt.value:
                return True
            await self.wait_clocks(self.clk_name, 1)
        return False

    async def initialize_test(self):
        """
        Initialize test environment.

        NOTE: Does NOT include clock/reset - use setup_clocks_and_reset() first!
        This method only sets up interfaces and initial configuration.
        """
        self.log.info("Initializing MonBus AXIL Group test...")
        self.stats['test_start_time'] = time.time()

        # Setup interfaces
        await self.setup_interfaces()

        # Initialize configuration registers to known state
        # Available protocols: AXI, AXIS, APB, ARB, CORE
        await self.configure_protocol_filtering(ProtocolType.PROTOCOL_AXI)
        await self.configure_protocol_filtering(ProtocolType.PROTOCOL_AXIS)
        await self.configure_protocol_filtering(ProtocolType.PROTOCOL_CORE)

        self.log.info("✅ Test initialization completed")

    async def reset_sequence(self):
        """
        Perform reset sequence (DEPRECATED - use mandatory methods instead).

        For new code, use:
          await tb.assert_reset()
          await tb.wait_clocks(clk_name, 10)
          await tb.deassert_reset()
        """
        self.log.warning("reset_sequence() is deprecated - use assert_reset() / deassert_reset()")

        # Use mandatory methods
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)

        self.log.info("✅ Reset sequence completed")

    async def test_basic_packet_flow(self, count: int = 32) -> Tuple[bool, Dict[str, Any]]:
        """Test basic packet flow through the system"""
        self.log.info(f"Testing basic packet flow with {count} packets...")

        success_count = 0
        total_count = count
        # Route every type to the write path (drained by m_axil) so the error
        # FIFO cannot fill up and stall the flow this test is measuring.
        for proto in (ProtocolType.PROTOCOL_AXI, ProtocolType.PROTOCOL_AXIS, ProtocolType.PROTOCOL_CORE):
            await self.configure_protocol_filtering(proto, pkt_mask=0x0000, err_select=0x0000)
        await self.wait_clocks(self.clk_name, 5)
        arb_start = len(self.arb_seen)
        in_before = self.in_seen['source'] + self.in_seen['sink']
        sent_keys = []
        test_stats = {
            'success_rate': 0.0,
            'packets_sent': 0,
            'packets_received': 0,
            'errors': []
        }

        for i in range(count):
            # Create test packet - only use available protocols (AXI, AXIS, ARB)
            protocol = random.choice([ProtocolType.PROTOCOL_AXI, ProtocolType.PROTOCOL_AXIS, ProtocolType.PROTOCOL_CORE])
            pkt_type = random.choice([PktType.PktTypeError, PktType.PktTypeCompletion, PktType.PktTypePerf])

            # Use only ARB event codes since those are the only ones we have
            if protocol == ProtocolType.PROTOCOL_CORE:
                if pkt_type == PktType.PktTypeError:
                    event_code = ARBErrorCode.ARB_ERR_STARVATION.value
                elif pkt_type == PktType.PktTypeCompletion:
                    event_code = ARBCompletionCode.ARB_COMPL_GRANT_ISSUED.value
                else:
                    event_code = ARBDebugCode.ARB_DEBUG_STATE_CHANGE.value
            else:
                event_code = 0  # Generic event code for non-ARB protocols

            packet_dict = self.create_monbus_packet_dict(
                protocol=protocol,
                pkt_type=pkt_type,
                event_code=event_code,
                channel_id=i % 32,
                agent_id=0x10 + (i % 16),
                data=0x12345678 + i
            )

            # Send via source or sink randomly
            if random.choice([True, False]):
                success = await self.send_source_packet(packet_dict)
            else:
                success = await self.send_sink_packet(packet_dict)

            if success:
                success_count += 1
                test_stats['packets_sent'] += 1
                sent_keys.append(self._key(packet_dict))
                self.stats['protocol_stats'][protocol.name][pkt_type.name] += 1

            # Add some delay between packets
            await self.wait_clocks(self.clk_name, random.randint(1, 5))

        # let the BFM pipelines finish their last handshake before counting
        for _ in range(200):
            await self.wait_clocks(self.clk_name, 1)
            if not self.source_monbus_master.transfer_busy and not self.sink_monbus_master.transfer_busy:
                break
        # Packets the DUT has accepted can still sit in its input skids while the
        # arbiter is held off by a backed-up write path (3 AXIL beats per packet
        # behind a BFM with delays), so wait for the arbiter to catch up with the
        # input count rather than a fixed 60 cycles (96 packets at 'full' left 5
        # behind -- regression 2026-09-27).
        accepted = self.in_seen['source'] + self.in_seen['sink'] - in_before   # DUT input handshakes
        for _ in range(40 * count + 500):
            if len(self.arb_seen) - arb_start >= accepted:
                break
            await self.wait_clocks(self.clk_name, 1)
        await self.wait_clocks(self.clk_name, 60)
        arrived = len(self.arb_seen) - arb_start
        accepted = self.in_seen['source'] + self.in_seen['sink'] - in_before
        test_stats['success_rate'] = success_count / total_count if total_count > 0 else 0.0
        test_stats['packets_received'] = arrived
        test_stats['packets_accepted'] = accepted
        if arrived != accepted:
            test_stats['errors'].append(f"arbiter passed {arrived} packets, the DUT accepted {accepted} at its inputs")
        if accepted != success_count:
            test_stats['errors'].append(f"DUT accepted {accepted} packets, the BFMs report {success_count} sent")
        if self._arb_keys(arb_start) != sorted(sent_keys):
            from collections import Counter
            missing = Counter(sent_keys) - Counter(self._arb_keys(arb_start))
            extra = Counter(self._arb_keys(arb_start)) - Counter(sent_keys)
            test_stats['errors'].append(f"arbiter output (protocol, type) multiset differs from what was sent: "
                                        f"missing {dict(missing)}, extra {dict(extra)}")
        for e in test_stats['errors']:
            self.log.error(e)

        return test_stats['success_rate'] > 0.9 and not test_stats['errors'], test_stats

    async def test_error_fifo_functionality(self, count: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """Test error FIFO functionality via AXI-Lite slave read"""
        self.log.info(f"Testing error FIFO functionality with {count} error packets...")

        # Configure to route ERROR packets to error FIFO
        await self.configure_protocol_filtering(
            ProtocolType.PROTOCOL_AXI,
            pkt_mask=0x0000,  # Don't drop any packets
            err_select=0x0001  # Route ERROR packets (bit 0) to error FIFO
        )

        # Send error packets
        error_packets_sent = 0
        self.expected_error_packets.clear()
        # Drain whatever an earlier phase left in the error FIFO so the records
        # read below are exactly the ones injected here.
        stale = 0
        while int(self.dut.irq_out.value) == 1 and stale < 3 * 64:
            await self.read_error_fifo()
            stale += 1
        if stale:
            self.log.info(f"drained {stale} stale slices from the error FIFO before the test")
        for i in range(count):
            packet_dict = self.create_monbus_packet_dict(
                protocol=ProtocolType.PROTOCOL_AXI,
                pkt_type=PktType.PktTypeError,
                event_code=0x1,
                channel_id=i,
                data=0x1000 + i
            )

            success = await self.send_source_packet(packet_dict)
            if success:
                error_packets_sent += 1
                self.expected_error_packets.append(packet_dict)

            await self.wait_clocks(self.clk_name, 2)

        # Wait for packets to propagate through arbitration and filtering
        await self.wait_clocks(self.clk_name, 50)

        # Check FIFO status before attempting reads
        status = await self.check_error_fifo_status()
        self.log.info(f"Error FIFO status after sending packets: {status}")

        if status['empty']:
            self.log.error("ERROR: FIFO is empty after sending packets - filtering may not be working!")
            # Debug: Check internal filtering signals. arb_monbus_valid
            # lives on the wrapper (post-arbiter); pkt_to_err_fifo and
            # err_fifo_wr_valid are filter-stage signals inside
            # monbus_group_core, i.e. dut -> u_group -> u_core. These are
            # best-effort only: as internal continuous assigns they may be
            # optimized away by the simulator, so never let a missing probe
            # mask the actual failure being reported here.
            self.log.error(f"Debug - arb_monbus_valid: {int(self.dut.arb_monbus_valid.value)}")
            for sig in ('pkt_to_err_fifo', 'err_fifo_wr_valid'):
                try:
                    val = int(getattr(self.dut.u_group.u_core, sig).value)
                    self.log.error(f"Debug - {sig}: {val}")
                except Exception as e:  # probe not present in this build
                    self.log.error(f"Debug - {sig}: unavailable ({e})")

        # Wait for interrupt to assert if FIFO has data
        if not status['empty'] and status['irq_out']:
            self.log.info("✅ Interrupt asserted, FIFO has data")
        elif not status['empty']:
            self.log.warning("FIFO has data but interrupt not asserted")

        # Try to read from error FIFO
        # Each record drains as three 64-bit slices in order {tag,ts},
        # packet[127:64], packet[63:0] (monbus_axil4_axil4_group.sv). Rebuild the
        # packet and compare it, field by field, with what was injected.
        from TBClasses.monbus import parse
        error_packets_read = 0
        mismatches = []
        for i in range(min(error_packets_sent, status['count'])):
            slices = []
            for _ in range(3):
                data = await self.read_error_fifo()
                slices.append(0 if data is None else int(data))
                await self.wait_clocks(self.clk_name, 1)
            raw = (slices[1] << 64) | slices[2]
            pkt = parse(raw)
            if i < 2:
                arb_raw = [hex(q.raw_packet) for q in self.arb_seen[-error_packets_sent:]][:2]
                self.log.info(f"record {i} slices: {[hex(x) for x in slices]}; record raw {hex(raw)}; arbiter raw {arb_raw}")
            error_packets_read += 1
            self.received_error_packets.append(raw)
            exp = self.expected_error_packets.popleft() if self.expected_error_packets else None
            if exp is None:
                mismatches.append(f"record {i}: nothing expected")
                continue
            got = (pkt.protocol, pkt.packet_type, pkt.event_code, pkt.channel_id, pkt.event_data)
            want = (int(exp['protocol']), int(exp['pkt_type']), int(exp['event_code']), int(exp['channel_id']), int(exp['data']))
            if got != want:
                mismatches.append(f"record {i}: got (proto,type,event,ch,data)={got}, expected {want}")
            await self.wait_clocks(self.clk_name, 1)
        if status['count'] != error_packets_sent:
            mismatches.append(f"err_fifo_count {status['count']} after sending {error_packets_sent} error packets")
        for m in mismatches[:8]:
            self.log.error(m)

        test_stats = {
            'packets_sent': error_packets_sent,
            'packets_read': error_packets_read,
            'fifo_count': status['count'],
            'mismatches': len(mismatches),
            'success_rate': 1.0 if (error_packets_read == error_packets_sent and not mismatches) else 0.0
        }

        return test_stats['success_rate'] > 0.5, test_stats

    async def test_master_write_functionality(self, count: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test master write functionality"""
        self.log.info(f"Testing master write functionality with {count} packets...")

        # Configure to route COMPLETION packets to master write
        await self.configure_protocol_filtering(
            ProtocolType.PROTOCOL_CORE,
            pkt_mask=0x0000,  # Don't drop any packets
            err_select=0x0000  # Don't route to error FIFO (will go to write FIFO)
        )

        # Set up slave to receive master writes
        write_count = 0
        expected_writes = count
        self.expected_write_packets.clear()   # per-call accounting (the stress test calls this repeatedly)
        arb_start, aw_start, w_start = len(self.arb_seen), len(self.aw_seen), len(self.w_seen)

        # Send packets that should trigger master writes
        for i in range(count):
            packet_dict = self.create_monbus_packet_dict(
                protocol=ProtocolType.PROTOCOL_CORE,
                pkt_type=PktType.PktTypeCompletion,
                event_code=ARBCompletionCode.ARB_COMPL_GRANT_ISSUED.value,
                channel_id=i,
                data=0x2000 + i
            )

            success = await self.send_sink_packet(packet_dict)
            if success:
                self.expected_write_packets.append(packet_dict)

            await self.wait_clocks(self.clk_name, 3)

        # Wait for master writes to complete
        await self.wait_clocks(self.clk_name, 50)

        # The master-write slave BFM saw the writes, or it did not. Wait for the
        # write path to drain (one AXIL beat per record slice, three per packet)
        # before counting -- a fixed 150-cycle wait cut the tail off at FULL depth.
        for _ in range(4000):
            await self.wait_clocks(self.clk_name, 1)
            if int(self.dut.write_fifo_count.value) == 0 and len(self.aw_seen) - aw_start == len(self.w_seen) - w_start \
                    and len(self.w_seen) - w_start >= 3 * len(self.expected_write_packets):
                break
        await self.wait_clocks(self.clk_name, 20)
        accepted = len(self.expected_write_packets)
        arrived = len(self.arb_seen) - arb_start
        aw = len(self.aw_seen) - aw_start
        w = len(self.w_seen) - w_start
        write_count = aw
        test_stats = {
            'expected_writes': expected_writes,
            'accepted': accepted,
            'arbiter_passed': arrived,
            'm_axil_aw': aw,
            'm_axil_w_beats': w,
            'write_fifo_count_after': int(self.dut.write_fifo_count.value),
            'completed_writes': write_count,
            'success_rate': 1.0 if (aw > 0 and arrived == accepted and w == aw and w == 3 * accepted) else 0.0,
        }
        self.log.info(f"master write stats: {test_stats}, err_fifo_count={int(self.dut.err_fifo_count.value)}")
        if arrived != accepted:
            self.log.error(f"master write: arbiter passed {arrived} of {accepted} accepted packets")
        if aw == 0:
            self.log.error("master write: no AW ever reached the m_axil slave -- the write path emitted nothing")
        if w != aw or w != 3 * accepted:
            self.log.error(f"master write: {aw} AW / {w} W beats for {accepted} packets (expected {3 * accepted} of each, one slice per beat)")

        return test_stats['success_rate'] > 0.5, test_stats

    async def test_protocol_filtering(self) -> Tuple[bool, Dict[str, Any]]:
        """Test protocol-specific packet filtering"""
        self.log.info("Testing protocol-specific packet filtering...")

        test_results = {}
        failures = []
        protocols = [ProtocolType.PROTOCOL_AXI, ProtocolType.PROTOCOL_AXIS, ProtocolType.PROTOCOL_CORE]

        for protocol in protocols:
            # Test dropping packets
            await self.configure_protocol_filtering(
                protocol,
                pkt_mask=0xFFFF,  # Drop all packet types
                err_select=0x0000
            )

            # Send packets that should be dropped
            await self.wait_clocks(self.clk_name, 5)
            arb_start, aw_start = len(self.arb_seen), len(self.aw_seen)
            err_before, wr_before = int(self.dut.err_fifo_count.value), int(self.dut.write_fifo_count.value)
            dropped_count = 0
            for i in range(8):
                packet_dict = self.create_monbus_packet_dict(
                    protocol=protocol,
                    pkt_type=PktType.PktTypeDebug,
                    event_code=0x0,
                    data=0x3000 + i
                )

                success = await self.send_source_packet(packet_dict)
                if success:
                    dropped_count += 1

                await self.wait_clocks(self.clk_name, 2)

            test_results[protocol.name] = {
                'packets_sent': dropped_count,
                'expected_dropped': dropped_count
            }
            await self.wait_clocks(self.clk_name, 20)
            arrived = len(self.arb_seen) - arb_start
            err_delta = int(self.dut.err_fifo_count.value) - err_before
            wr_delta = int(self.dut.write_fifo_count.value) - wr_before
            aw_delta = len(self.aw_seen) - aw_start
            test_results[protocol.name].update({'arbiter_passed': arrived, 'err_fifo_delta': err_delta,
                                                'write_fifo_delta': wr_delta, 'm_axil_aw_delta': aw_delta})
            if arrived != dropped_count:
                failures.append(f"{protocol.name}: {arrived} of {dropped_count} packets reached the arbiter")
            if err_delta or wr_delta or aw_delta:
                failures.append(f"{protocol.name}: masked packets still landed (err +{err_delta}, write +{wr_delta}, AW +{aw_delta})")
            # restore this protocol's default: accept everything, errors to the error FIFO
            await self.configure_protocol_filtering(protocol, pkt_mask=0x0000, err_select=0x0001)

        for f in failures:
            self.log.error(f)
        test_results['failures'] = failures

        return not failures, test_results

    async def test_concurrent_packet_streams(self, duration_cycles: int = 200) -> Tuple[bool, Dict[str, Any]]:
        """Test concurrent packet streams from source and sink"""
        self.log.info(f"Testing concurrent packet streams for {duration_cycles} cycles...")

        for proto in (ProtocolType.PROTOCOL_AXI, ProtocolType.PROTOCOL_AXIS):
            await self.configure_protocol_filtering(proto, pkt_mask=0x0000, err_select=0x0000)
        await self.wait_clocks(self.clk_name, 5)
        arb_start = len(self.arb_seen)
        in_before = dict(self.in_seen)
        src_before, snk_before = self.stats['packets_sent']['source'], self.stats['packets_sent']['sink']

        # Start concurrent packet injection using CocoTB's event loop
        source_task = cocotb.start_soon(self._inject_source_packets(duration_cycles // 2))
        sink_task = cocotb.start_soon(self._inject_sink_packets(duration_cycles // 2))

        # Wait for both streams to complete using CocoTB's Combine
        await Combine(source_task, sink_task)

        # Wait for all packets to propagate
        await self.wait_clocks(self.clk_name, 50)

        await self.wait_clocks(self.clk_name, 200)
        n_src = self.in_seen['source'] - in_before['source']     # accepted by the DUT, not just queued in the BFM
        n_snk = self.in_seen['sink'] - in_before['sink']
        # Same drain rule as test_basic_packet_flow: the arbiter can still be
        # held off by the write path after the last input handshake, so wait
        # for it to catch up with the accepted count before comparing (199 of
        # 200 on one seed of the 2026-09-27 confirming regression).
        for _ in range(40 * duration_cycles + 500):
            if len(self.arb_seen) - arb_start >= n_src + n_snk:
                break
            await self.wait_clocks(self.clk_name, 1)
        await self.wait_clocks(self.clk_name, 60)
        arrived = self.arb_seen[arb_start:]
        got_axi = sum(1 for q in arrived if q.protocol == ProtocolType.PROTOCOL_AXI.value)
        got_axis = sum(1 for q in arrived if q.protocol == ProtocolType.PROTOCOL_AXIS.value)
        errors = []
        if len(arrived) != n_src + n_snk:
            errors.append(f"arbiter passed {len(arrived)} packets, {n_src + n_snk} were sent")
        if got_axi != n_src or got_axis != n_snk:
            errors.append(f"arbiter output has {got_axi} AXI / {got_axis} AXIS packets, sent {n_src} / {n_snk}")
        for e in errors:
            self.log.error(e)
        test_stats = {
            'source_packets': n_src,
            'sink_packets': n_snk,
            'total_packets': n_src + n_snk,
            'arbiter_passed': len(arrived),
            'success_rate': 1.0 if not errors else 0.0,
        }

        return not errors, test_stats

    async def _inject_source_packets(self, count: int):
        """Helper to inject source packets"""
        for i in range(count):
            packet_dict = self.create_monbus_packet_dict(
                protocol=ProtocolType.PROTOCOL_AXI,
                pkt_type=PktType.PktTypePerf,
                event_code=0x0,
                channel_id=i % 16,
                data=0x4000 + i
            )
            await self.send_source_packet(packet_dict)
            await self.wait_clocks(self.clk_name, random.randint(1, 4))

    async def _inject_sink_packets(self, count: int):
        """Helper to inject sink packets"""
        for i in range(count):
            packet_dict = self.create_monbus_packet_dict(
                protocol=ProtocolType.PROTOCOL_AXIS,
                pkt_type=PktType.PktTypeThreshold,
                event_code=0x0,
                channel_id=i % 16,
                data=0x5000 + i
            )
            await self.send_sink_packet(packet_dict)
            await self.wait_clocks(self.clk_name, random.randint(1, 4))

    async def stress_test(self, iterations: int = 100) -> Tuple[bool, Dict[str, Any]]:
        """Run stress test with mixed operations"""
        self.log.info(f"Running stress test with {iterations} iterations...")

        self.set_timing_profile('stress')
        stress_stats = {
            'iterations': iterations,
            'successful_ops': 0,
            'failed_ops': 0,
            'total_packets': 0,
            'success_rate': 0.0
        }

        for i in range(iterations):
            # Mix of different operations
            operation = random.choice(['basic_flow', 'error_fifo', 'master_write', 'filtering'])

            try:
                if operation == 'basic_flow':
                    success, _ = await self.test_basic_packet_flow(count=8)
                elif operation == 'error_fifo':
                    success, _ = await self.test_error_fifo_functionality(count=4)
                elif operation == 'master_write':
                    success, _ = await self.test_master_write_functionality(count=4)
                else:  # filtering
                    success, _ = await self.test_protocol_filtering()

                if success:
                    stress_stats['successful_ops'] += 1
                else:
                    stress_stats['failed_ops'] += 1

            except Exception as e:
                self.log.warning(f"Stress test iteration {i} failed: {e}")
                stress_stats['failed_ops'] += 1

            # Brief pause between iterations
            await self.wait_clocks(self.clk_name, random.randint(5, 15))

        stress_stats['total_packets'] = self.stats['packets_sent']['source'] + self.stats['packets_sent']['sink']
        stress_stats['success_rate'] = stress_stats['successful_ops'] / iterations if iterations > 0 else 0.0

        return stress_stats['success_rate'] > 0.7, stress_stats

    def finalize_test(self):
        """Finalize test and collect final statistics"""
        self.stats['test_end_time'] = time.time()
        test_duration = self.stats['test_end_time'] - self.stats['test_start_time']

        self.log.info("="*60)
        self.log.info("MONBUS AXIL GROUP TEST FINAL STATISTICS")
        self.log.info("="*60)
        self.log.info(f"Test duration: {test_duration:.2f} seconds")
        self.log.info(f"Source packets sent: {self.stats['packets_sent']['source']}")
        self.log.info(f"Sink packets sent: {self.stats['packets_sent']['sink']}")
        self.log.info(f"Total packets sent: {self.stats['packets_sent']['source'] + self.stats['packets_sent']['sink']}")
        self.log.info(f"Error FIFO reads: {self.stats['error_fifo_reads']}")
        self.log.info(f"Master writes: {self.stats['master_writes']}")
        self.log.info(f"Config operations: {self.stats['config_operations']}")

        # Protocol breakdown
        self.log.info("\nProtocol Statistics:")
        for protocol, types in self.stats['protocol_stats'].items():
            self.log.info(f"  {protocol}:")
            for pkt_type, count in types.items():
                self.log.info(f"    {pkt_type}: {count}")

        # Filtering statistics
        filtering = self.stats['packets_filtered']
        self.log.info(f"\nFiltering Statistics:")
        self.log.info(f"  Dropped: {filtering['dropped']}")
        self.log.info(f"  To Error FIFO: {filtering['to_err_fifo']}")
        self.log.info(f"  To Write FIFO: {filtering['to_write_fifo']}")

    def get_test_stats(self) -> Dict[str, Any]:
        """Get comprehensive test statistics"""
        return {
            'summary': {
                'total_packets_sent': self.stats['packets_sent']['source'] + self.stats['packets_sent']['sink'],
                'source_packets': self.stats['packets_sent']['source'],
                'sink_packets': self.stats['packets_sent']['sink'],
                'error_fifo_reads': self.stats['error_fifo_reads'],
                'master_writes': self.stats['master_writes'],
                'config_operations': self.stats['config_operations']
            },
            'filtering': self.stats['packets_filtered'],
            'protocols': dict(self.stats['protocol_stats']),
            'timing': {
                'test_duration': self.stats['test_end_time'] - self.stats['test_start_time'],
                'current_profile': self.current_timing
            }
        }
