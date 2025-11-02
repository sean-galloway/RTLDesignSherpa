# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: NETWORK_PKT_TYPES
# Purpose: Network Interface Classes
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Network Interface Classes

Provides Network Master and Slave interfaces that follow the same patterns as AXIL4 interfaces,
built on the GAXI framework for robust packet handling and flow control.

Features:
- Network Master for packet transmission with credit management
- Network Slave for packet reception with ACK generation
- Enhanced chunk-based routing with v2.0 chunk_enables support
- Comprehensive EOS (End of Stream) tracking
- Built-in compliance checking
- Transaction-level APIs for easy testing

Usage:
    # Create Network Master
    master = MNOCMaster(dut, clock, prefix="m_network_", log=log)
    await master.send_packet(channel=5, data=packet_data, packet_type=NETWORK_PKT_TYPES.TS_PKT)

    # Create Network Slave
    slave = MNOCSlave(dut, clock, prefix="s_network_", log=log)
    packet = await slave.receive_packet()
"""

import asyncio
from typing import List, Dict, Any, Optional, Union, Tuple
from enum import IntEnum

from cocotb.triggers import RisingEdge, Timer
import cocotb

# Import GAXI components and framework
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.network.network_field_configs import MNOCFieldConfigHelper
from CocoTBFramework.components.network.network_packet import MNOCPacket
from CocoTBFramework.components.network.network_compliance_checker import MNOCComplianceChecker


class NETWORK_PKT_TYPES(IntEnum):
    """Network Packet Types as defined in specification"""
    CONFIG_PKT = 0  # Configuration packet for FC/RISC-V configuration
    TS_PKT = 1      # TruStream data packet for core communication
    RDA_PKT = 2     # RISC-V Direct Access packet for memory access
    RAW_PKT = 3     # Raw 512-bit data packet


class NETWORK_ACK_TYPES(IntEnum):
    """Network Acknowledgment Types"""
    MSAP_STOP = 0           # Packet received by MSAP, increment credit by 1
    MSAP_START = 1          # Starts a channel and sets credit to 8
    MSAP_CREDIT_ON = 2      # Packet received by RAPIDS, increment credit by 1
    MSAP_STOP_AT_EOS = 3    # Stop at end of stream


class MNOCMaster:
    """
    Network Master Interface - Packet Transmission with Credit Management

    Features:
    - Credit-based flow control with configurable limits
    - Enhanced chunk-based packet generation with v2.0 chunk_enables
    - Comprehensive EOS (End of Stream) support
    - Timeout mechanisms with configurable thresholds
    - Transaction-level APIs for easy testing

    API Methods:
    - send_packet() - High-level packet transmission
    - send_config_packet() - Configuration packet transmission
    - send_ts_packet() - TruStream packet transmission
    - send_rda_packet() - RDA packet transmission
    - send_raw_packet() - Raw data packet transmission
    """

    def __init__(self, dut, clock, prefix="", log=None, **kwargs):
        """Initialize Network Master interface with automatic compliance checking."""
        self.clock = clock
        self.log = log

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 512)
        self.addr_width = kwargs.get('addr_width', 8)
        self.num_channels = kwargs.get('num_channels', 32)
        self.initial_credits = kwargs.get('initial_credits', 4)
        self.multi_sig = kwargs.get('multi_sig', False)

        # Network Packet Interface (network_data) - Master drives
        self.packet_channel = GAXIMaster(
            dut=dut,
            title="NETWORK_Master",
            prefix=prefix,
            clock=clock,
            field_config=MNOCFieldConfigHelper.create_packet_field_config(
                self.data_width, self.addr_width
            ),
            pkt_prefix="network_pkt",
            multi_sig=self.multi_sig,
            log=log
        )

        # Network ACK Interface (network_ack) - Slave receives ACKs
        self.ack_channel = GAXISlave(
            dut=dut,
            title="ACK_Slave",
            prefix=prefix,
            clock=clock,
            field_config=MNOCFieldConfigHelper.create_ack_field_config(
                self.addr_width
            ),
            pkt_prefix="network_ack",
            multi_sig=self.multi_sig,
            log=log
        )

        # Store parameters for transaction methods
        self.timeout_cycles = kwargs.get('timeout_cycles', 1000)

        # Credit management per channel
        self.channel_credits = {i: self.initial_credits for i in range(self.num_channels)}
        self.packets_sent = {i: 0 for i in range(self.num_channels)}
        self.acks_received = {i: 0 for i in range(self.num_channels)}

        # Enhanced compliance checker integration
        self.compliance_checker = MNOCComplianceChecker.create_if_enabled(
            dut=dut,
            clock=clock,
            prefix=prefix,
            log=log,
            data_width=self.data_width,
            addr_width=self.addr_width,
            multi_sig=self.multi_sig,
            mode='master'
        )

        if self.compliance_checker and log:
            log.info("MNOCMaster: Compliance checking enabled")

        # Start ACK processing task
        if hasattr(cocotb, 'start_soon'):
            cocotb.start_soon(self._process_acks())
        else:
            cocotb.fork(self._process_acks())

    async def send_packet(self, channel: int, data: Union[int, List[int]],
                        packet_type: NETWORK_PKT_TYPES, chunk_enables: int = 0xFFFF,
                        eos: bool = False, **kwargs) -> None:
        """
        High-level packet transmission with credit management.

        Args:
            channel: Target channel ID (0 to num_channels-1)
            data: Packet data (int for single value, list for multi-field)
            packet_type: Network packet type (CONFIG_PKT, TS_PKT, RDA_PKT, RAW_PKT)
            chunk_enables: v2.0 chunk validity enables (16-bit, default all valid)
            eos: End of stream marker
            **kwargs: Additional packet fields
        """
        if self.log:
            self.log.debug(f"MNOCMaster: Sending packet ch={channel} type={packet_type.name} eos={eos}")

        # Check credit availability
        if not self._has_credits(channel):
            if self.log:
                self.log.warning(f"MNOCMaster: No credits available for channel {channel}")
            raise RuntimeError(f"No credits available for channel {channel}")

        # Create packet based on type
        if packet_type == NETWORK_PKT_TYPES.RAW_PKT:
            packet = self._create_raw_packet(channel, data, eos, **kwargs)
        else:
            packet = self._create_structured_packet(channel, data, packet_type,
                                                chunk_enables, eos, **kwargs)

        # Send packet
        await self.packet_channel.send(packet)

        # Update credit tracking
        self.packets_sent[channel] += 1

        if self.log:
            remaining_credits = self._get_remaining_credits(channel)
            self.log.debug(f"MNOCMaster: Packet sent, remaining credits: {remaining_credits}")

    async def send_config_packet(self, channel: int, config_data: List[int],
                                chunk_enables: int = 0xFFFF, eos: bool = False) -> None:
        """Send configuration packet for FC/RISC-V configuration."""
        await self.send_packet(channel, config_data, NETWORK_PKT_TYPES.CONFIG_PKT,
                            chunk_enables, eos)

    async def send_ts_packet(self, channel: int, ts_data: List[int],
                            chunk_enables: int = 0xFFFF, eos: bool = False) -> None:
        """Send TruStream data packet for core communication."""
        await self.send_packet(channel, ts_data, NETWORK_PKT_TYPES.TS_PKT,
                            chunk_enables, eos)

    async def send_rda_packet(self, channel: int, rda_data: List[int],
                            chunk_enables: int = 0xFFFF, eos: bool = False) -> None:
        """Send RISC-V Direct Access packet for memory access."""
        await self.send_packet(channel, rda_data, NETWORK_PKT_TYPES.RDA_PKT,
                            chunk_enables, eos)

    async def send_raw_packet(self, channel: int, raw_data: int, eos: bool = False) -> None:
        """Send raw 512-bit data packet."""
        await self.send_packet(channel, raw_data, NETWORK_PKT_TYPES.RAW_PKT,
                            0xFFFF, eos)

    def _create_structured_packet(self, channel: int, data: Union[int, List[int]],
                                packet_type: NETWORK_PKT_TYPES, chunk_enables: int,
                                eos: bool, **kwargs) -> MNOCPacket:
        """Create structured packet (CONFIG, TS, RDA) with v2.0 format."""
        # Ensure data is a list of 15 32-bit fields
        if isinstance(data, int):
            data_fields = [data] + [0] * 14  # Single value + 14 zeros
        else:
            data_fields = list(data) + [0] * (15 - len(data))  # Pad to 15 fields
            data_fields = data_fields[:15]  # Truncate if too long

        # Create packet with v2.0 structure
        packet = self.packet_channel.create_packet(
            # Header fields
            addr=channel,
            # Payload type
            payload_type=packet_type.value,
            # Data fields (15 x 32-bit)
            **{f'data_{i}': data_fields[i] for i in range(15)},
            # Control flags (15 bits, one per data field)
            ctrl=kwargs.get('ctrl', 0x7FFF),  # Default: all control bits set
            # v2.0 chunk enables (16 bits)
            chunk_enables=chunk_enables,
            # Reserved bit
            reserved=0,
            # EOS marker
            eos=eos,
            # Additional fields
            **kwargs
        )

        return packet

    def _create_raw_packet(self, channel: int, data: int, eos: bool, **kwargs) -> MNOCPacket:
        """Create RAW packet with full 512-bit payload."""
        packet = self.packet_channel.create_packet(
            # Header fields
            addr=channel,
            # Payload type
            payload_type=NETWORK_PKT_TYPES.RAW_PKT.value,
            # Raw data (full 512 bits)
            raw_data=data,
            # EOS marker
            eos=eos,
            # Additional fields
            **kwargs
        )

        return packet

    def _has_credits(self, channel: int) -> bool:
        """Check if channel has available credits."""
        return self._get_remaining_credits(channel) > 0

    def _get_remaining_credits(self, channel: int) -> int:
        """Get remaining credits for channel."""
        return self.initial_credits - (self.packets_sent[channel] - self.acks_received[channel])

    async def _process_acks(self):
        """Background task to process incoming ACKs and update credits."""
        while True:
            try:
                # Wait for ACK packet
                if len(self.ack_channel._recvQ) > 0:
                    ack_packet = self.ack_channel._recvQ.pop(0)

                    # Extract ACK information
                    channel = getattr(ack_packet, 'addr', 0)
                    ack_type = getattr(ack_packet, 'ack', 0)

                    # Update credits based on ACK type
                    if ack_type == NETWORK_ACK_TYPES.MSAP_STOP:
                        self.acks_received[channel] += 1
                    elif ack_type == NETWORK_ACK_TYPES.MSAP_START:
                        # Channel start - reset credits to 8
                        self.acks_received[channel] = self.packets_sent[channel] - 8
                    elif ack_type == NETWORK_ACK_TYPES.MSAP_CREDIT_ON:
                        self.acks_received[channel] += 1

                    if self.log:
                        remaining = self._get_remaining_credits(channel)
                        self.log.debug(f"MNOCMaster: ACK received ch={channel} type={ack_type} remaining={remaining}")

                await RisingEdge(self.clock)

            except Exception as e:
                if self.log:
                    self.log.error(f"MNOCMaster: Error processing ACKs: {e}")
                await Timer(1, units='us')

    def get_compliance_report(self) -> Optional[Dict[str, Any]]:
        """Get compliance report if compliance checking is enabled."""
        if self.compliance_checker:
            return self.compliance_checker.get_compliance_report()
        return None

    def get_credit_status(self) -> Dict[int, Dict[str, int]]:
        """Get current credit status for all channels."""
        return {
            ch: {
                'remaining': self._get_remaining_credits(ch),
                'sent': self.packets_sent[ch],
                'acks': self.acks_received[ch]
            }
            for ch in range(self.num_channels)
        }


class MNOCSlave:
    """
    Network Slave Interface - Packet Reception with ACK Generation
    
    Features:
    - Enhanced chunk-based routing with v2.0 chunk_enables extraction
    - Comprehensive EOS (End of Stream) tracking and propagation  
    - Immediate and credit-based ACK generation
    - Dual-path RDA routing for reads and writes
    - Transaction-level APIs for testing
    
    API Methods:
    - receive_packet() - High-level packet reception
    - send_ack() - Manual ACK generation
    - get_received_packets() - Get all received packets
    - wait_for_packet() - Wait for specific packet type
    """

    def __init__(self, dut, clock, prefix="", log=None, **kwargs):
        """Initialize Network Slave interface with automatic compliance checking."""
        self.dut = dut
        self.clock = clock
        self.log = log

        # Extract configuration parameters
        self.data_width = kwargs.get('data_width', 512)
        self.addr_width = kwargs.get('addr_width', 8)
        self.num_channels = kwargs.get('num_channels', 32)
        self.auto_ack = kwargs.get('auto_ack', True)
        self.multi_sig = kwargs.get('multi_sig', False)
        self.timeout_cycles = kwargs.get('timeout_cycles', 1000)

        # Network Packet Interface (network_pkt) - Slave receives packets
        self.packet_channel = GAXISlave(
            dut=dut,
            title="NETWORK_Slave",
            prefix=prefix,
            clock=clock,
            field_config=MNOCFieldConfigHelper.create_packet_field_config(
                self.data_width, self.addr_width
            ),
            pkt_prefix="network_pkt",
            multi_sig=self.multi_sig,
            log=log,
            **kwargs
        )

        # Network ACK Interface (network_ack) - Master sends ACKs
        self.ack_channel = GAXIMaster(
            dut=dut,
            title="ACK_Master", 
            prefix=prefix,
            clock=clock,
            field_config=MNOCFieldConfigHelper.create_ack_field_config(
                self.addr_width
            ),
            pkt_prefix="network_ack",
            multi_sig=self.multi_sig,
            log=log,
            **kwargs
        )

        # Packet storage and statistics
        self.received_packets = []
        self.packet_stats = {pkt_type: 0 for pkt_type in NETWORK_PKT_TYPES}

        # Enhanced compliance checker integration
        self.compliance_checker = MNOCComplianceChecker.create_if_enabled(
            dut=dut,
            clock=clock,
            prefix=prefix,
            log=log,
            data_width=self.data_width,
            addr_width=self.addr_width,
            multi_sig=self.multi_sig,
            mode='slave'
        )
        
        if self.compliance_checker and log:
            log.info("MNOCSlave: Compliance checking enabled")

        # Start packet processing task
        if hasattr(cocotb, 'start_soon'):
            cocotb.start_soon(self._process_packets())
        else:
            cocotb.fork(self._process_packets())

        if log:
            log.info(f"MNOCSlave: Initialized with {self.num_channels} channels, "
                    f"auto_ack={self.auto_ack}, data_width={self.data_width}")

    async def receive_packet(self, timeout_cycles: Optional[int] = None) -> MNOCPacket:
        """
        Receive the next Network packet.
        
        Args:
            timeout_cycles: Optional timeout override
            
        Returns:
            Received Network packet
            
        Raises:
            TimeoutError: If no packet received within timeout
        """
        timeout = timeout_cycles or self.timeout_cycles
        initial_count = len(self.received_packets)
        cycles_waited = 0

        while len(self.received_packets) <= initial_count:
            await RisingEdge(self.clock)
            cycles_waited += 1

            if cycles_waited > timeout:
                raise TimeoutError(f"Network packet timeout after {cycles_waited} cycles")

        packet = self.received_packets[initial_count]
        
        if self.log:
            packet_type = NETWORK_PKT_TYPES(getattr(packet, 'payload_type', 0))
            channel = getattr(packet, 'addr', 0)
            eos = getattr(packet, 'eos', False)
            self.log.debug(f"MNOCSlave: Received packet ch={channel} type={packet_type.name} eos={eos}")

        return packet

    async def wait_for_packet(self, packet_type: NETWORK_PKT_TYPES, 
                            channel: Optional[int] = None,
                            timeout_cycles: Optional[int] = None) -> MNOCPacket:
        """
        Wait for specific packet type and channel.
        
        Args:
            packet_type: Expected packet type
            channel: Expected channel (None for any channel)
            timeout_cycles: Optional timeout override
            
        Returns:
            Matching Network packet
        """
        timeout = timeout_cycles or self.timeout_cycles
        cycles_waited = 0

        while cycles_waited < timeout:
            # Check existing packets
            for packet in self.received_packets:
                pkt_type = NETWORK_PKT_TYPES(getattr(packet, 'payload_type', 0))
                pkt_channel = getattr(packet, 'addr', 0)
                
                if (pkt_type == packet_type and 
                    (channel is None or pkt_channel == channel)):
                    return packet
            
            await RisingEdge(self.clock)
            cycles_waited += 1

        raise TimeoutError(f"Timeout waiting for {packet_type.name} packet")

    async def send_ack(self, channel: int, ack_type: NETWORK_ACK_TYPES) -> None:
        """
        Manually send ACK packet.
        
        Args:
            channel: Target channel
            ack_type: Type of acknowledgment
        """
        if self.log:
            self.log.debug(f"MNOCSlave: Sending ACK ch={channel} type={ack_type.name}")

        # Create ACK packet using GAXI master
        ack_packet = await self.ack_channel.create_packet()
        ack_packet.addr = channel
        ack_packet.ack = ack_type.value
        
        # Calculate parity (odd parity of address)
        ack_packet.addr_par = bin(channel).count('1') % 2
        
        # Calculate ACK parity (odd parity of ack field)
        ack_packet.par = bin(ack_type.value).count('1') % 2

        await self.ack_channel.send(ack_packet)

    async def _process_packets(self):
        """Background task to process incoming packets and generate ACKs."""
        while True:
            try:
                # Check for new packets from GAXI slave
                if hasattr(self.packet_channel, '_recvQ') and len(self.packet_channel._recvQ) > 0:
                    packet = self.packet_channel._recvQ.pop(0)
                    
                    # Store packet
                    self.received_packets.append(packet)
                    
                    # Update statistics
                    packet_type = NETWORK_PKT_TYPES(getattr(packet, 'payload_type', 0))
                    self.packet_stats[packet_type] += 1
                    
                    # Extract packet information
                    channel = getattr(packet, 'addr', 0)
                    eos = getattr(packet, 'eos', False)
                    
                    if self.log:
                        self.log.debug(f"MNOCSlave: Processing packet ch={channel} type={packet_type.name} eos={eos}")
                    
                    # Generate automatic ACK if enabled
                    if self.auto_ack:
                        if eos:
                            ack_type = NETWORK_ACK_TYPES.MSAP_STOP_AT_EOS
                        else:
                            ack_type = NETWORK_ACK_TYPES.MSAP_STOP
                        
                        await self.send_ack(channel, ack_type)
                
                await RisingEdge(self.clock)
                
            except Exception as e:
                if self.log:
                    self.log.error(f"MNOCSlave: Error processing packets: {e}")
                await Timer(1, units='us')

    def get_received_packets(self, packet_type: Optional[NETWORK_PKT_TYPES] = None,
                        channel: Optional[int] = None) -> List[MNOCPacket]:
        """
        Get received packets with optional filtering.
        
        Args:
            packet_type: Filter by packet type (None for all)
            channel: Filter by channel (None for all)
            
        Returns:
            List of matching packets
        """
        packets = self.received_packets
        
        if packet_type is not None:
            packets = [p for p in packets 
                    if NETWORK_PKT_TYPES(getattr(p, 'payload_type', 0)) == packet_type]
        
        if channel is not None:
            packets = [p for p in packets if getattr(p, 'addr', 0) == channel]
            
        return packets

    def get_packet_statistics(self) -> Dict[str, int]:
        """Get packet reception statistics."""
        return {pkt_type.name: count for pkt_type, count in self.packet_stats.items()}

    def clear_received_packets(self):
        """Clear received packet history."""
        self.received_packets.clear()
        self.packet_stats = {pkt_type: 0 for pkt_type in NETWORK_PKT_TYPES}
        
        if self.log:
            self.log.debug("MNOCSlave: Cleared packet history")

    def get_compliance_report(self) -> Optional[Dict[str, Any]]:
        """Get compliance checking report if available."""
        if self.compliance_checker:
            return self.compliance_checker.get_compliance_report()
        return None

    def get_status(self) -> Dict[str, Any]:
        """Get current slave status."""
        return {
            'received_packets': len(self.received_packets),
            'packet_stats': self.get_packet_statistics(),
            'auto_ack': self.auto_ack,
            'num_channels': self.num_channels,
            'data_width': self.data_width,
            'compliance_enabled': self.compliance_checker is not None
        }

    # Convenience methods for specific packet types
    async def wait_for_config_packet(self, channel: Optional[int] = None, 
                                timeout_cycles: Optional[int] = None) -> MNOCPacket:
        """Wait for CONFIG packet."""
        return await self.wait_for_packet(NETWORK_PKT_TYPES.CONFIG_PKT, channel, timeout_cycles)

    async def wait_for_ts_packet(self, channel: Optional[int] = None, 
                            timeout_cycles: Optional[int] = None) -> MNOCPacket:
        """Wait for TS packet."""
        return await self.wait_for_packet(NETWORK_PKT_TYPES.TS_PKT, channel, timeout_cycles)

    async def wait_for_rda_packet(self, channel: Optional[int] = None, 
                                timeout_cycles: Optional[int] = None) -> MNOCPacket:
        """Wait for RDA packet."""
        return await self.wait_for_packet(NETWORK_PKT_TYPES.RDA_PKT, channel, timeout_cycles)

    async def wait_for_raw_packet(self, channel: Optional[int] = None, 
                                timeout_cycles: Optional[int] = None) -> MNOCPacket:
        """Wait for RAW packet."""
        return await self.wait_for_packet(NETWORK_PKT_TYPES.RAW_PKT, channel, timeout_cycles)

    # ACK convenience methods
    async def send_start_ack(self, channel: int) -> None:
        """Send START ACK to begin channel operation."""
        await self.send_ack(channel, NETWORK_ACK_TYPES.MSAP_START)

    async def send_stop_ack(self, channel: int) -> None:
        """Send STOP ACK for normal packet reception."""
        await self.send_ack(channel, NETWORK_ACK_TYPES.MSAP_STOP)

    async def send_credit_ack(self, channel: int) -> None:
        """Send CREDIT ACK to return credit."""
        await self.send_ack(channel, NETWORK_ACK_TYPES.MSAP_CREDIT_ON)

    async def send_stop_at_eos_ack(self, channel: int) -> None:
        """Send STOP_AT_EOS ACK for end-of-stream packets."""
        await self.send_ack(channel, NETWORK_ACK_TYPES.MSAP_STOP_AT_EOS)
