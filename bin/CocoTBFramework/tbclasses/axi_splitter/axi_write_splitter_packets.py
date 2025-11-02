# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SplitWriteTransactionState
# Purpose: Common AXI Write Splitter Packet Definitions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Common AXI Write Splitter Packet Definitions

Shared packet classes based on field configurations that can be used by both
the testbench and scoreboard, eliminating duplicate transaction definitions.

These packets extend GAXIPacket and use the field configurations defined
in the testbench for complete consistency.

Adapted from read splitter packets for write operations, including:
- AXI Write Address (AW) channel packets
- AXI Write Data (W) channel packets
- AXI Write Response (B) channel packets
- Split tracking for write transactions
"""

from typing import Optional, Dict, Any
from dataclasses import dataclass
from enum import Enum
import time

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class SplitWriteTransactionState(Enum):
    """State of a split write transaction"""
    PENDING = "pending"
    ADDRESS_SENT = "address_sent"    # AW sent, waiting for data
    DATA_PARTIAL = "data_partial"    # Some data sent
    DATA_COMPLETE = "data_complete"  # All data sent, waiting for response
    COMPLETE = "complete"            # Response received
    ERROR = "error"


def create_axi_write_address_field_config(id_width: int = 8, addr_width: int = 32, user_width: int = 1) -> FieldConfig:
    """
    Create AXI write address channel (AW) field configuration.

    Args:
        id_width: Transaction ID width
        addr_width: Address width
        user_width: User signal width

    Returns:
        FieldConfig for AXI write address channel
    """
    config = FieldConfig()

    # AXI Write Address Channel fields
    config.add_field(FieldDefinition(
        name="id", bits=id_width, format="hex",
        description="Transaction ID"
    ))
    config.add_field(FieldDefinition(
        name="addr", bits=addr_width, format="hex",
        description="Address"
    ))
    config.add_field(FieldDefinition(
        name="len", bits=8, format="dec",
        description="Burst length (transfers - 1)"
    ))
    config.add_field(FieldDefinition(
        name="size", bits=3, format="dec",
        description="Burst size (bytes per transfer)"
    ))
    config.add_field(FieldDefinition(
        name="burst", bits=2, format="dec",
        description="Burst type",
        encoding={0: "FIXED", 1: "INCR", 2: "WRAP"}
    ))
    config.add_field(FieldDefinition(
        name="lock", bits=1, format="dec",
        description="Lock type"
    ))
    config.add_field(FieldDefinition(
        name="cache", bits=4, format="hex",
        description="Cache control"
    ))
    config.add_field(FieldDefinition(
        name="prot", bits=3, format="hex",
        description="Protection attributes"
    ))
    config.add_field(FieldDefinition(
        name="qos", bits=4, format="dec",
        description="Quality of Service"
    ))
    config.add_field(FieldDefinition(
        name="region", bits=4, format="dec",
        description="Region identifier"
    ))

    if user_width > 0:
        config.add_field(FieldDefinition(
            name="user", bits=user_width, format="hex",
            description="User-defined attributes"
        ))

    return config


def create_axi_write_data_field_config(data_width: int = 32, user_width: int = 1) -> FieldConfig:
    """
    Create AXI write data channel (W) field configuration.

    Args:
        data_width: Data width
        user_width: User signal width

    Returns:
        FieldConfig for AXI write data channel
    """
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="data", bits=data_width, format="hex",
        description="Write data"
    ))
    config.add_field(FieldDefinition(
        name="strb", bits=data_width//8, format="hex",
        description="Write strobes"
    ))
    config.add_field(FieldDefinition(
        name="last", bits=1, format="dec",
        description="Last transfer in burst"
    ))

    if user_width > 0:
        config.add_field(FieldDefinition(
            name="user", bits=user_width, format="hex",
            description="User-defined attributes"
        ))

    return config


def create_axi_write_response_field_config(id_width: int = 8, user_width: int = 1) -> FieldConfig:
    """
    Create AXI write response channel (B) field configuration.

    Args:
        id_width: Transaction ID width
        user_width: User signal width

    Returns:
        FieldConfig for AXI write response channel
    """
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="id", bits=id_width, format="hex",
        description="Transaction ID"
    ))
    config.add_field(FieldDefinition(
        name="resp", bits=2, format="dec",
        description="Response status",
        encoding={0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
    ))

    if user_width > 0:
        config.add_field(FieldDefinition(
            name="user", bits=user_width, format="hex",
            description="User-defined attributes"
        ))

    return config


def create_write_split_info_field_config(id_width: int = 8, addr_width: int = 32) -> FieldConfig:
    """
    Create write split information field configuration.

    Args:
        id_width: Transaction ID width
        addr_width: Address width

    Returns:
        FieldConfig for write split information
    """
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="addr", bits=addr_width, format="hex",
        description="Original address"
    ))
    config.add_field(FieldDefinition(
        name="id", bits=id_width, format="hex",
        description="Original transaction ID"
    ))
    config.add_field(FieldDefinition(
        name="cnt", bits=8, format="dec",
        description="Number of split transactions"
    ))

    return config


class AXIWriteAddressPacket(GAXIPacket):
    """
    AXI Write Address Channel (AW) packet using field configuration.

    Replaces custom AWTransaction class with field-config-based packet.
    """

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        """
        Initialize AXI write address packet.

        Args:
            field_config: Field configuration (will use default if None)
            **kwargs: Initial field values
        """
        if field_config is None:
            field_config = create_axi_write_address_field_config()

        # Add timestamp for tracking
        self.timestamp = kwargs.pop('timestamp', time.time())

        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None) -> 'AXIWriteAddressPacket':
        """Create packet from dictionary data"""
        return cls(field_config=field_config, **data)

    def to_dict(self) -> Dict[str, Any]:
        """Convert packet to dictionary"""
        result = {}
        for field_name in self.field_config.field_names():
            result[field_name] = getattr(self, field_name, 0)
        result['timestamp'] = self.timestamp
        return result

    def get_burst_type_name(self) -> str:
        """Get burst type as string"""
        burst_map = {0: "FIXED", 1: "INCR", 2: "WRAP"}
        return burst_map.get(self.burst, f"UNKNOWN({self.burst})")

    def calculate_total_bytes(self) -> int:
        """Calculate total bytes in this burst"""
        bytes_per_beat = 1 << self.size
        num_beats = self.len + 1
        return bytes_per_beat * num_beats

    def will_cross_boundary(self, boundary_size: int) -> bool:
        """Check if this transaction will cross a boundary"""
        start_addr = self.addr
        total_bytes = self.calculate_total_bytes()
        end_addr = start_addr + total_bytes - 1

        start_boundary = start_addr // boundary_size
        end_boundary = end_addr // boundary_size

        return start_boundary != end_boundary


class AXIWriteDataPacket(GAXIPacket):
    """
    AXI Write Data Channel (W) packet using field configuration.

    Replaces custom WTransaction class with field-config-based packet.
    """

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        """
        Initialize AXI write data packet.

        Args:
            field_config: Field configuration (will use default if None)
            **kwargs: Initial field values
        """
        if field_config is None:
            field_config = create_axi_write_data_field_config()

        # Add timestamp for tracking
        self.timestamp = kwargs.pop('timestamp', time.time())

        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None) -> 'AXIWriteDataPacket':
        """Create packet from dictionary data"""
        return cls(field_config=field_config, **data)

    def to_dict(self) -> Dict[str, Any]:
        """Convert packet to dictionary"""
        result = {}
        for field_name in self.field_config.field_names():
            result[field_name] = getattr(self, field_name, 0)
        result['timestamp'] = self.timestamp
        return result

    def get_strobe_info(self) -> str:
        """Get write strobe information as string"""
        strb_val = getattr(self, 'strb', 0)
        return f"0x{strb_val:X}"

    def is_last_beat(self) -> bool:
        """Check if this is the last beat in the burst"""
        return bool(getattr(self, 'last', 0))


class AXIWriteResponsePacket(GAXIPacket):
    """
    AXI Write Response Channel (B) packet using field configuration.

    Replaces custom BTransaction class with field-config-based packet.
    """

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        """
        Initialize AXI write response packet.

        Args:
            field_config: Field configuration (will use default if None)
            **kwargs: Initial field values
        """
        if field_config is None:
            field_config = create_axi_write_response_field_config()

        # Add timestamp for tracking
        self.timestamp = kwargs.pop('timestamp', time.time())

        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None) -> 'AXIWriteResponsePacket':
        """Create packet from dictionary data"""
        return cls(field_config=field_config, **data)

    def to_dict(self) -> Dict[str, Any]:
        """Convert packet to dictionary"""
        result = {}
        for field_name in self.field_config.field_names():
            result[field_name] = getattr(self, field_name, 0)
        result['timestamp'] = self.timestamp
        return result

    def get_response_name(self) -> str:
        """Get response type as string"""
        resp_map = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        return resp_map.get(self.resp, f"UNKNOWN({self.resp})")

    def is_error_response(self) -> bool:
        """Check if this is an error response"""
        return self.resp in [2, 3]  # SLVERR or DECERR


class WriteSplitInfoPacket(GAXIPacket):
    """
    Write Split Information packet using field configuration.

    Represents information about write transaction splitting.
    """

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        """
        Initialize write split info packet.

        Args:
            field_config: Field configuration (will use default if None)
            **kwargs: Initial field values
        """
        if field_config is None:
            field_config = create_write_split_info_field_config()

        # Add timestamp for tracking
        self.timestamp = kwargs.pop('timestamp', time.time())

        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None) -> 'WriteSplitInfoPacket':
        """Create packet from dictionary data"""
        return cls(field_config=field_config, **data)

    def to_dict(self) -> Dict[str, Any]:
        """Convert packet to dictionary"""
        result = {}
        for field_name in self.field_config.field_names():
            result[field_name] = getattr(self, field_name, 0)
        result['timestamp'] = self.timestamp
        return result


@dataclass
class SplitWriteTransaction:
    """
    Tracks a complete split write transaction using field-config-based packets.

    This replaces the old custom SplitWriteTransaction class and handles
    the more complex write transaction flow with address, data, and response phases.
    """
    original_aw: AXIWriteAddressPacket
    split_info: Optional[WriteSplitInfoPacket]
    split_aws: list[AXIWriteAddressPacket]
    write_data: list[AXIWriteDataPacket]
    received_responses: list[AXIWriteResponsePacket]
    expected_responses: int
    expected_data_beats: int
    state: SplitWriteTransactionState
    start_time: float
    completion_time: Optional[float] = None
    errors: list[str] = None

    def __post_init__(self):
        if self.errors is None:
            self.errors = []
        if self.start_time == 0.0:
            self.start_time = time.time()

    def add_split_aw(self, aw_packet: AXIWriteAddressPacket):
        """Add a split AW transaction"""
        self.split_aws.append(aw_packet)

    def add_write_data(self, w_packet: AXIWriteDataPacket):
        """Add a write data packet"""
        self.write_data.append(w_packet)

        # Update state based on data completion
        if w_packet.is_last_beat() and len(self.write_data) >= self.expected_data_beats:
            if self.state in [SplitWriteTransactionState.ADDRESS_SENT, SplitWriteTransactionState.DATA_PARTIAL]:
                self.state = SplitWriteTransactionState.DATA_COMPLETE
        elif len(self.write_data) > 0:
            if self.state == SplitWriteTransactionState.ADDRESS_SENT:
                self.state = SplitWriteTransactionState.DATA_PARTIAL

    def add_response(self, b_packet: AXIWriteResponsePacket):
        """Add a response packet"""
        self.received_responses.append(b_packet)

        # Update state based on response count
        if len(self.received_responses) >= self.expected_responses:
            self.state = SplitWriteTransactionState.COMPLETE
            self.completion_time = time.time()

    def add_error(self, error: str):
        """Add an error to this transaction"""
        self.errors.append(error)
        self.state = SplitWriteTransactionState.ERROR

    def is_complete(self) -> bool:
        """Check if transaction is complete"""
        return self.state == SplitWriteTransactionState.COMPLETE

    def has_errors(self) -> bool:
        """Check if transaction has errors"""
        return len(self.errors) > 0 or self.state == SplitWriteTransactionState.ERROR

    def get_duration(self) -> Optional[float]:
        """Get transaction duration in seconds"""
        if self.completion_time:
            return self.completion_time - self.start_time
        return None


# Utility functions for packet conversion
def convert_gaxi_packet_to_axi_write_address(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIWriteAddressPacket:
    """Convert a GAXI packet to an AXI write address packet"""
    packet_data = {}

    # Extract relevant fields from GAXI packet
    for field_name in ['id', 'addr', 'len', 'size', 'burst', 'lock', 'cache', 'prot', 'qos', 'region', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)

    return AXIWriteAddressPacket.from_dict(packet_data, field_config)


def convert_gaxi_packet_to_axi_write_data(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIWriteDataPacket:
    """Convert a GAXI packet to an AXI write data packet"""
    packet_data = {}

    # Extract relevant fields from GAXI packet
    for field_name in ['data', 'strb', 'last', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)

    return AXIWriteDataPacket.from_dict(packet_data, field_config)


def convert_gaxi_packet_to_axi_write_response(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIWriteResponsePacket:
    """Convert a GAXI packet to an AXI write response packet"""
    packet_data = {}

    # Extract relevant fields from GAXI packet
    for field_name in ['id', 'resp', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)

    return AXIWriteResponsePacket.from_dict(packet_data, field_config)
