# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MNOCFieldConfigHelper
# Purpose: Network Field Configuration Helper
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Network Field Configuration Helper

Provides field configurations for Network v2.0 packet and ACK formats,
following the same patterns as AXIL4 field configurations.

Features:
- Network v2.0 packet structure with chunk_enables support
- Multiple payload types (CONFIG, TS, RDA, RAW)
- Enhanced chunk-based routing configurations
- ACK packet structures for flow control
- Configurable field widths and addressing

Usage:
    # Create packet field config
    packet_config = MNOCFieldConfigHelper.create_packet_field_config(512, 8)

    # Create ACK field config
    ack_config = MNOCFieldConfigHelper.create_ack_field_config(8)
"""

from typing import Dict, Any, List, Optional
from ..shared.field_config import FieldConfig, FieldDefinition


class MNOCFieldConfigHelper:
    """
    Helper class for creating Network field configurations.

    Provides factory methods for creating field configurations that match
    the Network v2.0 specification with enhanced chunk_enables support.
    """

    @staticmethod
    def create_packet_field_config(data_width: int = 512, addr_width: int = 8,
                                lsb_first: bool = False) -> FieldConfig:
        """
        Create field configuration for Network packet interface (network_data).

        Network Packet Structure:
        - Header: addr + parity
        - Payload: 512-bit data with type-specific structure
        - Control: payload_type, eos, payload parity

        Args:
            data_width: Data payload width (default: 512)
            addr_width: Address field width (default: 8)
            lsb_first: Field ordering mode (default: False for MSB-first)

        Returns:
            FieldConfig for Network packet interface
        """
        config = FieldConfig(lsb_first=lsb_first)

        # Calculate header parity width (odd parity of address)
        header_par_width = 1

        # Header fields (MSB to LSB order in packet)
        config.add_field(FieldDefinition(
            name="header_par",
            bits=header_par_width,
            default=0,
            description="Header parity (odd parity of addr)",
            format="bin"
        ))

        config.add_field(FieldDefinition(
            name="addr",
            bits=addr_width,
            default=0,
            description="Channel ID/Address",
            format="hex"
        ))

        # Control fields
        config.add_field(FieldDefinition(
            name="payload_par",
            bits=1,
            default=0,
            description="Payload parity bit",
            format="bin"
        ))

        config.add_field(FieldDefinition(
            name="eos",
            bits=1,
            default=0,
            description="End of stream marker",
            format="bin"
        ))

        config.add_field(FieldDefinition(
            name="payload_type",
            bits=2,
            default=0,
            description="Payload type selector",
            format="hex",
            encoding={
                0: "CONFIG_PKT",
                1: "TS_PKT",
                2: "RDA_PKT",
                3: "RAW_PKT"
            }
        ))

        # Payload fields - structure depends on payload_type
        # For structured packets (CONFIG, TS, RDA): v2.0 format
        config.add_field(FieldDefinition(
            name="reserved",
            bits=1,
            default=0,
            description="Reserved bit (v2.0)",
            format="bin"
        ))

        config.add_field(FieldDefinition(
            name="chunk_enables",
            bits=16,
            default=0xFFFF,
            description="Chunk validity enables (v2.0)",
            format="hex"
        ))

        config.add_field(FieldDefinition(
            name="ctrl",
            bits=15,
            default=0,
            description="Control flags (15 bits, one per data field)",
            format="hex"
        ))

        # Data fields for structured packets (15 x 32-bit fields)
        for i in range(15):
            config.add_field(FieldDefinition(
                name=f"data_{i}",
                bits=32,
                default=0,
                description=f"Data field {i} (32-bit)",
                format="hex"
            ))

        # Alternative: Raw data field for RAW packets (full 512-bit)
        config.add_field(FieldDefinition(
            name="raw_data",
            bits=512,
            default=0,
            description="Raw 512-bit data payload (RAW packets only)",
            format="hex"
        ))

        return config

    @staticmethod
    def create_ack_field_config(addr_width: int = 8, lsb_first: bool = False) -> FieldConfig:
        """
        Create field configuration for Network ACK interface (network_ack).

        Network ACK Structure:
        - Header: addr + parity
        - ACK: acknowledgment type + parity

        Args:
            addr_width: Address field width (default: 8)
            lsb_first: Field ordering mode (default: False for MSB-first)

        Returns:
            FieldConfig for Network ACK interface
        """
        config = FieldConfig(lsb_first=lsb_first)

        # ACK parity (odd parity of ack field)
        config.add_field(FieldDefinition(
            name="ack_par",
            bits=1,
            default=0,
            description="ACK parity (odd parity of ack field)",
            format="bin"
        ))

        # Acknowledgment type
        config.add_field(FieldDefinition(
            name="ack",
            bits=2,
            default=0,
            description="Acknowledgment type",
            format="hex",
            encoding={
                0: "MSAP_STOP",
                1: "MSAP_START",
                2: "MSAP_CREDIT_ON",
                3: "MSAP_STOP_AT_EOS"
            }
        ))

        # Header parity (odd parity of address)
        config.add_field(FieldDefinition(
            name="header_par",
            bits=1,
            default=0,
            description="Header parity (odd parity of addr)",
            format="bin"
        ))

        # Address field
        config.add_field(FieldDefinition(
            name="addr",
            bits=addr_width,
            default=0,
            description="Channel ID/Address",
            format="hex"
        ))

        return config

    @staticmethod
    def create_fub_field_config(data_width: int = 512, chan_width: int = 5,
                            lsb_first: bool = False) -> FieldConfig:
        """
        Create field configuration for FUB interface (to SRAM Control).

        Enhanced FUB Interface with v2.0 chunk enables:
        - Data: Full packet data
        - Channel: Source/target channel
        - Type: Packet type
        - Chunk enables: v2.0 chunk validity pattern
        - EOS: End of stream marker

        Args:
            data_width: Data width (default: 512)
            chan_width: Channel width (default: 5 for 32 channels)
            lsb_first: Field ordering mode (default: False for MSB-first)

        Returns:
            FieldConfig for FUB interface
        """
        config = FieldConfig(lsb_first=lsb_first)

        # FUB interface fields (MSB to LSB)
        config.add_field(FieldDefinition(
            name="eos",
            bits=1,
            default=0,
            description="End of stream marker",
            format="bin"
        ))

        config.add_field(FieldDefinition(
            name="chunk_en",
            bits=16,
            default=0xFFFF,
            description="Chunk enables (v2.0)",
            format="hex"
        ))

        config.add_field(FieldDefinition(
            name="pkt_type",
            bits=2,
            default=0,
            description="Packet type",
            format="hex",
            encoding={
                0: "CONFIG_PKT",
                1: "TS_PKT",
                2: "RDA_PKT",
                3: "RAW_PKT"
            }
        ))

        config.add_field(FieldDefinition(
            name="chan",
            bits=chan_width,
            default=0,
            description="Channel ID",
            format="hex"
        ))

        config.add_field(FieldDefinition(
            name="data",
            bits=data_width,
            default=0,
            description="Packet data",
            format="hex"
        ))

        return config

    @staticmethod
    def create_rda_field_config(data_width: int = 512, chan_width: int = 5,
                            lsb_first: bool = False) -> FieldConfig:
        """
        Create field configuration for RDA interfaces (descriptor/scheduler).

        RDA Interface for RISC-V Direct Access:
        - Packet: RDA packet data
        - Channel: Source channel
        - EOS: End of stream marker

        Args:
            data_width: Data width (default: 512)
            chan_width: Channel width (default: 5 for 32 channels)
            lsb_first: Field ordering mode (default: False for MSB-first)

        Returns:
            FieldConfig for RDA interface
        """
        config = FieldConfig(lsb_first=lsb_first)

        # RDA interface fields
        config.add_field(FieldDefinition(
            name="eos",
            bits=1,
            default=0,
            description="End of stream marker",
            format="bin"
        ))

        config.add_field(FieldDefinition(
            name="channel",
            bits=chan_width,
            default=0,
            description="Source channel ID",
            format="hex"
        ))

        config.add_field(FieldDefinition(
            name="packet",
            bits=data_width,
            default=0,
            description="RDA packet data",
            format="hex"
        ))

        return config

    @staticmethod
    def create_custom_packet_config(fields_spec: Dict[str, Dict[str, Any]],
                                lsb_first: bool = False) -> FieldConfig:
        """
        Create custom Network packet configuration from field specification.

        Args:
            fields_spec: Dictionary of field specifications
                Format: {field_name: {bits: int, default: int, description: str, ...}}
            lsb_first: Field ordering mode (default: False for MSB-first)

        Returns:
            Custom FieldConfig
        """
        config = FieldConfig(lsb_first=lsb_first)

        for field_name, field_spec in fields_spec.items():
            config.add_field(FieldDefinition(
                name=field_name,
                bits=field_spec['bits'],
                default=field_spec.get('default', 0),
                description=field_spec.get('description', f"Custom field {field_name}"),
                format=field_spec.get('format', 'hex'),
                encoding=field_spec.get('encoding')
            ))

        return config

    @staticmethod
    def get_network_v2_payload_mapping() -> Dict[str, Dict[str, Any]]:
        """
        Get the Network v2.0 payload bit mapping for reference.

        Returns:
            Dictionary describing v2.0 payload structure
        """
        return {
            "structure": "Network v2.0 Payload Format",
            "total_bits": 512,
            "fields": {
                "data_fields": {
                    "bits": "479:0",
                    "width": 480,
                    "description": "Fifteen 32-bit data fields (data[14:0])"
                },
                "ctrl": {
                    "bits": "494:480",
                    "width": 15,
                    "description": "Control flags (15 bits, one per data field)"
                },
                "chunk_enables": {
                    "bits": "510:495",
                    "width": 16,
                    "description": "Chunk validity enables (16 bits, v2.0 NEW)"
                },
                "reserved": {
                    "bits": "511",
                    "width": 1,
                    "description": "Reserved bit (v2.0 NEW)"
                }
            },
            "chunk_mapping": {
                "chunk_0": "data[31:0]",
                "chunk_1": "data[63:32]",
                "chunk_2": "data[95:64]",
                "chunk_3": "data[127:96]",
                "chunk_4": "data[159:128]",
                "chunk_5": "data[191:160]",
                "chunk_6": "data[223:192]",
                "chunk_7": "data[255:224]",
                "chunk_8": "data[287:256]",
                "chunk_9": "data[319:288]",
                "chunk_10": "data[351:320]",
                "chunk_11": "data[383:352]",
                "chunk_12": "data[415:384]",
                "chunk_13": "data[447:416]",
                "chunk_14": "data[479:448]",
                "chunk_15": "data[511:480] (not used in structured packets)"
            },
            "migration_notes": {
                "removed": ["first[3:0]", "len[3:0]", "dummy[8]"],
                "added": ["chunk_enables[15:0]", "reserved[0]"],
                "changed": "Payload bit mapping updated for v2.0 compatibility"
            }
        }

    @staticmethod
    def validate_chunk_enables(chunk_enables: int, packet_type: int = 1) -> bool:
        """
        Validate chunk_enables field according to Network v2.0 rules.

        Args:
            chunk_enables: 16-bit chunk enables value
            packet_type: Packet type (0=CONFIG, 1=TS, 2=RDA, 3=RAW)

        Returns:
            True if chunk_enables is valid
        """
        # Basic validation: at least one chunk must be valid
        if chunk_enables == 0:
            return False

        # Check range (16-bit value)
        if chunk_enables < 0 or chunk_enables > 0xFFFF:
            return False

        # For RAW packets, chunk_enables is part of raw data
        if packet_type == 3:  # RAW_PKT
            return True

        # For structured packets, chunk 15 should typically not be used
        # (since structured packets only have 15 data fields, chunks 0-14)
        if packet_type in [0, 1, 2] and (chunk_enables & 0x8000):
            # Warning: chunk 15 set for structured packet
            # This might be valid in some cases, so just warn but don't fail
            pass

        return True

    @staticmethod
    def chunk_enables_to_count(chunk_enables: int) -> int:
        """
        Count number of valid chunks from chunk_enables field.

        Args:
            chunk_enables: 16-bit chunk enables value

        Returns:
            Number of valid chunks (popcount)
        """
        return bin(chunk_enables).count('1')

    @staticmethod
    def create_chunk_enables_pattern(chunk_list: List[int]) -> int:
        """
        Create chunk_enables value from list of valid chunk indices.

        Args:
            chunk_list: List of chunk indices (0-15) that should be valid

        Returns:
            16-bit chunk_enables value
        """
        chunk_enables = 0
        for chunk_idx in chunk_list:
            if 0 <= chunk_idx <= 15:
                chunk_enables |= (1 << chunk_idx)
        return chunk_enables

    @staticmethod
    def decode_chunk_enables(chunk_enables: int) -> List[int]:
        """
        Decode chunk_enables value to list of valid chunk indices.

        Args:
            chunk_enables: 16-bit chunk enables value

        Returns:
            List of valid chunk indices
        """
        valid_chunks = []
        for i in range(16):
            if chunk_enables & (1 << i):
                valid_chunks.append(i)
        return valid_chunks
