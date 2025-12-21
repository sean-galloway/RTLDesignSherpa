# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5Packet
# Purpose: AXI5 Packet Implementation with support for AXI5-specific features.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Packet Implementation - Extends base Packet class with AXI5-specific functionality.

This module provides the AXI5Packet class that extends the base Packet class
with AXI5-specific functionality, using generic field names that match the
field configuration.

AXI5-specific features supported:
- Atomic operations (ATOP)
- Memory Tagging Extension (MTE) - TAG, TAGOP, TAGUPDATE, TAGMATCH
- Memory Partitioning and Monitoring (MPAM)
- Memory Encryption Context (MECID)
- Non-secure Access ID (NSAID)
- Transaction Tracing (TRACE)
- Chunked transfers (CHUNKEN, CHUNKV, CHUNKNUM, CHUNKSTRB)
- Poison indicators (POISON)
- Unique/Exclusive access (UNIQUE)

Key differences from AXI4:
- Removed: ARREGION, AWREGION
- Added: All signals listed above
"""

from typing import Optional, Tuple, Dict, Any
from ..shared.packet import Packet
from .axi5_field_configs import AXI5FieldConfigHelper


class AXI5Packet(Packet):
    """
    AXI5 Packet class extending the optimized base Packet class.

    Provides AXI5-specific functionality while leveraging all the performance
    optimizations and field management from the base Packet class.
    """

    def __init__(self, field_config, **kwargs):
        """
        Initialize AXI5 packet with field configuration.

        Args:
            field_config: FieldConfig object for the specific AXI5 channel
            **kwargs: Initial field values (use generic names: id, addr, data, etc.)
        """
        # Call parent constructor with field config and initial values
        super().__init__(field_config, **kwargs)

        # Cache channel type for performance
        self._channel_type = None

    @classmethod
    def create_aw_packet(cls, id_width: int = 8, addr_width: int = 32, user_width: int = 1,
                         data_width: int = 32, **field_values):
        """
        Create a Write Address (AW) channel packet.

        Args:
            id_width: Width of ID field
            addr_width: Width of ADDR field
            user_width: Width of USER field
            data_width: Data width for tag calculation
            **field_values: AXI5 AW channel field values using GENERIC names

        Returns:
            AXI5Packet configured for AW channel

        Example:
            packet = AXI5Packet.create_aw_packet(id=1, addr=0x1000, len=3, atop=0x30)
        """
        field_config = AXI5FieldConfigHelper.create_aw_field_config(
            id_width, addr_width, user_width, data_width=data_width
        )
        return cls(field_config, **field_values)

    @classmethod
    def create_w_packet(cls, data_width: int = 32, user_width: int = 1, **field_values):
        """
        Create a Write Data (W) channel packet.

        Args:
            data_width: Width of DATA field
            user_width: Width of USER field
            **field_values: AXI5 W channel field values using GENERIC names

        Returns:
            AXI5Packet configured for W channel

        Example:
            packet = AXI5Packet.create_w_packet(data=0xDEADBEEF, last=1, poison=0)
        """
        field_config = AXI5FieldConfigHelper.create_w_field_config(data_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_b_packet(cls, id_width: int = 8, user_width: int = 1,
                        data_width: int = 32, **field_values):
        """
        Create a Write Response (B) channel packet.

        Args:
            id_width: Width of ID field
            user_width: Width of USER field
            data_width: Data width for tag calculation
            **field_values: AXI5 B channel field values using GENERIC names

        Returns:
            AXI5Packet configured for B channel

        Example:
            packet = AXI5Packet.create_b_packet(id=1, resp=0, tagmatch=1)
        """
        field_config = AXI5FieldConfigHelper.create_b_field_config(
            id_width, user_width, data_width=data_width
        )
        return cls(field_config, **field_values)

    @classmethod
    def create_ar_packet(cls, id_width: int = 8, addr_width: int = 32,
                         user_width: int = 1, **field_values):
        """
        Create a Read Address (AR) channel packet.

        Args:
            id_width: Width of ID field
            addr_width: Width of ADDR field
            user_width: Width of USER field
            **field_values: AXI5 AR channel field values using GENERIC names

        Returns:
            AXI5Packet configured for AR channel

        Example:
            packet = AXI5Packet.create_ar_packet(id=2, addr=0x2000, len=7, chunken=1)
        """
        field_config = AXI5FieldConfigHelper.create_ar_field_config(
            id_width, addr_width, user_width
        )
        return cls(field_config, **field_values)

    @classmethod
    def create_r_packet(cls, id_width: int = 8, data_width: int = 32,
                        user_width: int = 1, **field_values):
        """
        Create a Read Data (R) channel packet.

        Args:
            id_width: Width of ID field
            data_width: Width of DATA field
            user_width: Width of USER field
            **field_values: AXI5 R channel field values using GENERIC names

        Returns:
            AXI5Packet configured for R channel

        Example:
            packet = AXI5Packet.create_r_packet(id=2, data=0x12345678, last=1, poison=0)
        """
        field_config = AXI5FieldConfigHelper.create_r_field_config(
            id_width, data_width, user_width
        )
        return cls(field_config, **field_values)

    def get_channel_type(self) -> str:
        """
        Determine which AXI5 channel this packet belongs to.

        Returns:
            String indicating channel type ('AW', 'W', 'B', 'AR', 'R', 'UNKNOWN')
        """
        if self._channel_type:
            return self._channel_type

        # Determine channel based on field presence
        has_addr = hasattr(self, 'addr')
        has_data = hasattr(self, 'data')
        has_strb = hasattr(self, 'strb')
        has_last = hasattr(self, 'last')
        has_resp = hasattr(self, 'resp')
        has_len = hasattr(self, 'len')
        has_atop = hasattr(self, 'atop')
        has_chunken = hasattr(self, 'chunken')
        has_chunkv = hasattr(self, 'chunkv')
        has_tagupdate = hasattr(self, 'tagupdate')

        if has_addr and has_len and not has_data:
            # Address channel with burst info
            if has_atop:
                self._channel_type = 'AW'
            elif has_chunken:
                self._channel_type = 'AR'
            else:
                # Default to AW if we have cache/prot
                self._channel_type = 'AW' if hasattr(self, 'cache') else 'AR'
        elif has_data and has_strb and has_last and not has_resp:
            # W channel has tagupdate
            self._channel_type = 'W'
        elif has_data and has_resp and has_last and not has_strb:
            # R channel has chunkv
            self._channel_type = 'R'
        elif has_resp and not has_data and not has_addr:
            self._channel_type = 'B'
        else:
            self._channel_type = 'UNKNOWN'

        return self._channel_type

    def validate_axi5_protocol(self) -> Tuple[bool, str]:
        """
        Validate packet against AXI5 protocol rules using generic field names.

        Returns:
            Tuple of (is_valid, error_message)
        """
        channel_type = self.get_channel_type()
        errors = []

        if channel_type in ['AW', 'AR']:
            # Address channel validation
            burst_len = getattr(self, 'len', 0)
            if not (0 <= burst_len <= 255):
                errors.append(f"Invalid burst length: {burst_len} (must be 0-255)")

            size = getattr(self, 'size', 0)
            if not (0 <= size <= 7):
                errors.append(f"Invalid size: {size} (must be 0-7)")

            burst_type = getattr(self, 'burst', 0)
            if burst_type not in [0, 1, 2]:
                errors.append(f"Invalid burst type: {burst_type} (must be 0=FIXED, 1=INCR, 2=WRAP)")

            # AXI5-specific: validate ATOP for AW
            if channel_type == 'AW':
                atop = getattr(self, 'atop', 0)
                if atop != 0:
                    # Validate atomic operation type
                    atop_type = (atop >> 4) & 0x3
                    if atop_type not in [0, 1, 2, 3]:
                        errors.append(f"Invalid ATOP type: {atop_type}")

            # AXI5-specific: validate TAGOP
            tagop = getattr(self, 'tagop', 0)
            if not (0 <= tagop <= 3):
                errors.append(f"Invalid TAGOP: {tagop} (must be 0-3)")

        elif channel_type == 'W':
            # Write data validation
            if not hasattr(self, 'last'):
                errors.append("W channel must have 'last' field")

        elif channel_type == 'R':
            # Read data validation
            if not hasattr(self, 'last'):
                errors.append("R channel must have 'last' field")

            resp = getattr(self, 'resp', 0)
            if resp not in [0, 1, 2, 3]:
                errors.append(f"Invalid response: {resp} (must be 0-3)")

            # AXI5-specific: validate chunk fields
            chunkv = getattr(self, 'chunkv', 0)
            if chunkv:
                chunknum = getattr(self, 'chunknum', 0)
                if chunknum < 0:
                    errors.append(f"Invalid chunknum: {chunknum}")

        elif channel_type == 'B':
            # Write response validation
            resp = getattr(self, 'resp', 0)
            if resp not in [0, 1, 2, 3]:
                errors.append(f"Invalid response: {resp} (must be 0-3)")

        is_valid = len(errors) == 0
        error_message = "; ".join(errors) if errors else ""

        return is_valid, error_message

    def get_burst_info(self) -> Dict[str, Any]:
        """
        Get burst information from address packets (AW/AR) using generic field names.

        Returns:
            Dictionary with burst information, or empty dict if not an address packet
        """
        channel_type = self.get_channel_type()

        if channel_type in ['AW', 'AR']:
            return {
                'burst_type': getattr(self, 'burst', None),
                'burst_length': (getattr(self, 'len', 0) + 1),
                'burst_size': getattr(self, 'size', None),
                'bytes_per_beat': (1 << getattr(self, 'size', 0)),
                'total_bytes': (getattr(self, 'len', 0) + 1) * (1 << getattr(self, 'size', 0)),
                'address': getattr(self, 'addr', None)
            }

        return {}

    def get_response_info(self) -> Dict[str, Any]:
        """
        Get response information from response packets (B/R) using generic field names.

        Returns:
            Dictionary with response information, or empty dict if not a response packet
        """
        channel_type = self.get_channel_type()

        if channel_type in ['B', 'R']:
            resp_code = getattr(self, 'resp', 0)
        else:
            return {}

        resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}

        info = {
            'response_code': resp_code,
            'response_name': resp_names.get(resp_code, 'UNKNOWN'),
            'is_error': resp_code >= 2,
            'is_exclusive': resp_code == 1,
            'tagmatch': getattr(self, 'tagmatch', None),
        }

        if channel_type == 'R':
            info['is_last'] = getattr(self, 'last', 0) == 1
            info['poison'] = getattr(self, 'poison', 0)
            info['chunkv'] = getattr(self, 'chunkv', 0)
            info['chunknum'] = getattr(self, 'chunknum', None)

        if channel_type == 'B':
            info['trace'] = getattr(self, 'trace', 0)

        return info

    def get_axi5_features(self) -> Dict[str, Any]:
        """
        Get AXI5-specific feature information.

        Returns:
            Dictionary with AXI5 feature status
        """
        features = {}

        # Atomic operation
        if hasattr(self, 'atop'):
            atop = getattr(self, 'atop', 0)
            features['is_atomic'] = atop != 0
            if atop != 0:
                atop_names = {
                    0x00: "Non-atomic",
                    0x10: "AtomicStore",
                    0x20: "AtomicLoad",
                    0x30: "AtomicSwap",
                    0x31: "AtomicCompare",
                }
                features['atomic_type'] = atop_names.get(atop, f"Atomic(0x{atop:02x})")

        # Memory Tagging Extension
        if hasattr(self, 'tagop'):
            tagop = getattr(self, 'tagop', 0)
            tagop_names = {0: "Invalid", 1: "Transfer", 2: "Update", 3: "Match"}
            features['tagop'] = tagop_names.get(tagop, f"Unknown({tagop})")
            features['tag'] = getattr(self, 'tag', None)

        if hasattr(self, 'tagmatch'):
            features['tagmatch'] = getattr(self, 'tagmatch', 0)

        if hasattr(self, 'tagupdate'):
            features['tagupdate'] = getattr(self, 'tagupdate', 0)

        # Security and partitioning
        if hasattr(self, 'nsaid'):
            features['nsaid'] = getattr(self, 'nsaid', 0)

        if hasattr(self, 'mpam'):
            features['mpam'] = getattr(self, 'mpam', 0)

        if hasattr(self, 'mecid'):
            features['mecid'] = getattr(self, 'mecid', 0)

        # Tracing
        if hasattr(self, 'trace'):
            features['trace'] = getattr(self, 'trace', 0)

        # Unique access
        if hasattr(self, 'unique'):
            features['unique'] = getattr(self, 'unique', 0)

        # Chunking
        if hasattr(self, 'chunken'):
            features['chunken'] = getattr(self, 'chunken', 0)

        if hasattr(self, 'chunkv'):
            features['chunkv'] = getattr(self, 'chunkv', 0)
            if features.get('chunkv'):
                features['chunknum'] = getattr(self, 'chunknum', 0)
                features['chunkstrb'] = getattr(self, 'chunkstrb', 0)

        # Poison
        if hasattr(self, 'poison'):
            features['poison'] = getattr(self, 'poison', 0)

        return features

    def __str__(self) -> str:
        """String representation of the packet using generic field names."""
        channel_type = self.get_channel_type()
        features = self.get_axi5_features()

        # Build feature string
        feature_strs = []
        if features.get('is_atomic'):
            feature_strs.append(f"atomic={features.get('atomic_type', '?')}")
        if features.get('poison'):
            feature_strs.append("POISON")
        if features.get('trace'):
            feature_strs.append("TRACE")
        feature_str = f", {', '.join(feature_strs)}" if feature_strs else ""

        if channel_type == 'AW':
            return (f"AXI5Packet(AW: id={getattr(self, 'id', '?')}, "
                    f"addr=0x{getattr(self, 'addr', 0):X}, "
                    f"len={getattr(self, 'len', 0)}{feature_str})")
        elif channel_type == 'W':
            return (f"AXI5Packet(W: data=0x{getattr(self, 'data', 0):X}, "
                    f"last={getattr(self, 'last', '?')}{feature_str})")
        elif channel_type == 'B':
            resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
            resp = resp_names.get(getattr(self, 'resp', 0), 'UNKNOWN')
            tagmatch = getattr(self, 'tagmatch', None)
            tagmatch_str = f", tagmatch={tagmatch}" if tagmatch is not None else ""
            return (f"AXI5Packet(B: id={getattr(self, 'id', '?')}, "
                    f"resp={resp}{tagmatch_str}{feature_str})")
        elif channel_type == 'AR':
            chunken = getattr(self, 'chunken', 0)
            chunk_str = ", chunken=1" if chunken else ""
            return (f"AXI5Packet(AR: id={getattr(self, 'id', '?')}, "
                    f"addr=0x{getattr(self, 'addr', 0):X}, "
                    f"len={getattr(self, 'len', 0)}{chunk_str}{feature_str})")
        elif channel_type == 'R':
            resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
            resp = resp_names.get(getattr(self, 'resp', 0), 'UNKNOWN')
            return (f"AXI5Packet(R: id={getattr(self, 'id', '?')}, "
                    f"data=0x{getattr(self, 'data', 0):X}, "
                    f"resp={resp}, last={getattr(self, 'last', '?')}{feature_str})")
        else:
            return f"AXI5Packet({channel_type})"


# Convenience functions for common packet patterns using GENERIC field names

def create_simple_write_packets(id_val: int, addr: int, data: int,
                                id_width: int = 8, addr_width: int = 32,
                                data_width: int = 32) -> Tuple[AXI5Packet, AXI5Packet]:
    """
    Create AW and W packets for a simple single-beat write using generic field names.

    Args:
        id_val: Write ID
        addr: Write address
        data: Write data
        id_width: ID field width
        addr_width: Address field width
        data_width: Data field width

    Returns:
        Tuple of (aw_packet, w_packet)
    """
    aw_packet = AXI5Packet.create_aw_packet(
        id_width=id_width, addr_width=addr_width, data_width=data_width,
        id=id_val, addr=addr, len=0, size=2, burst=1
    )

    strb_width = data_width // 8
    w_packet = AXI5Packet.create_w_packet(
        data_width=data_width,
        data=data, strb=(1 << strb_width) - 1, last=1
    )

    return aw_packet, w_packet


def create_simple_read_packet(id_val: int, addr: int,
                              id_width: int = 8, addr_width: int = 32) -> AXI5Packet:
    """
    Create AR packet for a simple single-beat read using generic field names.

    Args:
        id_val: Read ID
        addr: Read address
        id_width: ID field width
        addr_width: Address field width

    Returns:
        AR packet
    """
    return AXI5Packet.create_ar_packet(
        id_width=id_width, addr_width=addr_width,
        id=id_val, addr=addr, len=0, size=2, burst=1
    )


def create_atomic_write_packets(id_val: int, addr: int, data: int, atop: int,
                                id_width: int = 8, addr_width: int = 32,
                                data_width: int = 32) -> Tuple[AXI5Packet, AXI5Packet]:
    """
    Create AW and W packets for an atomic operation.

    Args:
        id_val: Write ID
        addr: Write address
        data: Write data
        atop: Atomic operation type (0x10=Store, 0x20=Load, 0x30=Swap, 0x31=Compare)
        id_width: ID field width
        addr_width: Address field width
        data_width: Data field width

    Returns:
        Tuple of (aw_packet, w_packet)
    """
    aw_packet = AXI5Packet.create_aw_packet(
        id_width=id_width, addr_width=addr_width, data_width=data_width,
        id=id_val, addr=addr, len=0, size=2, burst=1, atop=atop
    )

    strb_width = data_width // 8
    w_packet = AXI5Packet.create_w_packet(
        data_width=data_width,
        data=data, strb=(1 << strb_width) - 1, last=1
    )

    return aw_packet, w_packet


def create_tagged_write_packets(id_val: int, addr: int, data: int, tag: int, tagop: int,
                                id_width: int = 8, addr_width: int = 32,
                                data_width: int = 32) -> Tuple[AXI5Packet, AXI5Packet]:
    """
    Create AW and W packets with Memory Tagging Extension support.

    Args:
        id_val: Write ID
        addr: Write address
        data: Write data
        tag: Memory tag value
        tagop: Tag operation (0=Invalid, 1=Transfer, 2=Update, 3=Match)
        id_width: ID field width
        addr_width: Address field width
        data_width: Data field width

    Returns:
        Tuple of (aw_packet, w_packet)
    """
    aw_packet = AXI5Packet.create_aw_packet(
        id_width=id_width, addr_width=addr_width, data_width=data_width,
        id=id_val, addr=addr, len=0, size=2, burst=1, tag=tag, tagop=tagop
    )

    strb_width = data_width // 8
    num_tags = max(1, data_width // 128)
    w_packet = AXI5Packet.create_w_packet(
        data_width=data_width,
        data=data, strb=(1 << strb_width) - 1, last=1,
        tag=tag, tagupdate=(1 << num_tags) - 1  # Update all tags
    )

    return aw_packet, w_packet


# Example usage and testing
if __name__ == "__main__":
    print("AXI5 Packet Implementation Testing")
    print("=" * 70)

    # Test packet creation using generic field names
    aw_packet = AXI5Packet.create_aw_packet(id=1, addr=0x1000, len=3)
    print(f"AW Packet: {aw_packet}")
    print(f"Channel Type: {aw_packet.get_channel_type()}")
    print(f"Burst Info: {aw_packet.get_burst_info()}")

    # Test validation
    is_valid, error_msg = aw_packet.validate_axi5_protocol()
    print(f"Validation: {is_valid}, Message: {error_msg}")

    # Test W packet using generic field names
    w_packet = AXI5Packet.create_w_packet(data=0xDEADBEEF, last=1, poison=0)
    print(f"\nW Packet: {w_packet}")

    # Test R packet using generic field names
    r_packet = AXI5Packet.create_r_packet(id=2, data=0x12345678, resp=0, last=1, poison=0)
    print(f"R Packet: {r_packet}")
    print(f"Response Info: {r_packet.get_response_info()}")

    # Test atomic operation
    aw_atomic, w_atomic = create_atomic_write_packets(1, 0x2000, 0xCAFEBABE, atop=0x30)
    print(f"\nAtomic Write - AW: {aw_atomic}")
    print(f"AXI5 Features: {aw_atomic.get_axi5_features()}")

    # Test tagged write
    aw_tagged, w_tagged = create_tagged_write_packets(2, 0x3000, 0x12345678, tag=0xA, tagop=1)
    print(f"\nTagged Write - AW: {aw_tagged}")
    print(f"Tagged Write - W: {w_tagged}")
    print(f"AXI5 Features: {aw_tagged.get_axi5_features()}")

    print("\nAll packets created successfully!")
