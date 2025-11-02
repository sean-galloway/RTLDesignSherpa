# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4Packet
# Purpose: AXI4 Packet Implementation - FIXED to use generic field names consistently
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Packet Implementation - FIXED to use generic field names consistently

This module provides the AXI4Packet class that extends the base Packet class
with AXI4-specific functionality, using generic field names that match the
field configuration. The pkt_prefix parameter handles AXI4 signal mapping.

Key changes:
- Factory methods now use generic field names (id, addr, data, resp, etc.)
- String representation updated to use generic field names
- Documentation updated to reflect generic naming convention
"""

from typing import Optional, Tuple, Dict, Any
from ..shared.packet import Packet
from .axi4_field_configs import AXI4FieldConfigHelper


class AXI4Packet(Packet):
    """
    AXI4 Packet class extending the optimized base Packet class.
    FIXED to use generic field names consistently.

    Provides AXI4-specific functionality while leveraging all the performance
    optimizations and field management from the base Packet class.
    """

    def __init__(self, field_config, **kwargs):
        """
        Initialize AXI4 packet with field configuration.

        Args:
            field_config: FieldConfig object for the specific AXI4 channel
            **kwargs: Initial field values (use generic names: id, addr, data, etc.)
        """
        # Call parent constructor with field config and initial values
        super().__init__(field_config, **kwargs)

        # Cache channel type for performance
        self._channel_type = None

    @classmethod
    def create_aw_packet(cls, id_width: int = 8, addr_width: int = 32, user_width: int = 1, **field_values):
        """
        Create a Write Address (AW) channel packet.

        Args:
            id_width: Width of ID field
            addr_width: Width of ADDR field
            user_width: Width of USER field
            **field_values: AXI4 AW channel field values using GENERIC names (id, addr, len, etc.)

        Returns:
            AXI4Packet configured for AW channel

        Example:
            packet = AXI4Packet.create_aw_packet(id=1, addr=0x1000, len=3)
        """
        field_config = AXI4FieldConfigHelper.create_aw_field_config(id_width, addr_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_w_packet(cls, data_width: int = 32, user_width: int = 1, **field_values):
        """
        Create a Write Data (W) channel packet.

        Args:
            data_width: Width of DATA field
            user_width: Width of USER field
            **field_values: AXI4 W channel field values using GENERIC names (data, strb, last, user)

        Returns:
            AXI4Packet configured for W channel

        Example:
            packet = AXI4Packet.create_w_packet(data=0xDEADBEEF, last=1)
        """
        field_config = AXI4FieldConfigHelper.create_w_field_config(data_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_b_packet(cls, id_width: int = 8, user_width: int = 1, **field_values):
        """
        Create a Write Response (B) channel packet.

        Args:
            id_width: Width of ID field
            user_width: Width of USER field
            **field_values: AXI4 B channel field values using GENERIC names (id, resp, user)

        Returns:
            AXI4Packet configured for B channel

        Example:
            packet = AXI4Packet.create_b_packet(id=1, resp=0)  # OKAY response
        """
        field_config = AXI4FieldConfigHelper.create_b_field_config(id_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_ar_packet(cls, id_width: int = 8, addr_width: int = 32, user_width: int = 1, **field_values):
        """
        Create a Read Address (AR) channel packet.

        Args:
            id_width: Width of ID field
            addr_width: Width of ADDR field
            user_width: Width of USER field
            **field_values: AXI4 AR channel field values using GENERIC names (id, addr, len, etc.)

        Returns:
            AXI4Packet configured for AR channel

        Example:
            packet = AXI4Packet.create_ar_packet(id=2, addr=0x2000, len=7)
        """
        field_config = AXI4FieldConfigHelper.create_ar_field_config(id_width, addr_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_r_packet(cls, id_width: int = 8, data_width: int = 32, user_width: int = 1, **field_values):
        """
        Create a Read Data (R) channel packet.

        Args:
            id_width: Width of ID field
            data_width: Width of DATA field
            user_width: Width of USER field
            **field_values: AXI4 R channel field values using GENERIC names (id, data, resp, last, user)

        Returns:
            AXI4Packet configured for R channel

        Example:
            packet = AXI4Packet.create_r_packet(id=2, data=0x12345678, last=1)
        """
        field_config = AXI4FieldConfigHelper.create_r_field_config(id_width, data_width, user_width)
        return cls(field_config, **field_values)

    def get_channel_type(self) -> str:
        """
        Determine which AXI4 channel this packet belongs to.

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

        if has_addr and has_len and not has_data:
            # Address channel with burst info
            # Check for write vs read specific fields
            if hasattr(self, 'cache') or hasattr(self, 'prot'):
                self._channel_type = 'AW'
            else:
                self._channel_type = 'AR'
        elif has_data and has_strb and has_last and not has_resp:
            self._channel_type = 'W'
        elif has_data and has_resp and has_last and not has_strb:
            self._channel_type = 'R'
        elif has_resp and not has_data and not has_addr:
            self._channel_type = 'B'
        else:
            self._channel_type = 'UNKNOWN'

        return self._channel_type

    def validate_axi4_protocol(self) -> Tuple[bool, str]:
        """
        Validate packet against AXI4 protocol rules using generic field names.

        Returns:
            Tuple of (is_valid, error_message)
        """
        channel_type = self.get_channel_type()
        errors = []

        if channel_type in ['AW', 'AR']:
            # Address channel validation using generic field names
            burst_len = getattr(self, 'len', 0)
            if not (0 <= burst_len <= 255):
                errors.append(f"Invalid burst length: {burst_len} (must be 0-255)")

            size = getattr(self, 'size', 0)
            if not (0 <= size <= 7):
                errors.append(f"Invalid size: {size} (must be 0-7)")

            burst_type = getattr(self, 'burst', 0)
            if burst_type not in [0, 1, 2]:
                errors.append(f"Invalid burst type: {burst_type} (must be 0=FIXED, 1=INCR, 2=WRAP)")

        elif channel_type == 'W':
            # Write data validation using generic field names
            if not hasattr(self, 'last'):
                errors.append("W channel must have 'last' field")

        elif channel_type == 'R':
            # Read data validation using generic field names
            if not hasattr(self, 'last'):
                errors.append("R channel must have 'last' field")

            resp = getattr(self, 'resp', 0)
            if resp not in [0, 1, 2, 3]:
                errors.append(f"Invalid response: {resp} (must be 0-3)")

        elif channel_type == 'B':
            # Write response validation using generic field names
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
                'burst_length': (getattr(self, 'len', 0) + 1),  # Convert to actual beats
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
            'is_exclusive': resp_code == 1
        }

        if channel_type == 'R':
            info['is_last'] = getattr(self, 'last', 0) == 1

        return info

    def __str__(self) -> str:
        """String representation of the packet using generic field names."""
        channel_type = self.get_channel_type()

        if channel_type == 'AW':
            return f"AXI4Packet(AW: id={getattr(self, 'id', '?')}, addr=0x{getattr(self, 'addr', 0):X}, len={getattr(self, 'len', 0)})"
        elif channel_type == 'W':
            return f"AXI4Packet(W: data=0x{getattr(self, 'data', 0):X}, last={getattr(self, 'last', '?')})"
        elif channel_type == 'B':
            resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
            resp = resp_names.get(getattr(self, 'resp', 0), 'UNKNOWN')
            return f"AXI4Packet(B: id={getattr(self, 'id', '?')}, resp={resp})"
        elif channel_type == 'AR':
            return f"AXI4Packet(AR: id={getattr(self, 'id', '?')}, addr=0x{getattr(self, 'addr', 0):X}, len={getattr(self, 'len', 0)})"
        elif channel_type == 'R':
            resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
            resp = resp_names.get(getattr(self, 'resp', 0), 'UNKNOWN')
            return f"AXI4Packet(R: id={getattr(self, 'id', '?')}, data=0x{getattr(self, 'data', 0):X}, resp={resp}, last={getattr(self, 'last', '?')})"
        else:
            return f"AXI4Packet({channel_type})"


# Convenience functions for common packet patterns using GENERIC field names

def create_simple_write_packets(id_val: int, addr: int, data: int,
                            id_width: int = 8, addr_width: int = 32, data_width: int = 32) -> Tuple[AXI4Packet, AXI4Packet]:
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
    aw_packet = AXI4Packet.create_aw_packet(
        id_width=id_width, addr_width=addr_width,
        id=id_val, addr=addr, len=0, size=2, burst=1  # FIXED: using generic names
    )

    strb_width = data_width // 8
    w_packet = AXI4Packet.create_w_packet(
        data_width=data_width,
        data=data, strb=(1 << strb_width) - 1, last=1  # FIXED: using generic names
    )

    return aw_packet, w_packet


def create_simple_read_packet(id_val: int, addr: int,
                            id_width: int = 8, addr_width: int = 32) -> AXI4Packet:
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
    return AXI4Packet.create_ar_packet(
        id_width=id_width, addr_width=addr_width,
        id=id_val, addr=addr, len=0, size=2, burst=1  # FIXED: using generic names
    )


# Example usage and testing
if __name__ == "__main__":
    print("AXI4 Packet - FIXED Generic Field Names Implementation Testing")
    print("=" * 70)

    # Test packet creation using generic field names
    aw_packet = AXI4Packet.create_aw_packet(id=1, addr=0x1000, len=3)
    print(f"AW Packet: {aw_packet}")
    print(f"Channel Type: {aw_packet.get_channel_type()}")
    print(f"Burst Info: {aw_packet.get_burst_info()}")

    # Test validation
    is_valid, error_msg = aw_packet.validate_axi4_protocol()
    print(f"Validation: {is_valid}, Message: {error_msg}")

    # Test W packet using generic field names
    w_packet = AXI4Packet.create_w_packet(data=0xDEADBEEF, last=1)
    print(f"\nW Packet: {w_packet}")

    # Test R packet using generic field names
    r_packet = AXI4Packet.create_r_packet(id=2, data=0x12345678, resp=0, last=1)
    print(f"R Packet: {r_packet}")
    print(f"Response Info: {r_packet.get_response_info()}")

    # Test convenience functions using generic field names
    aw, w = create_simple_write_packets(1, 0x2000, 0x12345678)
    print(f"\nSimple Write - AW: {aw}")
    print(f"Simple Write - W: {w}")

    ar = create_simple_read_packet(2, 0x3000)
    print(f"Simple Read - AR: {ar}")

    print("\nAll packets created successfully using GENERIC field names!")
    print("Field configuration uses generic names (id, addr, data, resp, etc.)")
    print("pkt_prefix parameter in GAXI components handles AXI4 signal mapping (ar_, r_, etc.)")
