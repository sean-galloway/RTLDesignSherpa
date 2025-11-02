# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL4Packet
# Purpose: AXIL4 (AXI4-Lite) Packet Implementation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 (AXI4-Lite) Packet Implementation

Provides the AXIL4Packet class that extends the base Packet class with
AXI4-Lite specific functionality. Uses generic field names that match
the field configuration, with pkt_prefix handling AXIL4 signal mapping.

Key differences from AXI4:
- No burst support (always single transfer)
- No ID fields
- Simplified field sets
- Single transfer validation
"""

from typing import Optional, Tuple, Dict, Any
from ..shared.packet import Packet
from .axil4_field_configs import AXIL4FieldConfigHelper


class AXIL4Packet(Packet):
    """
    AXIL4 (AXI4-Lite) Packet class extending the optimized base Packet class.
    
    Provides AXIL4-specific functionality while leveraging all performance
    optimizations and field management from the base Packet class.
    """

    def __init__(self, field_config, **kwargs):
        """
        Initialize AXIL4 packet with field configuration.
        
        Args:
            field_config: FieldConfig object for the specific AXIL4 channel
            **kwargs: Initial field values (use generic names: addr, data, resp, etc.)
        """
        super().__init__(field_config, **kwargs)
        self._channel_type = None

    @classmethod
    def create_aw_packet(cls, addr_width: int = 32, user_width: int = 0, **field_values):
        """
        Create a Write Address (AW) channel packet.
        
        Args:
            addr_width: Width of address field
            user_width: Width of user field (0 to disable)
            **field_values: AXIL4 AW channel field values (addr, prot, user)
        
        Returns:
            AXIL4Packet configured for AW channel
            
        Example:
            packet = AXIL4Packet.create_aw_packet(addr=0x1000, prot=0)
        """
        field_config = AXIL4FieldConfigHelper.create_aw_field_config(addr_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_w_packet(cls, data_width: int = 32, user_width: int = 0, **field_values):
        """
        Create a Write Data (W) channel packet.
        
        Args:
            data_width: Width of data field
            user_width: Width of user field (0 to disable)
            **field_values: AXIL4 W channel field values (data, strb, user)
        
        Returns:
            AXIL4Packet configured for W channel
            
        Example:
            packet = AXIL4Packet.create_w_packet(data=0x12345678, strb=0xF)
        """
        field_config = AXIL4FieldConfigHelper.create_w_field_config(data_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_b_packet(cls, user_width: int = 0, **field_values):
        """
        Create a Write Response (B) channel packet.
        
        Args:
            user_width: Width of user field (0 to disable)
            **field_values: AXIL4 B channel field values (resp, user)
        
        Returns:
            AXIL4Packet configured for B channel
            
        Example:
            packet = AXIL4Packet.create_b_packet(resp=0)
        """
        field_config = AXIL4FieldConfigHelper.create_b_field_config(user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_ar_packet(cls, addr_width: int = 32, user_width: int = 0, **field_values):
        """
        Create a Read Address (AR) channel packet.
        
        Args:
            addr_width: Width of address field
            user_width: Width of user field (0 to disable)
            **field_values: AXIL4 AR channel field values (addr, prot, user)
        
        Returns:
            AXIL4Packet configured for AR channel
            
        Example:
            packet = AXIL4Packet.create_ar_packet(addr=0x2000, prot=0)
        """
        field_config = AXIL4FieldConfigHelper.create_ar_field_config(addr_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_r_packet(cls, data_width: int = 32, user_width: int = 0, **field_values):
        """
        Create a Read Data (R) channel packet.
        
        Args:
            data_width: Width of data field
            user_width: Width of user field (0 to disable)
            **field_values: AXIL4 R channel field values (data, resp, user)
        
        Returns:
            AXIL4Packet configured for R channel
            
        Example:
            packet = AXIL4Packet.create_r_packet(data=0xABCDEF00, resp=0)
        """
        field_config = AXIL4FieldConfigHelper.create_r_field_config(data_width, user_width)
        return cls(field_config, **field_values)

    def get_channel_type(self) -> str:
        """
        Determine the AXIL4 channel type based on available fields.
        
        Returns:
            Channel type string ('AW', 'W', 'B', 'AR', 'R')
        """
        if self._channel_type is None:
            field_names = set(self.get_field_names())
            
            # Check for unique field combinations
            if 'addr' in field_names and 'prot' in field_names and 'data' not in field_names:
                if 'resp' in field_names:
                    self._channel_type = 'AR'  # Read address
                else:
                    self._channel_type = 'AW'  # Write address
            elif 'data' in field_names and 'strb' in field_names:
                self._channel_type = 'W'   # Write data
            elif 'data' in field_names and 'resp' in field_names:
                self._channel_type = 'R'   # Read response
            elif 'resp' in field_names and 'data' not in field_names:
                self._channel_type = 'B'   # Write response
            else:
                self._channel_type = 'UNKNOWN'
                
        return self._channel_type

    def is_address_channel(self) -> bool:
        """Check if this is an address channel (AW or AR)."""
        return self.get_channel_type() in ['AW', 'AR']

    def is_data_channel(self) -> bool:
        """Check if this is a data channel (W or R).""" 
        return self.get_channel_type() in ['W', 'R']

    def is_response_channel(self) -> bool:
        """Check if this is a response channel (B or R)."""
        return self.get_channel_type() in ['B', 'R']

    def get_address(self) -> Optional[int]:
        """Get address for address channels."""
        return getattr(self, 'addr', None)

    def get_data(self) -> Optional[int]:
        """Get data for data/response channels."""
        return getattr(self, 'data', None)

    def get_response(self) -> Optional[int]:
        """Get response code for response channels."""
        return getattr(self, 'resp', None)

    def get_response_info(self) -> Dict[str, Any]:
        """
        Get response information for response channels.
        
        Returns:
            Dictionary with response details
        """
        if not self.is_response_channel():
            return {}
            
        resp_code = self.get_response()
        resp_names = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        
        return {
            'response_code': resp_code,
            'response_name': resp_names.get(resp_code, "UNKNOWN"),
            'is_error': resp_code >= 2,
            'data': self.get_data()
        }

    def validate_axil4_protocol(self) -> Tuple[bool, str]:
        """
        Validate AXIL4 protocol compliance.
        
        Returns:
            Tuple of (is_valid, error_message)
        """
        channel = self.get_channel_type()
        
        if channel == 'UNKNOWN':
            return False, "Unknown channel type"
        
        # AXIL4 always single transfer - no validation needed for burst fields
        # since they don't exist in AXIL4
        
        # Validate address alignment for address channels
        if self.is_address_channel():
            addr = self.get_address()
            if addr is not None and addr % 4 != 0:
                return False, f"Address 0x{addr:X} is not word-aligned"
        
        # Validate response codes
        if self.is_response_channel():
            resp = self.get_response()
            if resp is not None and resp > 3:
                return False, f"Invalid response code: {resp}"
        
        # Validate strobe signals for W channel
        if channel == 'W':
            strb = getattr(self, 'strb', None)
            if strb is not None:
                data_bytes = self.field_config.get_field_definition('data').bits // 8
                max_strb = (1 << data_bytes) - 1
                if strb > max_strb:
                    return False, f"Invalid strobe pattern: 0x{strb:X} for {data_bytes}-byte data"
        
        return True, "Valid AXIL4 packet"

    def __str__(self) -> str:
        """String representation of AXIL4 packet."""
        channel = self.get_channel_type()
        parts = [f"AXIL4{channel}"]
        
        # Add key fields based on channel type
        if self.is_address_channel():
            addr = self.get_address()
            if addr is not None:
                parts.append(f"addr=0x{addr:08X}")
        
        if self.is_data_channel() or self.is_response_channel():
            data = self.get_data()
            if data is not None:
                parts.append(f"data=0x{data:08X}")
        
        if self.is_response_channel():
            resp = self.get_response()
            if resp is not None:
                resp_names = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
                parts.append(f"resp={resp_names.get(resp, resp)}")
        
        return f"<{' '.join(parts)}>"


# Example usage and testing
if __name__ == "__main__":
    print("AXIL4 Packet Implementation Testing")
    print("=" * 50)
    
    # Test AW packet
    aw_packet = AXIL4Packet.create_aw_packet(addr=0x1000, prot=0)
    print(f"AW Packet: {aw_packet}")
    print(f"Channel Type: {aw_packet.get_channel_type()}")
    print(f"Address: 0x{aw_packet.get_address():08X}")
    
    # Test validation
    is_valid, error_msg = aw_packet.validate_axil4_protocol()
    print(f"Validation: {is_valid}, Message: {error_msg}")
    
    # Test W packet
    w_packet = AXIL4Packet.create_w_packet(data=0xDEADBEEF, strb=0xF)
    print(f"\nW Packet: {w_packet}")
    print(f"Data: 0x{w_packet.get_data():08X}")
    
    # Test R packet
    r_packet = AXIL4Packet.create_r_packet(data=0x12345678, resp=0)
    print(f"\nR Packet: {r_packet}")
    print(f"Response Info: {r_packet.get_response_info()}")
    
    # Test B packet
    b_packet = AXIL4Packet.create_b_packet(resp=2)  # SLVERR
    print(f"\nB Packet: {b_packet}")
    print(f"Response Info: {b_packet.get_response_info()}")
    
    # Test AR packet
    ar_packet = AXIL4Packet.create_ar_packet(addr=0x2000, prot=0)
    print(f"\nAR Packet: {ar_packet}")
    
    print("\nAll AXIL4 packets created successfully!")
    print("Key differences from AXI4:")
    print("  - No ID fields in any channel")
    print("  - No burst-related fields")
    print("  - Always single transfer operations")
    print("  - Simplified field sets for register access")
