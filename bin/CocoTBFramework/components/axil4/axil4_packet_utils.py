# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axil4_packet_utils
# Purpose: AXIL4 (AXI4-Lite) Packet Utilities
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 (AXI4-Lite) Packet Utilities

Simple utility functions for creating AXIL4 packets that use generic field names
(addr, data, resp, etc.) which match the field configuration. The pkt_prefix
parameter in GAXI components handles the AXIL4 signal mapping.

Key differences from AXI4:
- No ID fields in any utilities
- No burst-related utilities (always single transfer)
- Simplified field sets for register access

Note: Maintains function parity with AXI4 utilities where applicable for compatibility.
"""

from typing import Dict, Any, Optional, Tuple
from CocoTBFramework.components.axil4.axil4_packet import AXIL4Packet
from CocoTBFramework.components.axil4.axil4_field_configs import AXIL4FieldConfigHelper


def create_simple_read_packet(address: int, prot: int = 0, **kwargs) -> AXIL4Packet:
    """
    Create a simple AR (Address Read) packet for register access.
    
    Note: This function provides compatibility with AXI4 packet utilities.
    In AXIL4, there are no burst parameters (len, size, burst_type).

    Args:
        address: Read address
        prot: Protection type (default: 0)
        **kwargs: Additional fields (user, etc.)

    Returns:
        AXIL4Packet configured for AR channel
    """
    # Create AR field configuration
    ar_config = AXIL4FieldConfigHelper.create_ar_field_config()

    # Create packet with AR fields
    packet = AXIL4Packet(ar_config)

    # Set fields using generic field names
    packet.addr = address
    packet.prot = prot

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_write_address_packet(address: int, prot: int = 0, **kwargs) -> AXIL4Packet:
    """
    Create a simple AW (Address Write) packet for register access.

    Args:
        address: Write address
        prot: Protection type (default: 0)
        **kwargs: Additional fields (user, etc.)

    Returns:
        AXIL4Packet configured for AW channel
    """
    # Create AW field configuration
    aw_config = AXIL4FieldConfigHelper.create_aw_field_config()

    # Create packet
    packet = AXIL4Packet(aw_config)

    # Set fields using generic field names
    packet.addr = address
    packet.prot = prot

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_write_data_packet(data: int, strb: Optional[int] = None, 
                                  data_width: int = 32, **kwargs) -> AXIL4Packet:
    """
    Create a simple W (Write Data) packet for register access.

    Args:
        data: Write data value
        strb: Write strobes (None = all bytes enabled)
        data_width: Data width for strobe calculation
        **kwargs: Additional fields (user, etc.)

    Returns:
        AXIL4Packet configured for W channel
    """
    # Create W field configuration
    w_config = AXIL4FieldConfigHelper.create_w_field_config(data_width)

    # Create packet
    packet = AXIL4Packet(w_config)

    # Set fields using generic field names
    packet.data = data

    # Calculate default strobe if not provided
    if strb is None:
        strb_width = data_width // 8
        strb = (1 << strb_width) - 1  # All bytes enabled

    packet.strb = strb

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_read_response_packet(data: int, resp: int = 0, 
                                     data_width: int = 32, **kwargs) -> AXIL4Packet:
    """
    Create a simple R (Read Response) packet for register access.

    Args:
        data: Read data value
        resp: Response code (0=OKAY, 2=SLVERR, 3=DECERR)
        data_width: Data width
        **kwargs: Additional fields (user, etc.)

    Returns:
        AXIL4Packet configured for R channel
    """
    # Create R field configuration
    r_config = AXIL4FieldConfigHelper.create_r_field_config(data_width)

    # Create packet
    packet = AXIL4Packet(r_config)

    # Set fields using generic field names
    packet.data = data
    packet.resp = resp

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_write_response_packet(resp: int = 0, **kwargs) -> AXIL4Packet:
    """
    Create a simple B (Write Response) packet for register access.

    Args:
        resp: Response code (0=OKAY, 2=SLVERR, 3=DECERR)
        **kwargs: Additional fields (user, etc.)

    Returns:
        AXIL4Packet configured for B channel
    """
    # Create B field configuration
    b_config = AXIL4FieldConfigHelper.create_b_field_config()

    # Create packet
    packet = AXIL4Packet(b_config)

    # Set fields using generic field names
    packet.resp = resp

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_register_write(address: int, data: int, strb: Optional[int] = None,
                               prot: int = 0, data_width: int = 32) -> Tuple[AXIL4Packet, AXIL4Packet]:
    """
    Create AW and W packets for a simple register write.

    Args:
        address: Register address
        data: Register value
        strb: Write strobes (None = all bytes)
        prot: Protection type
        data_width: Data width

    Returns:
        Tuple of (aw_packet, w_packet)
    """
    aw_packet = create_simple_write_address_packet(address, prot)
    w_packet = create_simple_write_data_packet(data, strb, data_width)
    return aw_packet, w_packet


def create_simple_register_read(address: int, prot: int = 0) -> AXIL4Packet:
    """
    Create AR packet for a simple register read.

    Args:
        address: Register address
        prot: Protection type

    Returns:
        AR packet for register read
    """
    return create_simple_read_packet(address, prot)


def create_register_response_packets(read_data: Optional[int] = None, write_resp: Optional[int] = None,
                                   data_width: int = 32) -> Dict[str, AXIL4Packet]:
    """
    Create response packets for register operations.

    Args:
        read_data: Data for R packet (None to skip)
        write_resp: Response for B packet (None to skip)
        data_width: Data width for R packet

    Returns:
        Dictionary with 'R' and/or 'B' packets
    """
    packets = {}
    
    if read_data is not None:
        packets['R'] = create_simple_read_response_packet(read_data, 0, data_width)
    
    if write_resp is not None:
        packets['B'] = create_simple_write_response_packet(write_resp)
    
    return packets


def create_error_response_packets(error_type: str = "SLVERR", 
                                data_width: int = 32) -> Dict[str, AXIL4Packet]:
    """
    Create error response packets for testing.

    Args:
        error_type: "SLVERR" or "DECERR"
        data_width: Data width for R packet

    Returns:
        Dictionary with error response packets
    """
    resp_codes = {"OKAY": 0, "EXOKAY": 1, "SLVERR": 2, "DECERR": 3}
    resp_code = resp_codes.get(error_type.upper(), 2)  # Default to SLVERR
    
    return {
        'R': create_simple_read_response_packet(0xDEADDEAD, resp_code, data_width),
        'B': create_simple_write_response_packet(resp_code)
    }


def validate_axil4_address_alignment(address: int, data_width: int = 32) -> Tuple[bool, str]:
    """
    Validate AXIL4 address alignment requirements.

    Args:
        address: Address to validate
        data_width: Data width in bits

    Returns:
        Tuple of (is_valid, error_message)
    """
    bytes_per_transfer = data_width // 8
    
    if address % bytes_per_transfer != 0:
        return False, f"Address 0x{address:X} not aligned to {bytes_per_transfer}-byte boundary"
    
    return True, "Address properly aligned"


def create_axil4_register_map_packets(register_map: Dict[int, int], 
                                    data_width: int = 32) -> Dict[int, AXIL4Packet]:
    """
    Create R response packets for a register map.

    Args:
        register_map: Dictionary mapping addresses to data values
        data_width: Data width

    Returns:
        Dictionary mapping addresses to R packets
    """
    packets = {}
    
    for addr, data in register_map.items():
        packets[addr] = create_simple_read_response_packet(data, 0, data_width)
    
    return packets


def create_strobe_patterns(data_width: int = 32) -> Dict[str, int]:
    """
    Create common write strobe patterns for testing.

    Args:
        data_width: Data width in bits

    Returns:
        Dictionary of named strobe patterns
    """
    strb_width = data_width // 8
    max_strb = (1 << strb_width) - 1
    
    patterns = {
        'all_bytes': max_strb,
        'no_bytes': 0,
        'byte0_only': 0x1,
        'byte1_only': 0x2 if strb_width > 1 else 0,
        'lower_half': (1 << (strb_width // 2)) - 1,
        'upper_half': max_strb ^ ((1 << (strb_width // 2)) - 1),
        'alternating': 0x5 if strb_width >= 4 else 0x1,
    }
    
    # Filter out invalid patterns for narrow data widths
    return {name: pattern for name, pattern in patterns.items() 
            if pattern <= max_strb and pattern >= 0}


# Utility functions for response codes (compatibility with AXI4 utils)

def get_response_name(resp_code: int) -> str:
    """Get human-readable name for AXIL4 response code."""
    resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
    return resp_names.get(resp_code, f'UNKNOWN(0x{resp_code:X})')


def is_error_response(resp_code: int) -> bool:
    """Check if response code indicates an error."""
    return resp_code >= 2  # SLVERR or DECERR


def is_okay_response(resp_code: int) -> bool:
    """Check if response code is OKAY."""
    return resp_code == 0


# Convenience functions for common packet patterns (compatibility with AXI4)

def create_simple_write_packets(address: int, data: int, strb: Optional[int] = None,
                               prot: int = 0, data_width: int = 32) -> Tuple[AXIL4Packet, AXIL4Packet]:
    """
    Create AW and W packets for a simple register write.
    
    Note: Provides compatibility with AXI4 create_simple_write_packets but without ID parameter.

    Args:
        address: Register address
        data: Register data
        strb: Write strobes (None = all bytes)
        prot: Protection type
        data_width: Data width

    Returns:
        Tuple of (aw_packet, w_packet)
    """
    return create_simple_register_write(address, data, strb, prot, data_width)


# Example usage and testing
if __name__ == "__main__":
    print("AXIL4 Packet Utilities Testing")
    print("=" * 40)

    # Test AR packet creation
    ar_packet = create_simple_read_packet(address=0x1000, prot=0)
    print(f"AR Packet: addr=0x{ar_packet.addr:X}, prot={ar_packet.prot}")

    # Test AW packet creation
    aw_packet = create_simple_write_address_packet(address=0x2000, prot=0)
    print(f"AW Packet: addr=0x{aw_packet.addr:X}, prot={aw_packet.prot}")

    # Test W packet creation
    w_packet = create_simple_write_data_packet(data=0xDEADBEEF, strb=0xF)
    print(f"W Packet: data=0x{w_packet.data:X}, strb=0x{w_packet.strb:X}")

    # Test R packet creation
    r_packet = create_simple_read_response_packet(data=0x12345678, resp=0)
    print(f"R Packet: data=0x{r_packet.data:X}, resp={r_packet.resp}")

    # Test B packet creation
    b_packet = create_simple_write_response_packet(resp=0)
    print(f"B Packet: resp={b_packet.resp}")

    # Test convenience functions
    print("\nTesting convenience functions:")
    aw, w = create_simple_register_write(0x3000, 0xCAFEBABE)
    print(f"Register Write - AW: addr=0x{aw.addr:X}")
    print(f"Register Write - W: data=0x{w.data:X}")

    ar = create_simple_register_read(0x4000)
    print(f"Register Read - AR: addr=0x{ar.addr:X}")

    # Test error packets
    error_packets = create_error_response_packets("SLVERR")
    print(f"\nError Packets:")
    print(f"Error R: resp={error_packets['R'].resp}, data=0x{error_packets['R'].data:X}")
    print(f"Error B: resp={error_packets['B'].resp}")

    # Test strobe patterns
    strobe_patterns = create_strobe_patterns(32)
    print(f"\nStrobe patterns for 32-bit data:")
    for name, pattern in strobe_patterns.items():
        print(f"  {name}: 0x{pattern:X}")

    # Test address validation
    is_valid, msg = validate_axil4_address_alignment(0x1000, 32)
    print(f"\nAddress validation (0x1000): {is_valid} - {msg}")
    
    is_valid, msg = validate_axil4_address_alignment(0x1002, 32)
    print(f"Address validation (0x1002): {is_valid} - {msg}")

    print("\nAll AXIL4 packets created successfully using generic field names!")
    print("Key differences from AXI4 utilities:")
    print("  - No ID fields in any utilities")
    print("  - No burst-related packet creation")
    print("  - Register-oriented convenience functions")
    print("  - Simplified field sets for single transfers")
    print("  - Address alignment validation for register access")
    print("  - Function parity with AXI4 utilities where applicable")
