# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi4_packet_utils
# Purpose: AXI4 Packet Utilities - FIXED to use generic field names consistently
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Packet Utilities - FIXED to use generic field names consistently

Simple utility functions for creating AXI4 packets that use generic field names
(addr, id, len, data, etc.) which match the field configuration. The pkt_prefix
parameter in GAXI components handles the AXI4 signal mapping.
"""

from typing import Dict, Any, Optional, Tuple
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet
from CocoTBFramework.components.axi4.axi4_field_configs import AXI4FieldConfigHelper


def create_simple_read_packet(address: int, id_val: int = 0, burst_len: int = 1,
                            size: int = 2, burst_type: int = 1, **kwargs) -> AXI4Packet:
    """
    Create a simple AR (Address Read) packet using generic field names.

    Args:
        address: Read address
        id_val: Transaction ID
        burst_len: Burst length (1-256)
        size: Transfer size (log2 of bytes per beat)
        burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)
        **kwargs: Additional fields

    Returns:
        AXI4Packet configured for AR channel
    """
    # Create AR field configuration
    ar_config = AXI4FieldConfigHelper.create_ar_field_config()

    # Create packet with AR fields
    packet = AXI4Packet(ar_config)

    # Set basic fields using GENERIC field names
    packet.id = id_val                    # FIXED: was arid
    packet.addr = address                 # FIXED: was araddr
    packet.len = burst_len - 1           # FIXED: was arlen (AXI4 uses length-1 encoding)
    packet.size = size                    # Generic field name (was arsize)
    packet.burst = burst_type             # FIXED: was arburst

    # Set default values for other fields using generic names
    packet.lock = kwargs.get('lock', 0)       # FIXED: was arlock
    packet.cache = kwargs.get('cache', 0)     # FIXED: was arcache
    packet.prot = kwargs.get('prot', 0)       # FIXED: was arprot
    packet.qos = kwargs.get('qos', 0)         # FIXED: was arqos
    packet.region = kwargs.get('region', 0)   # FIXED: was arregion

    # Set user field if present using generic name
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)   # FIXED: was aruser

    return packet


def create_simple_write_address_packet(address: int, id_val: int = 0, burst_len: int = 1,
                                    size: int = 2, burst_type: int = 1, **kwargs) -> AXI4Packet:
    """
    Create a simple AW (Address Write) packet using generic field names.

    Args:
        address: Write address
        id_val: Transaction ID
        burst_len: Burst length (1-256)
        size: Transfer size (log2 of bytes per beat)
        burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)
        **kwargs: Additional fields

    Returns:
        AXI4Packet configured for AW channel
    """
    # Create AW field configuration
    aw_config = AXI4FieldConfigHelper.create_aw_field_config()

    # Create packet with AW fields
    packet = AXI4Packet(aw_config)

    # Set basic fields using GENERIC field names
    packet.id = id_val                    # FIXED: was awid
    packet.addr = address                 # FIXED: was awaddr
    packet.len = burst_len - 1           # FIXED: was awlen (AXI4 uses length-1 encoding)
    packet.size = size                    # Generic field name (was awsize)
    packet.burst = burst_type             # FIXED: was awburst

    # Set default values for other fields using generic names
    packet.lock = kwargs.get('lock', 0)       # FIXED: was awlock
    packet.cache = kwargs.get('cache', 0)     # FIXED: was awcache
    packet.prot = kwargs.get('prot', 0)       # FIXED: was awprot
    packet.qos = kwargs.get('qos', 0)         # FIXED: was awqos
    packet.region = kwargs.get('region', 0)   # FIXED: was awregion

    # Set user field if present using generic name
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)   # FIXED: was awuser

    return packet


def create_simple_write_data_packet(data: int, last: bool = True, strb: Optional[int] = None,
                                data_width: int = 32, **kwargs) -> AXI4Packet:
    """
    Create a simple W (Write Data) packet using generic field names.

    Args:
        data: Write data value
        last: Whether this is the last beat in the burst
        strb: Write strobes (None = all bytes enabled)
        data_width: Data width for strobe calculation
        **kwargs: Additional fields

    Returns:
        AXI4Packet configured for W channel
    """
    # Create W field configuration
    w_config = AXI4FieldConfigHelper.create_w_field_config(data_width)

    # Create packet
    packet = AXI4Packet(w_config)

    # Set fields using GENERIC field names
    packet.data = data                        # FIXED: was wdata
    packet.last = 1 if last else 0          # FIXED: was wlast

    # Calculate default strobe if not provided
    if strb is None:
        strb_width = data_width // 8
        strb = (1 << strb_width) - 1  # All bytes enabled

    packet.strb = strb                       # FIXED: was wstrb

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)  # FIXED: was wuser

    return packet


def create_simple_read_response_packet(data: int, resp: int = 0, last: bool = True,
                                    id_val: int = 0, data_width: int = 32, **kwargs) -> AXI4Packet:
    """
    Create a simple R (Read Response) packet using generic field names.

    Args:
        data: Read data value
        resp: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
        last: Whether this is the last beat in the burst
        id_val: Transaction ID (must match AR ID)
        data_width: Data width
        **kwargs: Additional fields

    Returns:
        AXI4Packet configured for R channel
    """
    # Create R field configuration
    r_config = AXI4FieldConfigHelper.create_r_field_config(data_width=data_width)

    # Create packet
    packet = AXI4Packet(r_config)

    # Set fields using GENERIC field names
    packet.id = id_val                       # FIXED: was rid
    packet.data = data                       # FIXED: was rdata
    packet.resp = resp                       # FIXED: was rresp
    packet.last = 1 if last else 0         # FIXED: was rlast

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)  # FIXED: was ruser

    return packet


def create_simple_write_response_packet(resp: int = 0, id_val: int = 0, **kwargs) -> AXI4Packet:
    """
    Create a simple B (Write Response) packet using generic field names.

    Args:
        resp: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
        id_val: Transaction ID (must match AW ID)
        **kwargs: Additional fields

    Returns:
        AXI4Packet configured for B channel
    """
    # Create B field configuration
    b_config = AXI4FieldConfigHelper.create_b_field_config()

    # Create packet
    packet = AXI4Packet(b_config)

    # Set fields using GENERIC field names
    packet.id = id_val                       # FIXED: was bid
    packet.resp = resp                       # FIXED: was bresp

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)  # FIXED: was buser

    return packet


# Convenience functions for common packet patterns

def create_simple_write_packets(id_val: int, addr: int, data: int,
                            id_width: int = 8, addr_width: int = 32,
                            data_width: int = 32) -> Tuple[AXI4Packet, AXI4Packet]:
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
    # Create AW packet using generic field names
    aw_packet = create_simple_write_address_packet(
        address=addr,
        id_val=id_val,
        burst_len=1,    # Single beat
        size=2,         # 4 bytes
        burst_type=1    # INCR
    )

    # Create W packet using generic field names
    w_packet = create_simple_write_data_packet(
        data=data,
        last=True,      # Single beat, so it's last
        data_width=data_width
    )

    return aw_packet, w_packet


def create_burst_write_packets(id_val: int, start_addr: int, data_list: list,
                            size: int = 2, burst_type: int = 1) -> Tuple[AXI4Packet, list]:
    """
    Create AW and multiple W packets for a burst write using generic field names.

    Args:
        id_val: Write ID
        start_addr: Starting address
        data_list: List of data values for each beat
        size: Transfer size (log2 of bytes per beat)
        burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)

    Returns:
        Tuple of (aw_packet, w_packet_list)
    """
    burst_len = len(data_list)

    # Create AW packet
    aw_packet = create_simple_write_address_packet(
        address=start_addr,
        id_val=id_val,
        burst_len=burst_len,
        size=size,
        burst_type=burst_type
    )

    # Create W packets
    w_packets = []
    for i, data in enumerate(data_list):
        is_last = (i == burst_len - 1)
        w_packet = create_simple_write_data_packet(
            data=data,
            last=is_last
        )
        w_packets.append(w_packet)

    return aw_packet, w_packets


def create_burst_read_response_packets(id_val: int, data_list: list,
                                    resp: int = 0) -> list:
    """
    Create multiple R packets for a burst read response using generic field names.

    Args:
        id_val: Transaction ID (must match AR ID)
        data_list: List of data values for each beat
        resp: Response code for all beats

    Returns:
        List of R packets
    """
    r_packets = []
    burst_len = len(data_list)

    for i, data in enumerate(data_list):
        is_last = (i == burst_len - 1)
        r_packet = create_simple_read_response_packet(
            data=data,
            resp=resp,
            last=is_last,
            id_val=id_val
        )
        r_packets.append(r_packet)

    return r_packets


# Example usage and testing
if __name__ == "__main__":
    print("AXI4 Packet Utilities - FIXED Generic Field Names Testing")
    print("=" * 70)

    # Test AR packet creation
    ar_packet = create_simple_read_packet(address=0x1000, id_val=5, burst_len=4)
    print(f"AR Packet: addr=0x{ar_packet.addr:X}, id={ar_packet.id}, len={ar_packet.len}")

    # Test AW packet creation
    aw_packet = create_simple_write_address_packet(address=0x2000, id_val=3, burst_len=2)
    print(f"AW Packet: addr=0x{aw_packet.addr:X}, id={aw_packet.id}, len={aw_packet.len}")

    # Test W packet creation
    w_packet = create_simple_write_data_packet(data=0xDEADBEEF, last=True)
    print(f"W Packet: data=0x{w_packet.data:X}, last={w_packet.last}, strb=0x{w_packet.strb:X}")

    # Test R packet creation
    r_packet = create_simple_read_response_packet(data=0x12345678, id_val=5)
    print(f"R Packet: data=0x{r_packet.data:X}, id={r_packet.id}, resp={r_packet.resp}, last={r_packet.last}")

    # Test B packet creation
    b_packet = create_simple_write_response_packet(resp=0, id_val=3)
    print(f"B Packet: id={b_packet.id}, resp={b_packet.resp}")

    # Test convenience functions
    print("\nTesting convenience functions:")
    aw, w = create_simple_write_packets(1, 0x3000, 0xCAFEBABE)
    print(f"Simple Write - AW: addr=0x{aw.addr:X}, id={aw.id}")
    print(f"Simple Write - W: data=0x{w.data:X}, last={w.last}")

    # Test burst packets
    aw_burst, w_list = create_burst_write_packets(2, 0x4000, [0x11111111, 0x22222222, 0x33333333])
    print(f"Burst Write - AW: addr=0x{aw_burst.addr:X}, id={aw_burst.id}, len={aw_burst.len}")
    print(f"Burst Write - W packets: {len(w_list)} beats")

    r_list = create_burst_read_response_packets(7, [0xAAAAAAAA, 0xBBBBBBBB])
    print(f"Burst Read Response: {len(r_list)} R packets, first data=0x{r_list[0].data:X}")

    print("\nAll packets created successfully using generic field names!")
    print("The pkt_prefix parameter in GAXI components will handle AXI4 signal mapping.")
