# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi5_packet_utils
# Purpose: AXI5 Packet Utilities - Helper functions for creating AXI5 packets.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Packet Utilities - Helper functions for creating AXI5 packets.

Simple utility functions for creating AXI5 packets that use generic field names
(addr, id, len, data, etc.) which match the field configuration. Includes
support for all AXI5-specific features.

AXI5-specific features supported:
- Atomic operations (ATOP)
- Memory Tagging Extension (MTE)
- MPAM, MECID, NSAID
- Chunked transfers
- Poison indicators
"""

from typing import Dict, Any, Optional, Tuple, List
from .axi5_packet import AXI5Packet
from .axi5_field_configs import AXI5FieldConfigHelper


def create_simple_read_packet(address: int, id_val: int = 0, burst_len: int = 1,
                              size: int = 2, burst_type: int = 1, **kwargs) -> AXI5Packet:
    """
    Create a simple AR (Address Read) packet using generic field names.

    Args:
        address: Read address
        id_val: Transaction ID
        burst_len: Burst length (1-256)
        size: Transfer size (log2 of bytes per beat)
        burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)
        **kwargs: Additional fields (nsaid, trace, mpam, mecid, chunken, tagop, etc.)

    Returns:
        AXI5Packet configured for AR channel
    """
    # Create AR field configuration
    ar_config = AXI5FieldConfigHelper.create_ar_field_config()

    # Create packet with AR fields
    packet = AXI5Packet(ar_config)

    # Set basic fields using GENERIC field names
    packet.id = id_val
    packet.addr = address
    packet.len = burst_len - 1  # AXI5 uses length-1 encoding
    packet.size = size
    packet.burst = burst_type

    # Set default values for other fields
    packet.lock = kwargs.get('lock', 0)
    packet.cache = kwargs.get('cache', 0)
    packet.prot = kwargs.get('prot', 0)
    packet.qos = kwargs.get('qos', 0)

    # AXI5-specific fields
    packet.nsaid = kwargs.get('nsaid', 0)
    packet.trace = kwargs.get('trace', 0)
    packet.mpam = kwargs.get('mpam', 0)
    packet.mecid = kwargs.get('mecid', 0)
    packet.unique = kwargs.get('unique', 0)
    packet.chunken = kwargs.get('chunken', 0)
    packet.tagop = kwargs.get('tagop', 0)

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_write_address_packet(address: int, id_val: int = 0, burst_len: int = 1,
                                       size: int = 2, burst_type: int = 1, **kwargs) -> AXI5Packet:
    """
    Create a simple AW (Address Write) packet using generic field names.

    Args:
        address: Write address
        id_val: Transaction ID
        burst_len: Burst length (1-256)
        size: Transfer size (log2 of bytes per beat)
        burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)
        **kwargs: Additional fields (atop, nsaid, trace, mpam, mecid, tagop, tag, etc.)

    Returns:
        AXI5Packet configured for AW channel
    """
    # Create AW field configuration
    aw_config = AXI5FieldConfigHelper.create_aw_field_config()

    # Create packet with AW fields
    packet = AXI5Packet(aw_config)

    # Set basic fields using GENERIC field names
    packet.id = id_val
    packet.addr = address
    packet.len = burst_len - 1  # AXI5 uses length-1 encoding
    packet.size = size
    packet.burst = burst_type

    # Set default values for other fields
    packet.lock = kwargs.get('lock', 0)
    packet.cache = kwargs.get('cache', 0)
    packet.prot = kwargs.get('prot', 0)
    packet.qos = kwargs.get('qos', 0)

    # AXI5-specific fields
    packet.atop = kwargs.get('atop', 0)
    packet.nsaid = kwargs.get('nsaid', 0)
    packet.trace = kwargs.get('trace', 0)
    packet.mpam = kwargs.get('mpam', 0)
    packet.mecid = kwargs.get('mecid', 0)
    packet.unique = kwargs.get('unique', 0)
    packet.tagop = kwargs.get('tagop', 0)
    packet.tag = kwargs.get('tag', 0)

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_write_data_packet(data: int, last: bool = True, strb: Optional[int] = None,
                                    data_width: int = 32, **kwargs) -> AXI5Packet:
    """
    Create a simple W (Write Data) packet using generic field names.

    Args:
        data: Write data value
        last: Whether this is the last beat in the burst
        strb: Write strobes (None = all bytes enabled)
        data_width: Data width for strobe calculation
        **kwargs: Additional fields (poison, tag, tagupdate, etc.)

    Returns:
        AXI5Packet configured for W channel
    """
    # Create W field configuration
    w_config = AXI5FieldConfigHelper.create_w_field_config(data_width)

    # Create packet
    packet = AXI5Packet(w_config)

    # Set fields using GENERIC field names
    packet.data = data
    packet.last = 1 if last else 0

    # Calculate default strobe if not provided
    if strb is None:
        strb_width = data_width // 8
        strb = (1 << strb_width) - 1  # All bytes enabled

    packet.strb = strb

    # AXI5-specific fields
    packet.poison = kwargs.get('poison', 0)
    packet.tag = kwargs.get('tag', 0)
    packet.tagupdate = kwargs.get('tagupdate', 0)

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_read_response_packet(data: int, resp: int = 0, last: bool = True,
                                       id_val: int = 0, data_width: int = 32, **kwargs) -> AXI5Packet:
    """
    Create a simple R (Read Response) packet using generic field names.

    Args:
        data: Read data value
        resp: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
        last: Whether this is the last beat in the burst
        id_val: Transaction ID (must match AR ID)
        data_width: Data width
        **kwargs: Additional fields (trace, poison, chunkv, chunknum, chunkstrb, tag, tagmatch)

    Returns:
        AXI5Packet configured for R channel
    """
    # Create R field configuration
    r_config = AXI5FieldConfigHelper.create_r_field_config(data_width=data_width)

    # Create packet
    packet = AXI5Packet(r_config)

    # Set fields using GENERIC field names
    packet.id = id_val
    packet.data = data
    packet.resp = resp
    packet.last = 1 if last else 0

    # AXI5-specific fields
    packet.trace = kwargs.get('trace', 0)
    packet.poison = kwargs.get('poison', 0)
    packet.chunkv = kwargs.get('chunkv', 0)
    packet.chunknum = kwargs.get('chunknum', 0)
    packet.chunkstrb = kwargs.get('chunkstrb', 0)
    packet.tag = kwargs.get('tag', 0)
    packet.tagmatch = kwargs.get('tagmatch', 0)

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


def create_simple_write_response_packet(resp: int = 0, id_val: int = 0, **kwargs) -> AXI5Packet:
    """
    Create a simple B (Write Response) packet using generic field names.

    Args:
        resp: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
        id_val: Transaction ID (must match AW ID)
        **kwargs: Additional fields (trace, tag, tagmatch)

    Returns:
        AXI5Packet configured for B channel
    """
    # Create B field configuration
    b_config = AXI5FieldConfigHelper.create_b_field_config()

    # Create packet
    packet = AXI5Packet(b_config)

    # Set fields using GENERIC field names
    packet.id = id_val
    packet.resp = resp

    # AXI5-specific fields
    packet.trace = kwargs.get('trace', 0)
    packet.tag = kwargs.get('tag', 0)
    packet.tagmatch = kwargs.get('tagmatch', 0)

    # Set user field if present
    if hasattr(packet, 'user'):
        packet.user = kwargs.get('user', 0)

    return packet


# Convenience functions for common packet patterns

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


def create_burst_write_packets(id_val: int, start_addr: int, data_list: List[int],
                               size: int = 2, burst_type: int = 1,
                               **kwargs) -> Tuple[AXI5Packet, List[AXI5Packet]]:
    """
    Create AW and multiple W packets for a burst write using generic field names.

    Args:
        id_val: Write ID
        start_addr: Starting address
        data_list: List of data values for each beat
        size: Transfer size (log2 of bytes per beat)
        burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)
        **kwargs: Additional AXI5 fields (atop, nsaid, trace, etc.)

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
        burst_type=burst_type,
        **kwargs
    )

    # Create W packets
    w_packets = []
    for i, data in enumerate(data_list):
        is_last = (i == burst_len - 1)
        w_packet = create_simple_write_data_packet(
            data=data,
            last=is_last,
            poison=kwargs.get('poison', 0),
            tag=kwargs.get('tag', 0),
            tagupdate=kwargs.get('tagupdate', 0)
        )
        w_packets.append(w_packet)

    return aw_packet, w_packets


def create_burst_read_response_packets(id_val: int, data_list: List[int],
                                       resp: int = 0, **kwargs) -> List[AXI5Packet]:
    """
    Create multiple R packets for a burst read response using generic field names.

    Args:
        id_val: Transaction ID (must match AR ID)
        data_list: List of data values for each beat
        resp: Response code for all beats
        **kwargs: Additional AXI5 fields (trace, poison, etc.)

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
            id_val=id_val,
            trace=kwargs.get('trace', 0),
            poison=kwargs.get('poison', 0),
            tag=kwargs.get('tag', 0),
            tagmatch=kwargs.get('tagmatch', 0)
        )
        r_packets.append(r_packet)

    return r_packets


# AXI5-specific packet creation functions

def create_atomic_transaction_packets(id_val: int, addr: int, data: int, atop: int,
                                      data_width: int = 32, **kwargs) -> Tuple[AXI5Packet, AXI5Packet]:
    """
    Create AW and W packets for an atomic operation.

    Args:
        id_val: Transaction ID
        addr: Target address
        data: Operand data
        atop: Atomic operation type
              - 0x10: AtomicStore
              - 0x20: AtomicLoad
              - 0x30: AtomicSwap
              - 0x31: AtomicCompare
        data_width: Data width
        **kwargs: Additional AXI5 fields

    Returns:
        Tuple of (aw_packet, w_packet)
    """
    aw_packet = create_simple_write_address_packet(
        address=addr,
        id_val=id_val,
        burst_len=1,
        atop=atop,
        **kwargs
    )

    w_packet = create_simple_write_data_packet(
        data=data,
        last=True,
        data_width=data_width
    )

    return aw_packet, w_packet


def create_tagged_write_packets(id_val: int, addr: int, data_list: List[int],
                                tag: int, tagop: int,
                                data_width: int = 32, **kwargs) -> Tuple[AXI5Packet, List[AXI5Packet]]:
    """
    Create AW and W packets with Memory Tagging Extension support.

    Args:
        id_val: Transaction ID
        addr: Target address
        data_list: List of data values
        tag: Memory tag value
        tagop: Tag operation (0=Invalid, 1=Transfer, 2=Update, 3=Match)
        data_width: Data width
        **kwargs: Additional AXI5 fields

    Returns:
        Tuple of (aw_packet, w_packet_list)
    """
    burst_len = len(data_list)

    aw_packet = create_simple_write_address_packet(
        address=addr,
        id_val=id_val,
        burst_len=burst_len,
        tag=tag,
        tagop=tagop,
        **kwargs
    )

    # Calculate number of tags
    num_tags = max(1, data_width // 128)
    tagupdate_mask = (1 << num_tags) - 1 if tagop == 2 else 0  # Update all tags if Update operation

    w_packets = []
    for i, data in enumerate(data_list):
        is_last = (i == burst_len - 1)
        w_packet = create_simple_write_data_packet(
            data=data,
            last=is_last,
            data_width=data_width,
            tag=tag,
            tagupdate=tagupdate_mask
        )
        w_packets.append(w_packet)

    return aw_packet, w_packets


def create_tagged_read_packet(id_val: int, addr: int, burst_len: int = 1,
                              tagop: int = 1, **kwargs) -> AXI5Packet:
    """
    Create AR packet with Memory Tagging Extension support.

    Args:
        id_val: Transaction ID
        addr: Target address
        burst_len: Burst length
        tagop: Tag operation (0=Invalid, 1=Transfer, 2=Update, 3=Match)
        **kwargs: Additional AXI5 fields

    Returns:
        AR packet
    """
    return create_simple_read_packet(
        address=addr,
        id_val=id_val,
        burst_len=burst_len,
        tagop=tagop,
        **kwargs
    )


def create_chunked_read_packet(id_val: int, addr: int, burst_len: int = 1,
                               **kwargs) -> AXI5Packet:
    """
    Create AR packet with chunking enabled.

    Args:
        id_val: Transaction ID
        addr: Target address
        burst_len: Burst length
        **kwargs: Additional AXI5 fields

    Returns:
        AR packet with chunken=1
    """
    return create_simple_read_packet(
        address=addr,
        id_val=id_val,
        burst_len=burst_len,
        chunken=1,
        **kwargs
    )


def create_secure_write_packets(id_val: int, addr: int, data: int,
                                nsaid: int, mpam: int = 0, mecid: int = 0,
                                data_width: int = 32, **kwargs) -> Tuple[AXI5Packet, AXI5Packet]:
    """
    Create AW and W packets with security context.

    Args:
        id_val: Transaction ID
        addr: Target address
        data: Write data
        nsaid: Non-secure access ID
        mpam: Memory partitioning info
        mecid: Memory encryption context ID
        data_width: Data width
        **kwargs: Additional AXI5 fields

    Returns:
        Tuple of (aw_packet, w_packet)
    """
    aw_packet = create_simple_write_address_packet(
        address=addr,
        id_val=id_val,
        burst_len=1,
        nsaid=nsaid,
        mpam=mpam,
        mecid=mecid,
        **kwargs
    )

    w_packet = create_simple_write_data_packet(
        data=data,
        last=True,
        data_width=data_width
    )

    return aw_packet, w_packet


def create_traced_write_packets(id_val: int, addr: int, data: int,
                                data_width: int = 32, **kwargs) -> Tuple[AXI5Packet, AXI5Packet]:
    """
    Create AW and W packets with transaction tracing enabled.

    Args:
        id_val: Transaction ID
        addr: Target address
        data: Write data
        data_width: Data width
        **kwargs: Additional AXI5 fields

    Returns:
        Tuple of (aw_packet, w_packet) with trace=1
    """
    aw_packet = create_simple_write_address_packet(
        address=addr,
        id_val=id_val,
        burst_len=1,
        trace=1,
        **kwargs
    )

    w_packet = create_simple_write_data_packet(
        data=data,
        last=True,
        data_width=data_width
    )

    return aw_packet, w_packet


# Example usage and testing
if __name__ == "__main__":
    print("AXI5 Packet Utilities Testing")
    print("=" * 70)

    # Test AR packet creation
    ar_packet = create_simple_read_packet(address=0x1000, id_val=5, burst_len=4,
                                          nsaid=1, trace=1)
    print(f"AR Packet: addr=0x{ar_packet.addr:X}, id={ar_packet.id}, len={ar_packet.len}")
    print(f"  nsaid={ar_packet.nsaid}, trace={ar_packet.trace}")

    # Test AW packet creation
    aw_packet = create_simple_write_address_packet(address=0x2000, id_val=3, burst_len=2,
                                                   atop=0x30)
    print(f"\nAW Packet: addr=0x{aw_packet.addr:X}, id={aw_packet.id}, len={aw_packet.len}")
    print(f"  atop=0x{aw_packet.atop:02X}")

    # Test W packet creation
    w_packet = create_simple_write_data_packet(data=0xDEADBEEF, last=True, poison=0)
    print(f"\nW Packet: data=0x{w_packet.data:X}, last={w_packet.last}, poison={w_packet.poison}")

    # Test R packet creation
    r_packet = create_simple_read_response_packet(data=0x12345678, id_val=5, chunkv=1, chunknum=3)
    print(f"\nR Packet: data=0x{r_packet.data:X}, id={r_packet.id}")
    print(f"  chunkv={r_packet.chunkv}, chunknum={r_packet.chunknum}")

    # Test B packet creation
    b_packet = create_simple_write_response_packet(resp=0, id_val=3, tagmatch=1)
    print(f"\nB Packet: id={b_packet.id}, resp={b_packet.resp}, tagmatch={b_packet.tagmatch}")

    # Test atomic packets
    aw_atomic, w_atomic = create_atomic_transaction_packets(1, 0x3000, 0xCAFEBABE, atop=0x30)
    print(f"\nAtomic Write - AW: addr=0x{aw_atomic.addr:X}, atop=0x{aw_atomic.atop:02X}")

    # Test tagged packets
    aw_tagged, w_list = create_tagged_write_packets(2, 0x4000, [0x11111111, 0x22222222],
                                                    tag=0xA, tagop=2)
    print(f"\nTagged Write - AW: addr=0x{aw_tagged.addr:X}, tag={aw_tagged.tag}, tagop={aw_tagged.tagop}")
    print(f"Tagged Write - W packets: {len(w_list)} beats")

    # Test secure packets
    aw_secure, w_secure = create_secure_write_packets(3, 0x5000, 0xABCDEF01,
                                                      nsaid=2, mpam=0x100, mecid=0x1234)
    print(f"\nSecure Write - AW: nsaid={aw_secure.nsaid}, mpam={aw_secure.mpam}, mecid={aw_secure.mecid}")

    print("\nAll packets created successfully!")
