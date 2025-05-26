"""
AXI4 Packet Classes (Optimized Version)

This module provides:
1. AXI4Packet class that extends optimized Packet class with AXI4-specific functionality
2. Factory methods for creating packets for each AXI4 channel
3. Protocol validation functions with performance optimizations
4. Caching of frequently accessed field information
"""

from CocoTBFramework.components.packet import Packet, _FIELD_CACHE
from .axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG, AXI4_W_FIELD_CONFIG, AXI4_B_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG, AXI4_R_FIELD_CONFIG
)


class AXI4Packet(Packet):
    """
    AXI4 Packet class that extends the optimized Packet base class with AXI4-specific methods.

    This class provides:
    - Specialized constructors for each AXI4 channel
    - Helper methods for working with AXI4 bursts
    - AXI4 protocol validation
    - Performance optimizations through caching
    """

    @classmethod
    def create_aw_packet(cls,
                        awid=0,
                        awaddr=0,
                        awlen=0,
                        awsize=0,
                        awburst=1,  # INCR
                        awlock=0,
                        awcache=0,
                        awprot=0,
                        awqos=0,
                        awregion=0,
                        awuser=0):
        """
        Create a Write Address (AW) channel packet.

        Args:
            awid: Write transaction ID
            awaddr: Write address
            awlen: Burst length (0 = 1 beat, 15 = 16 beats)
            awsize: Burst size (0 = 1 byte, 1 = 2 bytes, 2 = 4 bytes, etc.)
            awburst: Burst type (0 = FIXED, 1 = INCR, 2 = WRAP)
            awlock: Lock type (0 = Normal, 1 = Exclusive)
            awcache: Cache type
            awprot: Protection type
            awqos: Quality of Service
            awregion: Region identifier
            awuser: User signal

        Returns:
            AXI4Packet: Write address packet
        """
        # Create packet using FieldConfig
        packet = cls(AXI4_AW_FIELD_CONFIG)

        # Set field values (these will be automatically masked by the parent class)
        packet.awid = awid
        packet.awaddr = awaddr
        packet.awlen = awlen
        packet.awsize = awsize
        packet.awburst = awburst
        packet.awlock = awlock
        packet.awcache = awcache
        packet.awprot = awprot
        packet.awqos = awqos
        packet.awregion = awregion
        packet.awuser = awuser

        return packet

    @classmethod
    def create_w_packet(cls, wdata=0, wstrb=0xF, wlast=1, wuser=0):
        """
        Create a Write Data (W) channel packet.

        Args:
            wdata: Write data
            wstrb: Write strobe (byte enable)
            wlast: Last transfer in write burst
            wuser: User signal

        Returns:
            AXI4Packet: Write data packet
        """
        # Create packet using FieldConfig
        packet = cls(AXI4_W_FIELD_CONFIG)

        # Set field values (these will be automatically masked by the parent class)
        packet.wdata = wdata
        packet.wstrb = wstrb
        packet.wlast = wlast
        packet.wuser = wuser

        return packet

    @classmethod
    def create_b_packet(cls, bid=0, bresp=0, buser=0):
        """
        Create a Write Response (B) channel packet.

        Args:
            bid: Response ID
            bresp: Write response (0 = OKAY, 1 = EXOKAY, 2 = SLVERR, 3 = DECERR)
            buser: User signal

        Returns:
            AXI4Packet: Write response packet
        """
        # Create packet using FieldConfig
        packet = cls(AXI4_B_FIELD_CONFIG)

        # Set field values (these will be automatically masked by the parent class)
        packet.bid = bid
        packet.bresp = bresp
        packet.buser = buser

        return packet

    @classmethod
    def create_ar_packet(cls,
                        arid=0,
                        araddr=0,
                        arlen=0,
                        arsize=0,
                        arburst=1,  # INCR
                        arlock=0,
                        arcache=0,
                        arprot=0,
                        arqos=0,
                        arregion=0,
                        aruser=0):
        """
        Create a Read Address (AR) channel packet.

        Args:
            arid: Read transaction ID
            araddr: Read address
            arlen: Burst length (0 = 1 beat, 15 = 16 beats)
            arsize: Burst size (0 = 1 byte, 1 = 2 bytes, 2 = 4 bytes, etc.)
            arburst: Burst type (0 = FIXED, 1 = INCR, 2 = WRAP)
            arlock: Lock type (0 = Normal, 1 = Exclusive)
            arcache: Cache type
            arprot: Protection type
            arqos: Quality of Service
            arregion: Region identifier
            aruser: User signal

        Returns:
            AXI4Packet: Read address packet
        """
        # Create packet using FieldConfig
        packet = cls(AXI4_AR_FIELD_CONFIG)

        # Set field values (these will be automatically masked by the parent class)
        packet.arid = arid
        packet.araddr = araddr
        packet.arlen = arlen
        packet.arsize = arsize
        packet.arburst = arburst
        packet.arlock = arlock
        packet.arcache = arcache
        packet.arprot = arprot
        packet.arqos = arqos
        packet.arregion = arregion
        packet.aruser = aruser

        return packet

    @classmethod
    def create_r_packet(cls, rid=0, rdata=0, rresp=0, rlast=1, ruser=0):
        """
        Create a Read Data (R) channel packet.

        Args:
            rid: Read ID
            rdata: Read data
            rresp: Read response (0 = OKAY, 1 = EXOKAY, 2 = SLVERR, 3 = DECERR)
            rlast: Last transfer in read burst
            ruser: User signal

        Returns:
            AXI4Packet: Read data packet
        """
        # Create packet using FieldConfig
        packet = cls(AXI4_R_FIELD_CONFIG)

        # Set field values (these will be automatically masked by the parent class)
        packet.rid = rid
        packet.rdata = rdata
        packet.rresp = rresp
        packet.rlast = rlast
        packet.ruser = ruser

        return packet

    def validate_axi4_protocol(self):
        """
        Validates the packet against AXI4 protocol rules.
        Uses optimized caching for field lookups.

        Returns:
            tuple: (is_valid, error_message)
        """
        # Determine which channel this packet is for
        # Optimized implementation that checks existence of key fields efficiently
        if 'awid' in self.fields:
            return self._validate_aw_packet()
        elif 'wdata' in self.fields:
            return self._validate_w_packet()
        elif 'bid' in self.fields:
            return self._validate_b_packet()
        elif 'arid' in self.fields:
            return self._validate_ar_packet()
        elif 'rid' in self.fields:
            return self._validate_r_packet()
        else:
            return False, "Unknown AXI4 packet type"

    def _validate_aw_packet(self):
        """Validate Write Address channel packet using cached operations"""
        # Check address alignment based on size
        if 'awsize' in self.fields and 'awaddr' in self.fields:
            byte_count = 1 << self.fields['awsize']
            if self.fields['awaddr'] % byte_count != 0:
                return False, f"AW address 0x{self.fields['awaddr']:X} not aligned for size {self.fields['awsize']} ({byte_count} bytes)"

        # Check burst type
        if 'awburst' in self.fields:
            if self.fields['awburst'] not in [0, 1, 2]:  # FIXED, INCR, WRAP
                return False, f"Invalid AW burst type: {self.fields['awburst']}"

            # For WRAP bursts, check power-of-2 length
            if self.fields['awburst'] == 2 and 'awlen' in self.fields and (self.fields['awlen'] + 1) not in [2, 4, 8, 16]:
                return False, f"WRAP burst length must be 2, 4, 8, or 16 (awlen={self.fields['awlen']})"

        # Check burst length
        if 'awlen' in self.fields and self.fields['awlen'] > 255:
            return False, f"AW burst length exceeds AXI4 maximum: {self.fields['awlen']}"

        return True, "Valid AW packet"

    def _validate_w_packet(self):
        """Validate Write Data channel packet using cached operations"""
        # Validate strobe for enabled bytes
        if 'wstrb' in self.fields and self.fields['wstrb'] == 0:
            return False, "Write strobe is zero (no bytes enabled)"

        # Validate wlast field if present
        if 'wlast' in self.fields and not isinstance(self.fields['wlast'], int):
            return False, f"WLAST must be an integer: {self.fields['wlast']}"

        return True, "Valid W packet"

    def _validate_b_packet(self):
        """Validate Write Response channel packet using cached operations"""
        # Check response code
        if 'bresp' in self.fields and self.fields['bresp'] not in [0, 1, 2, 3]:
            return False, f"Invalid B response code: {self.fields['bresp']}"

        return True, "Valid B packet"

    def _validate_ar_packet(self):
        """Validate Read Address channel packet using cached operations"""
        # Check address alignment based on size
        if 'arsize' in self.fields and 'araddr' in self.fields:
            byte_count = 1 << self.fields['arsize']
            if self.fields['araddr'] % byte_count != 0:
                return False, f"AR address 0x{self.fields['araddr']:X} not aligned for size {self.fields['arsize']} ({byte_count} bytes)"

        # Check burst type
        if 'arburst' in self.fields:
            if self.fields['arburst'] not in [0, 1, 2]:  # FIXED, INCR, WRAP
                return False, f"Invalid AR burst type: {self.fields['arburst']}"

            # For WRAP bursts, check power-of-2 length
            if self.fields['arburst'] == 2 and 'arlen' in self.fields and (self.fields['arlen'] + 1) not in [2, 4, 8, 16]:
                return False, f"WRAP burst length must be 2, 4, 8, or 16 (arlen={self.fields['arlen']})"

        # Check burst length
        if 'arlen' in self.fields and self.fields['arlen'] > 255:
            return False, f"AR burst length exceeds AXI4 maximum: {self.fields['arlen']}"

        return True, "Valid AR packet"

    def _validate_r_packet(self):
        """Validate Read Data channel packet using cached operations"""
        # Check response code
        if 'rresp' in self.fields and self.fields['rresp'] not in [0, 1, 2, 3]:
            return False, f"Invalid R response code: {self.fields['rresp']}"

        # Validate rlast field if present
        if 'rlast' in self.fields and not isinstance(self.fields['rlast'], int):
            return False, f"RLAST must be an integer: {self.fields['rlast']}"

        return True, "Valid R packet"

    def get_burst_addresses(self):
        """
        Calculate all addresses in a burst sequence based on address, length, size, and burst type.
        Uses optimized field access and bit operations.

        Returns:
            list: List of addresses in the burst
        """
        # Determine if this is a read or write address packet
        is_read = 'araddr' in self.fields

        # Get the relevant fields using direct dictionary access for better performance
        if is_read:
            addr = self.fields['araddr']
            burst_len = self.fields['arlen']
            size = self.fields['arsize']
            burst_type = self.fields['arburst']
        else:
            addr = self.fields['awaddr']
            burst_len = self.fields['awlen']
            size = self.fields['awsize']
            burst_type = self.fields['awburst']

        # Calculate the byte count for this size using bit shift for performance
        byte_count = 1 << size

        # Pre-allocate the addresses list for better performance
        addresses = [0] * (burst_len + 1)
        current_addr = addr

        for i in range(burst_len + 1):
            addresses[i] = current_addr

            # Update address based on burst type
            if burst_type == 0:  # FIXED
                # Address remains the same for all beats
                pass
            elif burst_type == 1:  # INCR
                # Increment address by byte count
                current_addr += byte_count
            elif burst_type == 2:  # WRAP
                # Calculate the wrap boundary (align to burst size)
                wrap_size = (burst_len + 1) * byte_count
                wrap_mask = wrap_size - 1
                wrap_boundary = addr & ~wrap_mask

                # Increment address
                current_addr += byte_count

                # Check if we need to wrap
                if (current_addr & wrap_mask) == 0:
                    current_addr = wrap_boundary

        return addresses

# Helper functions for optimized performance

def validate_axi4_packet_cached(packet):
    """
    Validate an AXI4 packet against protocol rules with optimized caching.
    This is a standalone function that can be used without creating an instance.

    Args:
        packet: The packet to validate

    Returns:
        tuple: (is_valid, error_message)
    """
    # Determine which channel this packet is for based on field existence
    if hasattr(packet, 'awid'):
        return _validate_aw_packet_cached(packet)
    elif hasattr(packet, 'wdata'):
        return _validate_w_packet_cached(packet)
    elif hasattr(packet, 'bid'):
        return _validate_b_packet_cached(packet)
    elif hasattr(packet, 'arid'):
        return _validate_ar_packet_cached(packet)
    elif hasattr(packet, 'rid'):
        return _validate_r_packet_cached(packet)
    else:
        return False, "Unknown AXI4 packet type"

def _validate_aw_packet_cached(packet):
    """Validate Write Address channel packet with performance optimizations"""
    # Check address alignment based on size
    if hasattr(packet, 'awsize') and hasattr(packet, 'awaddr'):
        byte_count = 1 << packet.awsize
        if packet.awaddr % byte_count != 0:
            return False, f"AW address 0x{packet.awaddr:X} not aligned for size {packet.awsize} ({byte_count} bytes)"

    # Check burst type
    if hasattr(packet, 'awburst'):
        if packet.awburst not in [0, 1, 2]:  # FIXED, INCR, WRAP
            return False, f"Invalid AW burst type: {packet.awburst}"

        # For WRAP bursts, check power-of-2 length
        if packet.awburst == 2 and hasattr(packet, 'awlen') and (packet.awlen + 1) not in [2, 4, 8, 16]:
            return False, f"WRAP burst length must be 2, 4, 8, or 16 (awlen={packet.awlen})"

    # Check burst length
    if hasattr(packet, 'awlen') and packet.awlen > 255:
        return False, f"AW burst length exceeds AXI4 maximum: {packet.awlen}"

    return True, "Valid AW packet"

def _validate_w_packet_cached(packet):
    """Validate Write Data channel packet with performance optimizations"""
    # Validate strobe for enabled bytes
    if hasattr(packet, 'wstrb') and packet.wstrb == 0:
        return False, "Write strobe is zero (no bytes enabled)"

    # Validate wlast field if present
    if hasattr(packet, 'wlast') and not isinstance(packet.wlast, int):
        return False, f"WLAST must be an integer: {packet.wlast}"

    return True, "Valid W packet"

def _validate_b_packet_cached(packet):
    """Validate Write Response channel packet with performance optimizations"""
    # Check response code
    if hasattr(packet, 'bresp') and packet.bresp not in [0, 1, 2, 3]:
        return False, f"Invalid B response code: {packet.bresp}"

    return True, "Valid B packet"

def _validate_ar_packet_cached(packet):
    """Validate Read Address channel packet with performance optimizations"""
    # Check address alignment based on size
    if hasattr(packet, 'arsize') and hasattr(packet, 'araddr'):
        byte_count = 1 << packet.arsize
        if packet.araddr % byte_count != 0:
            return False, f"AR address 0x{packet.araddr:X} not aligned for size {packet.arsize} ({byte_count} bytes)"

    # Check burst type
    if hasattr(packet, 'arburst'):
        if packet.arburst not in [0, 1, 2]:  # FIXED, INCR, WRAP
            return False, f"Invalid AR burst type: {packet.arburst}"

        # For WRAP bursts, check power-of-2 length
        if packet.arburst == 2 and hasattr(packet, 'arlen') and (packet.arlen + 1) not in [2, 4, 8, 16]:
            return False, f"WRAP burst length must be 2, 4, 8, or 16 (arlen={packet.arlen})"

    # Check burst length
    if hasattr(packet, 'arlen') and packet.arlen > 255:
        return False, f"AR burst length exceeds AXI4 maximum: {packet.arlen}"

    return True, "Valid AR packet"

def _validate_r_packet_cached(packet):
    """Validate Read Data channel packet with performance optimizations"""
    # Check response code
    if hasattr(packet, 'rresp') and packet.rresp not in [0, 1, 2, 3]:
        return False, f"Invalid R response code: {packet.rresp}"

    # Validate rlast field if present
    if hasattr(packet, 'rlast') and not isinstance(packet.rlast, int):
        return False, f"RLAST must be an integer: {packet.rlast}"

    return True, "Valid R packet"

def get_burst_addresses_cached(packet):
    """
    Calculate all addresses in a burst sequence with optimized performance.
    This is a standalone function that can be used without creating an instance.

    Args:
        packet: The packet containing burst information

    Returns:
        list: List of addresses in the burst
    """
    # Determine if this is a read or write address packet
    is_read = hasattr(packet, 'araddr')

    # Get the relevant fields
    if is_read:
        addr = packet.araddr
        burst_len = packet.arlen
        size = packet.arsize
        burst_type = packet.arburst
    else:
        addr = packet.awaddr
        burst_len = packet.awlen
        size = packet.awsize
        burst_type = packet.awburst

    # Calculate the byte count for this size
    byte_count = 1 << size

    # Pre-allocate the addresses list for better performance
    addresses = [0] * (burst_len + 1)
    current_addr = addr

    for i in range(burst_len + 1):
        addresses[i] = current_addr

        # Update address based on burst type
        if burst_type == 1:
            # Increment address by byte count
            current_addr += byte_count
        elif burst_type == 2:
            # Calculate the wrap boundary (align to burst size)
            wrap_size = (burst_len + 1) * byte_count
            wrap_mask = wrap_size - 1
            wrap_boundary = addr & ~wrap_mask

            # Increment address
            current_addr += byte_count

            # Check if we need to wrap
            if (current_addr & wrap_mask) == 0:
                current_addr = wrap_boundary

    return addresses

# Performance monitoring function
def get_axi4_cache_stats():
    """
    Get statistics about the field cache performance.

    Returns:
        Dict with cache statistics
    """
    return _FIELD_CACHE.get_stats()

# Cache management function
def clear_axi4_cache():
    """Clear the field cache to free memory and reset statistics"""
    _FIELD_CACHE.clear()
