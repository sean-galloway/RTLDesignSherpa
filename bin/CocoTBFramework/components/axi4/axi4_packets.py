"""
AXI4 Packet Classes

This module provides:
1. AXI4Packet class that extends GAXIPacket with AXI4-specific functionality
2. Factory methods for creating packets for each AXI4 channel
3. Protocol validation functions
"""

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from .axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG,
    AXI4_W_FIELD_CONFIG,
    AXI4_B_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG,
    AXI4_R_FIELD_CONFIG
)


class AXI4Packet(GAXIPacket):
    """
    AXI4 Packet class that extends the base GAXIPacket with AXI4-specific methods.

    This class provides:
    - Specialized constructors for each AXI4 channel
    - Helper methods for working with AXI4 bursts
    - AXI4 protocol validation
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
        packet = cls(AXI4_AW_FIELD_CONFIG)
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

    def validate_axi4_protocol(self):
        """
        Validates the packet against AXI4 protocol rules.

        Returns:
            (bool, str): (is_valid, error_message)
        """
        # Determine which channel this packet is for
        if hasattr(self, 'awid'):
            return self._validate_aw_packet()
        elif hasattr(self, 'wdata'):
            return self._validate_w_packet()
        elif hasattr(self, 'bid'):
            return self._validate_b_packet()
        elif hasattr(self, 'arid'):
            return self._validate_ar_packet()
        elif hasattr(self, 'rid'):
            return self._validate_r_packet()
        else:
            return False, "Unknown AXI4 packet type"

    def _validate_aw_packet(self):
        """Validate Write Address channel packet"""
        # Check address alignment based on size
        if hasattr(self, 'awsize') and hasattr(self, 'awaddr'):
            byte_count = 1 << self.awsize
            if self.awaddr % byte_count != 0:
                return False, f"AW address 0x{self.awaddr:X} not aligned for size {self.awsize} ({byte_count} bytes)"

        # Check burst type
        if hasattr(self, 'awburst'):
            if self.awburst not in [0, 1, 2]:  # FIXED, INCR, WRAP
                return False, f"Invalid AW burst type: {self.awburst}"

            # For WRAP bursts, check power-of-2 length
            if self.awburst == 2 and hasattr(self, 'awlen') and (self.awlen + 1) not in [2, 4, 8, 16]:
                return False, f"WRAP burst length must be 2, 4, 8, or 16 (awlen={self.awlen})"

        # Check burst length
        if hasattr(self, 'awlen') and self.awlen > 255:
            return False, f"AW burst length exceeds AXI4 maximum: {self.awlen}"

        return True, "Valid AW packet"

    def _validate_w_packet(self):
        """Validate Write Data channel packet"""
        # Validate strobe for enabled bytes
        if hasattr(self, 'wstrb') and self.wstrb == 0:
            return False, "Write strobe is zero (no bytes enabled)"

        # Validate wlast field if present
        if hasattr(self, 'wlast') and not isinstance(self.wlast, int):
            return False, f"WLAST must be an integer: {self.wlast}"

        return True, "Valid W packet"

    def _validate_b_packet(self):
        """Validate Write Response channel packet"""
        # Check response code
        if hasattr(self, 'bresp') and self.bresp not in [0, 1, 2, 3]:
            return False, f"Invalid B response code: {self.bresp}"

        return True, "Valid B packet"

    def _validate_ar_packet(self):
        """Validate Read Address channel packet"""
        # Check address alignment based on size
        if hasattr(self, 'arsize') and hasattr(self, 'araddr'):
            byte_count = 1 << self.arsize
            if self.araddr % byte_count != 0:
                return False, f"AR address 0x{self.araddr:X} not aligned for size {self.arsize} ({byte_count} bytes)"

        # Check burst type
        if hasattr(self, 'arburst'):
            if self.arburst not in [0, 1, 2]:  # FIXED, INCR, WRAP
                return False, f"Invalid AR burst type: {self.arburst}"

            # For WRAP bursts, check power-of-2 length
            if self.arburst == 2 and hasattr(self, 'arlen') and (self.arlen + 1) not in [2, 4, 8, 16]:
                return False, f"WRAP burst length must be 2, 4, 8, or 16 (arlen={self.arlen})"

        # Check burst length
        if hasattr(self, 'arlen') and self.arlen > 255:
            return False, f"AR burst length exceeds AXI4 maximum: {self.arlen}"

        return True, "Valid AR packet"

    def _validate_r_packet(self):
        """Validate Read Data channel packet"""
        # Check response code
        if hasattr(self, 'rresp') and self.rresp not in [0, 1, 2, 3]:
            return False, f"Invalid R response code: {self.rresp}"

        # Validate rlast field if present
        if hasattr(self, 'rlast') and not isinstance(self.rlast, int):
            return False, f"RLAST must be an integer: {self.rlast}"

        return True, "Valid R packet"

    def get_burst_addresses(self):
        """
        Calculate all addresses in a burst sequence based on address, length, size, and burst type.

        Returns:
            list: List of addresses in the burst
        """
        # Determine if this is a read or write address packet
        is_read = hasattr(self, 'araddr')

        # Get the relevant fields
        if is_read:
            addr = self.araddr
            burst_len = self.arlen
            size = self.arsize
            burst_type = self.arburst
        else:
            addr = self.awaddr
            burst_len = self.awlen
            size = self.awsize
            burst_type = self.awburst

        # Calculate the byte count for this size
        byte_count = 1 << size

        # Calculate all addresses in the burst
        addresses = []
        current_addr = addr

        for _ in range(burst_len + 1):
            addresses.append(current_addr)

            if burst_type == 1:
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
        packet = cls(AXI4_W_FIELD_CONFIG)
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
        packet = cls(AXI4_B_FIELD_CONFIG)
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
        packet = cls(AXI4_AR_FIELD_CONFIG)
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
        packet = cls(AXI4_R_FIELD_CONFIG)
        packet.rid = rid
        packet.rdata = rdata
        packet.rresp = rresp
        packet.rlast = rlast
        packet.ruser = ruser
        return packet
