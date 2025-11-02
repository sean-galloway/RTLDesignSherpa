# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXISPacket
# Purpose: AXIS Packet - Stream protocol packet implementation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Packet - Stream protocol packet implementation

This module provides packet classes for AXI4-Stream protocol.
Inherits from base GAXIPacket to maintain consistency with the GAXI framework.
"""

from ..gaxi.gaxi_packet import GAXIPacket


class AXISPacket(GAXIPacket):
    """
    AXIS Packet class for AXI4-Stream protocol.
    
    Inherits all functionality from GAXIPacket while providing
    AXIS-specific convenience methods and field access.
    
    AXIS protocol uses a single T channel with:
    - data: Stream data payload
    - strb: Byte enables
    - last: End of packet/frame indicator
    - id: Stream identifier (optional)
    - dest: Destination routing (optional)
    - user: User-defined sideband data (optional)
    """

    def __init__(self, *args, **kwargs):
        """Initialize AXIS packet."""
        super().__init__(*args, **kwargs)
    
    # Convenience properties for AXIS-specific fields
    @property
    def data(self):
        """Get stream data."""
        return self.get_field_value('data', 0)
    
    @data.setter
    def data(self, value):
        """Set stream data."""
        self.set_field_value('data', value)
    
    @property
    def strb(self):
        """Get stream strobe (byte enables)."""
        return self.get_field_value('strb', 0)
    
    @strb.setter
    def strb(self, value):
        """Set stream strobe (byte enables)."""
        self.set_field_value('strb', value)
    
    @property
    def last(self):
        """Get stream last indicator."""
        return self.get_field_value('last', 0)
    
    @last.setter
    def last(self, value):
        """Set stream last indicator."""
        self.set_field_value('last', value)
    
    @property
    def id(self):
        """Get stream ID."""
        return self.get_field_value('id', 0)
    
    @id.setter
    def id(self, value):
        """Set stream ID."""
        self.set_field_value('id', value)
    
    @property
    def dest(self):
        """Get stream destination."""
        return self.get_field_value('dest', 0)
    
    @dest.setter
    def dest(self, value):
        """Set stream destination."""
        self.set_field_value('dest', value)
    
    @property
    def user(self):
        """Get user signal."""
        return self.get_field_value('user', 0)
    
    @user.setter
    def user(self, value):
        """Set user signal."""
        self.set_field_value('user', value)
    
    # AXIS-specific utility methods
    def is_last(self) -> bool:
        """Check if this is the last transfer in a packet/frame."""
        return bool(self.last)
    
    def is_first(self) -> bool:
        """Check if this is the first transfer in a packet/frame (for multi-beat packets)."""
        # In simple stream protocols, this is typically determined by context
        # Could be enhanced with additional state tracking if needed
        return True
    
    def get_byte_count(self) -> int:
        """
        Get number of valid bytes based on strobe signal.
        
        Returns:
            Number of valid bytes in this transfer
        """
        if not hasattr(self, '_fields') or 'strb' not in self._fields:
            return 0
        
        strb_value = self.strb
        return bin(strb_value).count('1')
    
    def get_data_bytes(self) -> list:
        """
        Get data as list of valid bytes based on strobe.
        
        Returns:
            List of valid byte values
        """
        data_value = self.data
        strb_value = self.strb
        
        data_bytes = []
        byte_pos = 0
        
        while strb_value > 0:
            if strb_value & 1:
                byte_val = (data_value >> (byte_pos * 8)) & 0xFF
                data_bytes.append(byte_val)
            strb_value >>= 1
            byte_pos += 1
        
        return data_bytes
    
    def set_data_bytes(self, byte_list: list):
        """
        Set data and strobe from list of bytes.
        
        Args:
            byte_list: List of byte values to pack into data field
        """
        data_value = 0
        strb_value = 0
        
        for i, byte_val in enumerate(byte_list):
            data_value |= (byte_val & 0xFF) << (i * 8)
            strb_value |= (1 << i)
        
        self.data = data_value
        self.strb = strb_value
    
    def __str__(self):
        """String representation of AXIS packet."""
        field_strs = []
        
        # Always show data and strb
        field_strs.append(f"data=0x{self.data:x}")
        field_strs.append(f"strb=0b{self.strb:b}")
        
        # Show last if it's set
        if self.last:
            field_strs.append(f"last={self.last}")
        
        # Show optional fields if they exist and are non-zero
        if hasattr(self, '_fields'):
            if 'id' in self._fields and self.id != 0:
                field_strs.append(f"id=0x{self.id:x}")
            if 'dest' in self._fields and self.dest != 0:
                field_strs.append(f"dest=0x{self.dest:x}")
            if 'user' in self._fields and self.user != 0:
                field_strs.append(f"user=0x{self.user:x}")
        
        return f"AXISPacket({', '.join(field_strs)})"
    
    def __repr__(self):
        """Detailed representation of AXIS packet."""
        return (f"AXISPacket(time={self.timestamp}, "
                f"data=0x{self.data:x}, strb=0b{self.strb:b}, "
                f"last={self.last}, bytes={self.get_byte_count()})")


# Factory function for creating AXIS packets
def create_axis_packet(data=0, strb=None, last=0, id=0, dest=0, user=0, 
                      field_config=None, **kwargs):
    """
    Factory function to create AXIS packets with field values.
    
    Args:
        data: Stream data value
        strb: Strobe value (if None, defaults to all bytes enabled)
        last: Last indicator
        id: Stream ID
        dest: Destination
        user: User signal
        field_config: Field configuration
        **kwargs: Additional packet parameters
    
    Returns:
        AXISPacket instance
    """
    packet = AXISPacket(field_config=field_config, **kwargs)
    
    # Set field values
    packet.data = data
    
    # Auto-generate strobe if not provided
    if strb is None and field_config and 'strb' in field_config:
        strb_bits = field_config['strb'].bits
        strb = (1 << strb_bits) - 1  # All bytes enabled
    
    if strb is not None:
        packet.strb = strb
    packet.last = last
    packet.id = id
    packet.dest = dest
    packet.user = user
    
    return packet
