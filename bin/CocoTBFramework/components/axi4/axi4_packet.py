"""
AXI4 Packet Implementation - Ground Up Design

This module provides the AXI4Packet class that extends the base Packet class
with AXI4-specific functionality, working seamlessly with the ground-up design approach.

Key Design Principles:
1. Extend base Packet class (not GAXIPacket - this is AXI4-specific)
2. Use AXI4FieldConfigHelper for field configurations
3. Simple factory methods for each channel type
4. AXI4 protocol validation built-in
5. Clean integration with AXI4Master packet creation
"""

from typing import Optional, Tuple, Dict, Any
from ..shared.packet import Packet
from .axi4_field_configs import AXI4FieldConfigHelper


class AXI4Packet(Packet):
    """
    AXI4 Packet class extending the optimized base Packet class.

    Provides AXI4-specific functionality while leveraging all the performance
    optimizations and field management from the base Packet class.
    """

    def __init__(self, field_config, **kwargs):
        """
        Initialize AXI4 packet with field configuration.

        Args:
            field_config: FieldConfig object for the specific AXI4 channel
            **kwargs: Initial field values
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
            id_width: Width of AWID field
            addr_width: Width of AWADDR field
            user_width: Width of AWUSER field
            **field_values: AXI4 AW channel field values (awid, awaddr, awlen, etc.)

        Returns:
            AXI4Packet configured for AW channel

        Example:
            packet = AXI4Packet.create_aw_packet(awid=1, awaddr=0x1000, awlen=3)
        """
        field_config = AXI4FieldConfigHelper.create_aw_field_config(id_width, addr_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_w_packet(cls, data_width: int = 32, user_width: int = 1, **field_values):
        """
        Create a Write Data (W) channel packet.

        Args:
            data_width: Width of WDATA field
            user_width: Width of WUSER field
            **field_values: AXI4 W channel field values (wdata, wstrb, wlast, wuser)

        Returns:
            AXI4Packet configured for W channel

        Example:
            packet = AXI4Packet.create_w_packet(wdata=0xDEADBEEF, wlast=1)
        """
        field_config = AXI4FieldConfigHelper.create_w_field_config(data_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_b_packet(cls, id_width: int = 8, user_width: int = 1, **field_values):
        """
        Create a Write Response (B) channel packet.

        Args:
            id_width: Width of BID field
            user_width: Width of BUSER field
            **field_values: AXI4 B channel field values (bid, bresp, buser)

        Returns:
            AXI4Packet configured for B channel

        Example:
            packet = AXI4Packet.create_b_packet(bid=1, bresp=0)  # OKAY response
        """
        field_config = AXI4FieldConfigHelper.create_b_field_config(id_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_ar_packet(cls, id_width: int = 8, addr_width: int = 32, user_width: int = 1, **field_values):
        """
        Create a Read Address (AR) channel packet.

        Args:
            id_width: Width of ARID field
            addr_width: Width of ARADDR field
            user_width: Width of ARUSER field
            **field_values: AXI4 AR channel field values (arid, araddr, arlen, etc.)

        Returns:
            AXI4Packet configured for AR channel

        Example:
            packet = AXI4Packet.create_ar_packet(arid=2, araddr=0x2000, arlen=7)
        """
        field_config = AXI4FieldConfigHelper.create_ar_field_config(id_width, addr_width, user_width)
        return cls(field_config, **field_values)

    @classmethod
    def create_r_packet(cls, id_width: int = 8, data_width: int = 32, user_width: int = 1, **field_values):
        """
        Create a Read Data (R) channel packet.

        Args:
            id_width: Width of RID field
            data_width: Width of RDATA field
            user_width: Width of RUSER field
            **field_values: AXI4 R channel field values (rid, rdata, rresp, rlast, ruser)

        Returns:
            AXI4Packet configured for R channel

        Example:
            packet = AXI4Packet.create_r_packet(rid=2, rdata=0x12345678, rlast=1)
        """
        field_config = AXI4FieldConfigHelper.create_r_field_config(id_width, data_width, user_width)
        return cls(field_config, **field_values)

    def get_channel_type(self) -> str:
        """
        Determine which AXI4 channel this packet belongs to.

        Returns:
            Channel type string ('AW', 'W', 'B', 'AR', 'R', 'UNKNOWN')
        """
        if self._channel_type is None:
            # Check for unique fields that identify each channel
            field_names = set(self.field_config.field_names())

            if 'awid' in field_names or 'awaddr' in field_names:
                self._channel_type = 'AW'
            elif 'wdata' in field_names or 'wstrb' in field_names:
                self._channel_type = 'W'
            elif 'bid' in field_names and 'bresp' in field_names:
                self._channel_type = 'B'
            elif 'arid' in field_names or 'araddr' in field_names:
                self._channel_type = 'AR'
            elif 'rid' in field_names and 'rdata' in field_names:
                self._channel_type = 'R'
            else:
                self._channel_type = 'UNKNOWN'

        return self._channel_type

    def validate_axi4_protocol(self) -> Tuple[bool, str]:
        """
        Validates the packet against AXI4 protocol rules.

        Returns:
            Tuple of (is_valid, error_message)
        """
        channel_type = self.get_channel_type()

        # Dispatch to appropriate validation method
        validation_methods = {
            'AW': self._validate_aw_packet,
            'W': self._validate_w_packet,
            'B': self._validate_b_packet,
            'AR': self._validate_ar_packet,
            'R': self._validate_r_packet
        }

        validator = validation_methods.get(channel_type)
        if validator:
            return validator()
        else:
            return False, f"Unknown AXI4 packet type: {channel_type}"

    def _validate_aw_packet(self) -> Tuple[bool, str]:
        """Validate Write Address channel packet."""
        # Check address alignment based on size
        if hasattr(self, 'awsize') and hasattr(self, 'awaddr'):
            if self.awsize > 7:  # Max size is 2^7 = 128 bytes
                return False, f"Invalid AW size: {self.awsize} (max is 7)"

            byte_count = 1 << self.awsize
            if self.awaddr % byte_count != 0:
                return False, f"AW address 0x{self.awaddr:X} not aligned for size {self.awsize} ({byte_count} bytes)"

        # Check burst type
        if hasattr(self, 'awburst'):
            if self.awburst not in [0, 1, 2]:  # FIXED, INCR, WRAP
                return False, f"Invalid AW burst type: {self.awburst} (must be 0=FIXED, 1=INCR, 2=WRAP)"

            # For WRAP bursts, check power-of-2 length
            if self.awburst == 2 and hasattr(self, 'awlen'):
                valid_lens = [1, 3, 7, 15]  # 2, 4, 8, 16 beats (awlen is 0-based)
                if self.awlen not in valid_lens:
                    return False, f"WRAP burst length must be 2, 4, 8, or 16 beats (awlen={self.awlen})"

        # Check burst length
        if hasattr(self, 'awlen'):
            if self.awlen > 255:  # AXI4 supports up to 256 beats
                return False, f"AW burst length too long: {self.awlen + 1} beats (max 256)"

        # Check lock type
        if hasattr(self, 'awlock'):
            if self.awlock not in [0, 1]:  # Normal, Exclusive
                return False, f"Invalid AW lock: {self.awlock} (must be 0=Normal, 1=Exclusive)"

        return True, "AW packet valid"

    def _validate_w_packet(self) -> Tuple[bool, str]:
        """Validate Write Data channel packet."""
        # Check that wstrb has correct relationship to wdata
        if hasattr(self, 'wdata') and hasattr(self, 'wstrb'):
            # Calculate expected strobe width from data width
            data_width = self.field_config.get_field('wdata').bits
            expected_strb_width = data_width // 8
            actual_strb_width = self.field_config.get_field('wstrb').bits

            if actual_strb_width != expected_strb_width:
                return False, f"W strobe width {actual_strb_width} doesn't match data width {data_width} (expected {expected_strb_width})"

        # Check wlast value
        if hasattr(self, 'wlast'):
            if self.wlast not in [0, 1]:
                return False, f"Invalid W last: {self.wlast} (must be 0 or 1)"

        return True, "W packet valid"

    def _validate_b_packet(self) -> Tuple[bool, str]:
        """Validate Write Response channel packet."""
        # Check response type
        if hasattr(self, 'bresp'):
            if self.bresp not in [0, 1, 2, 3]:  # OKAY, EXOKAY, SLVERR, DECERR
                return False, f"Invalid B response: {self.bresp} (must be 0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)"

        return True, "B packet valid"

    def _validate_ar_packet(self) -> Tuple[bool, str]:
        """Validate Read Address channel packet."""
        # AR validation is similar to AW
        if hasattr(self, 'arsize') and hasattr(self, 'araddr'):
            if self.arsize > 7:
                return False, f"Invalid AR size: {self.arsize} (max is 7)"

            byte_count = 1 << self.arsize
            if self.araddr % byte_count != 0:
                return False, f"AR address 0x{self.araddr:X} not aligned for size {self.arsize} ({byte_count} bytes)"

        if hasattr(self, 'arburst'):
            if self.arburst not in [0, 1, 2]:
                return False, f"Invalid AR burst type: {self.arburst} (must be 0=FIXED, 1=INCR, 2=WRAP)"

            if self.arburst == 2 and hasattr(self, 'arlen'):
                valid_lens = [1, 3, 7, 15]
                if self.arlen not in valid_lens:
                    return False, f"WRAP burst length must be 2, 4, 8, or 16 beats (arlen={self.arlen})"

        if hasattr(self, 'arlen'):
            if self.arlen > 255:
                return False, f"AR burst length too long: {self.arlen + 1} beats (max 256)"

        if hasattr(self, 'arlock'):
            if self.arlock not in [0, 1]:
                return False, f"Invalid AR lock: {self.arlock} (must be 0=Normal, 1=Exclusive)"

        return True, "AR packet valid"

    def _validate_r_packet(self) -> Tuple[bool, str]:
        """Validate Read Data channel packet."""
        # Check response type
        if hasattr(self, 'rresp'):
            if self.rresp not in [0, 1, 2, 3]:  # OKAY, EXOKAY, SLVERR, DECERR
                return False, f"Invalid R response: {self.rresp} (must be 0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)"

        # Check rlast value
        if hasattr(self, 'rlast'):
            if self.rlast not in [0, 1]:
                return False, f"Invalid R last: {self.rlast} (must be 0 or 1)"

        return True, "R packet valid"

    def get_burst_info(self) -> Dict[str, Any]:
        """
        Get burst information from address packets (AW/AR).

        Returns:
            Dictionary with burst information, or empty dict if not an address packet
        """
        channel_type = self.get_channel_type()

        if channel_type in ['AW', 'AR']:
            prefix = channel_type.lower()

            return {
                'burst_type': getattr(self, f'{prefix}burst', None),
                'burst_length': (getattr(self, f'{prefix}len', 0) + 1),  # Convert to actual beats
                'burst_size': getattr(self, f'{prefix}size', None),
                'bytes_per_beat': (1 << getattr(self, f'{prefix}size', 0)),
                'total_bytes': (getattr(self, f'{prefix}len', 0) + 1) * (1 << getattr(self, f'{prefix}size', 0)),
                'address': getattr(self, f'{prefix}addr', None)
            }

        return {}

    def get_response_info(self) -> Dict[str, Any]:
        """
        Get response information from response packets (B/R).

        Returns:
            Dictionary with response information, or empty dict if not a response packet
        """
        channel_type = self.get_channel_type()

        if channel_type == 'B':
            resp_code = getattr(self, 'bresp', 0)
        elif channel_type == 'R':
            resp_code = getattr(self, 'rresp', 0)
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
            info['is_last'] = getattr(self, 'rlast', 0) == 1

        return info

    def __str__(self) -> str:
        """String representation of the packet."""
        channel_type = self.get_channel_type()

        if channel_type == 'AW':
            return f"AXI4Packet(AW: id={getattr(self, 'awid', '?')}, addr=0x{getattr(self, 'awaddr', 0):X}, len={getattr(self, 'awlen', 0)})"
        elif channel_type == 'W':
            return f"AXI4Packet(W: data=0x{getattr(self, 'wdata', 0):X}, last={getattr(self, 'wlast', '?')})"
        elif channel_type == 'B':
            resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
            resp = resp_names.get(getattr(self, 'bresp', 0), 'UNKNOWN')
            return f"AXI4Packet(B: id={getattr(self, 'bid', '?')}, resp={resp})"
        elif channel_type == 'AR':
            return f"AXI4Packet(AR: id={getattr(self, 'arid', '?')}, addr=0x{getattr(self, 'araddr', 0):X}, len={getattr(self, 'arlen', 0)})"
        elif channel_type == 'R':
            resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
            resp = resp_names.get(getattr(self, 'rresp', 0), 'UNKNOWN')
            return f"AXI4Packet(R: id={getattr(self, 'rid', '?')}, data=0x{getattr(self, 'rdata', 0):X}, resp={resp}, last={getattr(self, 'rlast', '?')})"
        else:
            return f"AXI4Packet({channel_type})"


# Convenience functions for common packet patterns
def create_simple_write_packets(awid: int, addr: int, data: int,
                               id_width: int = 8, addr_width: int = 32, data_width: int = 32) -> Tuple[AXI4Packet, AXI4Packet]:
    """
    Create AW and W packets for a simple single-beat write.

    Args:
        awid: Write ID
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
        awid=awid, awaddr=addr, awlen=0, awsize=2, awburst=1  # Single beat, 4 bytes, INCR
    )

    strb_width = data_width // 8
    w_packet = AXI4Packet.create_w_packet(
        data_width=data_width,
        wdata=data, wstrb=(1 << strb_width) - 1, wlast=1  # All bytes valid, last beat
    )

    return aw_packet, w_packet


def create_simple_read_packet(arid: int, addr: int,
                            id_width: int = 8, addr_width: int = 32) -> AXI4Packet:
    """
    Create AR packet for a simple single-beat read.

    Args:
        arid: Read ID
        addr: Read address
        id_width: ID field width
        addr_width: Address field width

    Returns:
        AR packet
    """
    return AXI4Packet.create_ar_packet(
        id_width=id_width, addr_width=addr_width,
        arid=arid, araddr=addr, arlen=0, arsize=2, arburst=1  # Single beat, 4 bytes, INCR
    )


# Example usage and testing
if __name__ == "__main__":
    print("AXI4 Packet - Ground Up Implementation Testing")
    print("=" * 60)

    # Test packet creation
    aw_packet = AXI4Packet.create_aw_packet(awid=1, awaddr=0x1000, awlen=3)
    print(f"AW Packet: {aw_packet}")
    print(f"Channel Type: {aw_packet.get_channel_type()}")
    print(f"Burst Info: {aw_packet.get_burst_info()}")

    # Test validation
    is_valid, error_msg = aw_packet.validate_axi4_protocol()
    print(f"Validation: {is_valid}, Message: {error_msg}")

    # Test W packet
    w_packet = AXI4Packet.create_w_packet(wdata=0xDEADBEEF, wlast=1)
    print(f"\nW Packet: {w_packet}")

    # Test convenience functions
    aw, w = create_simple_write_packets(1, 0x2000, 0x12345678)
    print(f"\nSimple Write - AW: {aw}")
    print(f"Simple Write - W: {w}")

    ar = create_simple_read_packet(2, 0x3000)
    print(f"Simple Read - AR: {ar}")
