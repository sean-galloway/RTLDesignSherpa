# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5Packet
# Purpose: AXIS5 Packet - Stream protocol packet with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Packet - Stream protocol packet with AMBA5 extensions

This module provides packet classes for AXI5-Stream protocol with:
- TWAKEUP: Wake-up signaling
- TPARITY: Data parity protection
"""

import random
from typing import Optional, Dict, Any

from ..axis4.axis_packet import AXISPacket
from ..shared.field_config import FieldConfig, FieldDefinition
from ..shared.flex_randomizer import FlexRandomizer


class AXIS5Packet(AXISPacket):
    """
    AXIS5 Packet class for AXI5-Stream protocol.

    Extends AXISPacket with AMBA5-specific fields:
    - wakeup: Wake-up signaling
    - parity: Data parity bits
    - parity_error: Parity error indicator
    """

    def __init__(self, field_config=None, skip_compare_fields=None,
                 data_width=32, enable_wakeup=True, enable_parity=False, **kwargs):
        """
        Initialize AXIS5 packet.

        Args:
            field_config: Field configuration (if None, creates default)
            skip_compare_fields: Fields to skip in comparison
            data_width: Data width in bits
            enable_wakeup: Enable wakeup signal field
            enable_parity: Enable parity signal field
            **kwargs: Initial field values
        """
        # Store AXIS5 configuration
        object.__setattr__(self, 'enable_wakeup', enable_wakeup)
        object.__setattr__(self, 'enable_parity', enable_parity)
        object.__setattr__(self, 'parity_width', data_width // 8)

        # Create field config if not provided
        if field_config is None:
            field_config = self.create_axis5_field_config(
                data_width=data_width,
                enable_wakeup=enable_wakeup,
                enable_parity=enable_parity
            )

        # Set default skip fields
        if skip_compare_fields is None:
            skip_compare_fields = ['start_time', 'end_time', 'count', 'parity_error']

        # Initialize parent
        super().__init__(field_config, skip_compare_fields, data_width=data_width, **kwargs)

    @staticmethod
    def create_axis5_field_config(data_width=32, id_width=8, dest_width=4, user_width=1,
                                   enable_wakeup=True, enable_parity=False):
        """
        Create field configuration for AXIS5 packets.

        Args:
            data_width: Data width in bits
            id_width: ID width in bits
            dest_width: Destination width in bits
            user_width: User width in bits
            enable_wakeup: Enable wakeup field
            enable_parity: Enable parity field

        Returns:
            FieldConfig object with AXIS5 fields
        """
        strb_width = data_width // 8
        parity_width = strb_width  # 1 parity bit per byte

        config = FieldConfig()

        # Core AXIS fields
        config.add_field(FieldDefinition(
            name="data",
            bits=data_width,
            default=0,
            format="hex",
            display_width=data_width // 4,
            description="Stream Data"
        ))

        config.add_field(FieldDefinition(
            name="strb",
            bits=strb_width,
            default=(1 << strb_width) - 1,
            format="bin",
            display_width=strb_width,
            description="Byte Strobes"
        ))

        config.add_field(FieldDefinition(
            name="last",
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Last Transfer"
        ))

        config.add_field(FieldDefinition(
            name="id",
            bits=id_width,
            default=0,
            format="hex",
            display_width=max(1, id_width // 4),
            description="Stream ID"
        ))

        config.add_field(FieldDefinition(
            name="dest",
            bits=dest_width,
            default=0,
            format="hex",
            display_width=max(1, dest_width // 4),
            description="Destination"
        ))

        config.add_field(FieldDefinition(
            name="user",
            bits=user_width,
            default=0,
            format="hex",
            display_width=max(1, user_width // 4),
            description="User Signal"
        ))

        # AXIS5 extension fields
        if enable_wakeup:
            config.add_field(FieldDefinition(
                name="wakeup",
                bits=1,
                default=0,
                format="dec",
                display_width=1,
                description="Wake-up Signal"
            ))

        if enable_parity:
            config.add_field(FieldDefinition(
                name="parity",
                bits=parity_width,
                default=0,
                format="bin",
                display_width=parity_width,
                description="Data Parity"
            ))

            config.add_field(FieldDefinition(
                name="parity_error",
                bits=1,
                default=0,
                format="dec",
                display_width=1,
                description="Parity Error"
            ))

        return config

    # AXIS5-specific properties
    @property
    def wakeup(self):
        """Get wakeup signal."""
        return self.get_field_value('wakeup', 0)

    @wakeup.setter
    def wakeup(self, value):
        """Set wakeup signal."""
        self.set_field_value('wakeup', value)

    @property
    def parity(self):
        """Get parity signal."""
        return self.get_field_value('parity', 0)

    @parity.setter
    def parity(self, value):
        """Set parity signal."""
        self.set_field_value('parity', value)

    @property
    def parity_error(self):
        """Get parity error indicator."""
        return self.get_field_value('parity_error', 0)

    @parity_error.setter
    def parity_error(self, value):
        """Set parity error indicator."""
        self.set_field_value('parity_error', value)

    # AXIS5-specific methods
    def calculate_parity(self) -> int:
        """
        Calculate parity for the data field.

        Returns:
            Calculated parity value (1 bit per byte)
        """
        data_value = self.data
        parity_width = getattr(self, 'parity_width', 4)
        parity = 0

        for i in range(parity_width):
            byte_val = (data_value >> (i * 8)) & 0xFF
            # Odd parity per byte
            bit_parity = bin(byte_val).count('1') & 1
            parity |= (bit_parity << i)

        return parity

    def check_parity(self) -> bool:
        """
        Check if parity matches calculated parity.

        Returns:
            True if parity is correct, False otherwise
        """
        if not getattr(self, 'enable_parity', False):
            return True
        calculated = self.calculate_parity()
        return self.parity == calculated

    def set_wakeup(self, enable: bool = True):
        """Set wakeup signal state."""
        self.wakeup = 1 if enable else 0

    def is_wakeup_active(self) -> bool:
        """Check if wakeup is active."""
        return bool(self.wakeup)

    def to_axis4_packet(self):
        """
        Convert to AXIS4 packet (drop AXIS5 fields).

        Returns:
            AXISPacket without AXIS5 extensions
        """
        axis4_pkt = AXISPacket(data_width=getattr(self, 'data_width', 32))
        axis4_pkt.data = self.data
        axis4_pkt.strb = self.strb
        axis4_pkt.last = self.last
        axis4_pkt.id = self.id
        axis4_pkt.dest = self.dest
        axis4_pkt.user = self.user
        return axis4_pkt

    def __str__(self):
        """String representation."""
        result = [
            "AXIS5 Packet:",
            f"  Data:     0x{self.data:X}",
            f"  Strobe:   0b{self.strb:b}",
            f"  Last:     {self.last}",
            f"  ID:       0x{self.id:X}",
            f"  Dest:     0x{self.dest:X}",
            f"  User:     0x{self.user:X}",
        ]

        if getattr(self, 'enable_wakeup', False):
            result.append(f"  Wakeup:   {self.wakeup}")

        if getattr(self, 'enable_parity', False):
            result.append(f"  Parity:   0b{self.parity:b}")
            result.append(f"  ParityOK: {self.check_parity()}")

        return "\n".join(result)


class AXIS5Transaction:
    """
    AXIS5 Transaction generator with randomization.
    """

    def __init__(self, data_width=32, id_width=8, dest_width=4, user_width=1,
                 enable_wakeup=True, enable_parity=False, randomizer=None):
        """
        Initialize AXIS5 transaction generator.

        Args:
            data_width: Data width in bits
            id_width: ID width in bits
            dest_width: Destination width in bits
            user_width: User width in bits
            enable_wakeup: Enable wakeup randomization
            enable_parity: Enable parity generation
            randomizer: Optional FlexRandomizer for value generation
        """
        self.data_width = data_width
        self.id_width = id_width
        self.dest_width = dest_width
        self.user_width = user_width
        self.enable_wakeup = enable_wakeup
        self.enable_parity = enable_parity
        self.strb_width = data_width // 8

        # Create field config
        self.field_config = AXIS5Packet.create_axis5_field_config(
            data_width=data_width,
            id_width=id_width,
            dest_width=dest_width,
            user_width=user_width,
            enable_wakeup=enable_wakeup,
            enable_parity=enable_parity
        )

        # Setup randomizer
        if randomizer is None:
            self.randomizer = FlexRandomizer({
                'data': ([(0, (1 << data_width) - 1)], [1]),
                'strb': ([((1 << self.strb_width) - 1, (1 << self.strb_width) - 1)], [1]),
                'last': ([(0, 0), (1, 1)], [3, 1]),
                'id': ([(0, (1 << id_width) - 1)], [1]),
                'dest': ([(0, (1 << dest_width) - 1)], [1]),
                'user': ([(0, (1 << user_width) - 1)], [1]),
                'wakeup': ([(0, 0), (1, 1)], [9, 1]),  # 10% wakeup probability
            })
        elif isinstance(randomizer, FlexRandomizer):
            self.randomizer = randomizer
        else:
            self.randomizer = FlexRandomizer(randomizer)

        # Current packet
        self.packet = AXIS5Packet(
            field_config=self.field_config,
            data_width=data_width,
            enable_wakeup=enable_wakeup,
            enable_parity=enable_parity
        )

    def next(self) -> AXIS5Packet:
        """
        Generate next random transaction.

        Returns:
            AXIS5Packet with randomized values
        """
        values = self.randomizer.next()

        packet = AXIS5Packet(
            field_config=self.field_config,
            data_width=self.data_width,
            enable_wakeup=self.enable_wakeup,
            enable_parity=self.enable_parity
        )

        # Set core fields
        packet.data = values.get('data', random.randint(0, (1 << self.data_width) - 1))
        packet.strb = values.get('strb', (1 << self.strb_width) - 1)
        packet.last = values.get('last', 0)
        packet.id = values.get('id', 0)
        packet.dest = values.get('dest', 0)
        packet.user = values.get('user', 0)

        # Set AXIS5 fields
        if self.enable_wakeup:
            packet.wakeup = values.get('wakeup', 0)

        if self.enable_parity:
            # Auto-calculate parity
            packet.parity = packet.calculate_parity()

        self.packet = packet
        return packet.copy()

    def create_packet(self, data, last=0, id=0, dest=0, user=0,
                      wakeup=0, strb=None) -> AXIS5Packet:
        """
        Create a packet with specific values.

        Args:
            data: Data value
            last: Last transfer flag
            id: Stream ID
            dest: Destination
            user: User signal
            wakeup: Wakeup signal
            strb: Strobe value (if None, full strobe)

        Returns:
            AXIS5Packet with specified values
        """
        packet = AXIS5Packet(
            field_config=self.field_config,
            data_width=self.data_width,
            enable_wakeup=self.enable_wakeup,
            enable_parity=self.enable_parity
        )

        packet.data = data
        packet.strb = strb if strb is not None else (1 << self.strb_width) - 1
        packet.last = last
        packet.id = id
        packet.dest = dest
        packet.user = user

        if self.enable_wakeup:
            packet.wakeup = wakeup

        if self.enable_parity:
            packet.parity = packet.calculate_parity()

        return packet
