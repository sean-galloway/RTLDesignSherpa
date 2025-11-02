# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBPacket
# Purpose: APB Packet Implementation using the generic Packet base class
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""APB Packet Implementation using the generic Packet base class"""

import random
from collections import deque
from typing import Dict, Any, List, Optional, Union
from cocotb_coverage.crv import Randomized

# Import the base Packet class and other dependencies
from ..shared.packet import Packet
from ..shared.field_config import FieldConfig, FieldDefinition
from ..shared.flex_randomizer import FlexRandomizer

# Define the PWRITE mapping
PWRITE_MAP = ['READ', 'WRITE']


class APBPacket(Packet):
    """
    APB packet class for handling APB transactions.

    This class extends the base Packet class with APB-specific functionality.
    """

    def __init__(self, field_config=None, skip_compare_fields=None,
                 data_width=32, addr_width=32, strb_width=4, **kwargs):
        """
        Initialize an APB packet with the given field configuration.

        Args:
            field_config: Either a FieldConfig object or a dictionary of field definitions
            skip_compare_fields: List of field names to skip during comparison operations
            data_width: Width of data field in bits
            addr_width: Width of address field in bits
            strb_width: Width of strobe field in bits
            **kwargs: Initial values for fields (e.g., paddr=0x123, pwrite=1)
        """
        # Initialize configuration variables before calling super().__init__
        # Using object.__setattr__ to bypass __setattr__ checks
        object.__setattr__(self, 'data_width', data_width)
        object.__setattr__(self, 'addr_width', addr_width)
        object.__setattr__(self, 'strb_width', strb_width)
        object.__setattr__(self, 'count', kwargs.get('count', 0))

        # Use default APB field config if none provided
        if field_config is None:
            field_config = APBPacket.create_apb_field_config(addr_width, data_width, strb_width)

        # Set default skip_compare_fields if none provided
        if skip_compare_fields is None:
            skip_compare_fields = ['start_time', 'end_time', 'count']

        # Initialize base class
        super().__init__(field_config, skip_compare_fields, **kwargs)

        # Derive APB-specific attributes after base initialization
        self.direction = PWRITE_MAP[self.fields.get('pwrite', 0)]

        # For backward compatibility
        self.cycle = self  # In case code expects to access a 'cycle' attribute

    @staticmethod
    def create_apb_field_config(addr_width, data_width, strb_width):
        """
        Create default field configuration for APB packets.

        Args:
            addr_width: Width of address field in bits
            data_width: Width of data field in bits
            strb_width: Width of strobe field in bits

        Returns:
            FieldConfig object with APB fields
        """
        config = FieldConfig()

        # Add fields
        config.add_field(FieldDefinition(
            name="pwrite",
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Write Enable (0=Read, 1=Write)"
        ))

        config.add_field(FieldDefinition(
            name="paddr",
            bits=addr_width,
            default=0,
            format="hex",
            display_width=addr_width // 4,
            description="Address"
        ))

        config.add_field(FieldDefinition(
            name="pwdata",
            bits=data_width,
            default=0,
            format="hex",
            display_width=data_width // 4,
            description="Write Data"
        ))

        config.add_field(FieldDefinition(
            name="prdata",
            bits=data_width,
            default=0,
            format="hex",
            display_width=data_width // 4,
            description="Read Data"
        ))

        config.add_field(FieldDefinition(
            name="pstrb",
            bits=strb_width,
            default=0,
            format="bin",
            display_width=strb_width,
            description="Write Strobes"
        ))

        config.add_field(FieldDefinition(
            name="pprot",
            bits=3,
            default=0,
            format="hex",
            display_width=1,
            description="Protection Control"
        ))

        config.add_field(FieldDefinition(
            name="pslverr",
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Slave Error"
        ))

        return config

    def __str__(self):
        """
        Provide a detailed string representation of the APB packet.

        Returns:
            Formatted string with all fields
        """
        result = [
            "APB Packet:",
            f"  Direction:  {self.direction}",
            f"  Address:    {self._format_field('paddr', self.fields['paddr'])}",
        ]

        # Data fields based on direction
        if self.direction == 'WRITE':
            result.append(f"  Write Data: {self._format_field('pwdata', self.fields['pwdata'])}")
            result.append(f"  Strobes:    {self._format_field('pstrb', self.fields['pstrb'])}")
        else:
            result.append(f"  Read Data:  {self._format_field('prdata', self.fields['prdata'])}")

        # Control fields
        result.append(f"  Protection: {self._format_field('pprot', self.fields['pprot'])}")
        result.append(f"  Slave Err:  {self._format_field('pslverr', self.fields['pslverr'])}")

        # Timing information
        if self.start_time > 0:
            result.append(f"  Start Time: {self.start_time} ns")
        if self.end_time > 0:
            result.extend(
                (
                    f"  End Time:   {self.end_time} ns",
                    f"  Duration:   {self.end_time - self.start_time} ns",
                )
            )
        # Transaction count
        result.append(f"  Count:      {self.count}")

        return "\n".join(result)

    def formatted(self, compact=False):
        """
        Return a formatted string representation.

        Args:
            compact: If True, return a more compact representation

        Returns:
            Formatted string representation
        """
        if not compact:
            # Use the full string representation
            return self.__str__()

        # Compact representation
        fields = [
            f"time={self.start_time}",
            f"dir={self.direction}",
            f"addr={self._format_field('paddr', self.fields['paddr'])}",
        ]

        if self.direction == 'WRITE':
            fields.append(f"wdata={self._format_field('pwdata', self.fields['pwdata'])}")
            fields.append(f"strb={self._format_field('pstrb', self.fields['pstrb'])}")
        else:
            fields.append(f"rdata={self._format_field('prdata', self.fields['prdata'])}")

        fields.append(f"prot={self._format_field('pprot', self.fields['pprot'])}")

        if self.fields['pslverr']:
            fields.append(f"err={self.fields['pslverr']}")

        return f"APBPacket({', '.join(fields)})"

    def __eq__(self, other):
        """
        Compare packets for equality, skipping fields in skip_compare_fields.
        Override to add APB-specific comparison logic.

        Args:
            other: Another packet to compare with

        Returns:
            True if all non-skipped fields match, False otherwise
        """
        if not isinstance(other, APBPacket):
            return NotImplemented

        # Compare the relevant data field based on direction
        if self.direction == 'WRITE':
            data_self = self.fields.get('pwdata', 0)
            data_other = other.fields.get('pwdata', 0)
        else:
            data_self = self.fields.get('prdata', 0)
            data_other = other.fields.get('prdata', 0)

        # Basic checks for key fields
        if (self.direction != other.direction or
            self.fields.get('paddr', 0) != other.fields.get('paddr', 0) or
            data_self != data_other or
            self.fields.get('pprot', 0) != other.fields.get('pprot', 0) or
            self.fields.get('pslverr', 0) != other.fields.get('pslverr', 0)):
            return False

        # For writes, also check strobes
        if self.direction == 'WRITE' and self.fields.get('pstrb', 0) != other.fields.get('pstrb', 0):
            return False

        return True


class APBTransaction(Randomized):
    """
    APB Transaction class with improved randomization and configuration.

    This class generates APB packets with randomized field values.
    """

    def __init__(self, data_width=32, addr_width=32, strb_width=4, randomizer=None, **kwargs):
        """
        Initialize APB Transaction generator.

        Args:
            data_width: Data width in bits
            addr_width: Address width in bits
            strb_width: Strobe width in bits
            randomizer: Optional randomizer dictionary or FlexRandomizer
            **kwargs: Initial values for fields
        """
        # Initialize the Randomized base class first
        super().__init__()

        # Add randomized variables explicitly as class attributes
        # This must be done before calling add_rand
        self.pwrite = 0
        self.paddr = 0
        self.pstrb = 0
        self.pprot = 0

        # Add these variables to be randomized
        self.add_rand("pwrite", [0, 1])
        self.add_rand("paddr", list(range(2**12)))
        self.add_rand("pstrb", list(range(2**strb_width)))
        self.add_rand("pprot", list(range(8)))

        # Store configuration attributes directly
        self.data_width = data_width
        self.addr_width = addr_width
        self.strb_width = strb_width
        self.addr_mask = (strb_width - 1)

        # Setup field configuration
        self.field_config = APBPacket.create_apb_field_config(
            addr_width, data_width, strb_width
        )

        # Setup randomizer for FlexRandomizer-based randomization
        if randomizer is None:
            addr_min_hi = (4 * self.strb_width) - 1
            addr_max_lo = (4 * self.strb_width)
            addr_max_hi = (32 * self.strb_width) - 1

            # Default randomizer
            self.randomizer = FlexRandomizer({
                'pwrite': ([(0, 0), (1, 1)], [1, 1]),
                'paddr': ([(0, addr_min_hi), (addr_max_lo, addr_max_hi)], [4, 1]),
                'pstrb': ([(15, 15), (0, 14)], [4, 1]),
                'pprot': ([(0, 0), (1, 7)], [4, 1])
            })
        elif isinstance(randomizer, FlexRandomizer):
            # Use provided FlexRandomizer
            self.randomizer = randomizer
        elif isinstance(randomizer, dict):
            # Create from dictionary
            self.randomizer = FlexRandomizer(randomizer)
        else:
            # Try to convert to FlexRandomizer
            self.randomizer = FlexRandomizer(randomizer)

        # Create initial packet with any initial values from kwargs
        self.packet = APBPacket(
            field_config=self.field_config,
            data_width=data_width,
            addr_width=addr_width,
            strb_width=strb_width,
            **kwargs
        )

    def next(self):
        """
        Generate next transaction using randomizer.

        This will use either the Randomized infrastructure or the FlexRandomizer
        based on the implementation.

        Returns:
            APBPacket: Generated packet
        """
        # Use Randomized's randomize method to set self.pwrite, self.paddr, etc.
        self.randomize()

        # Also get values from FlexRandomizer
        value_dict = self.randomizer.next()

        # Create a new packet
        packet = APBPacket(
            field_config=self.field_config,
            data_width=self.data_width,
            addr_width=self.addr_width,
            strb_width=self.strb_width
        )

        # We can choose which source of randomization to use
        # Here we use FlexRandomizer for consistency with original implementation
        packet.fields['pwrite'] = value_dict['pwrite']
        packet.fields['paddr'] = value_dict['paddr'] & ~self.addr_mask
        packet.fields['pstrb'] = value_dict['pstrb']
        packet.fields['pprot'] = value_dict['pprot']
        packet.direction = PWRITE_MAP[packet.fields['pwrite']]

        # Generate random data for write
        if packet.direction == 'WRITE':
            packet.fields['pwdata'] = random.randint(0, (1 << self.data_width) - 1)

        # Update internal packet and return a copy
        self.packet = packet
        return packet.copy()

    def set_constrained_random(self):
        """
        Set fields using constrained randomization.

        Returns:
            self for chaining
        """
        self.next()
        return self

    def __str__(self):
        """
        String representation using packet's formatting.

        Returns:
            Formatted string
        """
        return f"APB Transaction:\n{self.packet}"

    def formatted(self, compact=False):
        """
        Return a formatted representation.

        Args:
            compact: If True, return a compact one-line representation

        Returns:
            Formatted string
        """
        if compact:
            return f"APBTransaction({self.packet.formatted(compact=True)})"
        else:
            return self.__str__()

