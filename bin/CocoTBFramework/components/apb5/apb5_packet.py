# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5Packet
# Purpose: APB5 Packet Implementation with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""APB5 Packet Implementation with AMBA5 extensions.

This module extends the APB packet with APB5-specific signals:
- PAUSER: User-defined request attributes
- PWUSER: User-defined write data attributes
- PRUSER: User-defined read data attributes
- PBUSER: User-defined response attributes
- PWAKEUP: Wake-up signal status
- Parity error flags
"""

import random
from typing import Optional
from cocotb_coverage.crv import Randomized

from ..shared.packet import Packet
from ..shared.field_config import FieldConfig, FieldDefinition
from ..shared.flex_randomizer import FlexRandomizer
from ..apb.apb_packet import APBPacket, PWRITE_MAP


class APB5Packet(Packet):
    """
    APB5 packet class for handling APB5 transactions with AMBA5 extensions.

    This class extends the base Packet class with APB5-specific functionality
    including user signals, wake-up support, and parity error tracking.
    """

    def __init__(self, field_config=None, skip_compare_fields=None,
                 data_width=32, addr_width=32, strb_width=4,
                 auser_width=4, wuser_width=4, ruser_width=4, buser_width=4,
                 **kwargs):
        """
        Initialize an APB5 packet with the given field configuration.

        Args:
            field_config: Either a FieldConfig object or a dictionary of field definitions
            skip_compare_fields: List of field names to skip during comparison operations
            data_width: Width of data field in bits
            addr_width: Width of address field in bits
            strb_width: Width of strobe field in bits
            auser_width: Width of PAUSER field in bits
            wuser_width: Width of PWUSER field in bits
            ruser_width: Width of PRUSER field in bits
            buser_width: Width of PBUSER field in bits
            **kwargs: Initial values for fields
        """
        # Initialize configuration variables before calling super().__init__
        object.__setattr__(self, 'data_width', data_width)
        object.__setattr__(self, 'addr_width', addr_width)
        object.__setattr__(self, 'strb_width', strb_width)
        object.__setattr__(self, 'auser_width', auser_width)
        object.__setattr__(self, 'wuser_width', wuser_width)
        object.__setattr__(self, 'ruser_width', ruser_width)
        object.__setattr__(self, 'buser_width', buser_width)
        object.__setattr__(self, 'count', kwargs.get('count', 0))

        # Use default APB5 field config if none provided
        if field_config is None:
            field_config = APB5Packet.create_apb5_field_config(
                addr_width, data_width, strb_width,
                auser_width, wuser_width, ruser_width, buser_width
            )

        # Set default skip_compare_fields if none provided
        if skip_compare_fields is None:
            skip_compare_fields = ['start_time', 'end_time', 'count', 'wakeup',
                                   'parity_error_wdata', 'parity_error_rdata',
                                   'parity_error_ctrl']

        # Initialize base class
        super().__init__(field_config, skip_compare_fields, **kwargs)

        # Derive APB-specific attributes after base initialization
        self.direction = PWRITE_MAP[self.fields.get('pwrite', 0)]

        # For backward compatibility
        self.cycle = self

    @staticmethod
    def create_apb5_field_config(addr_width, data_width, strb_width,
                                  auser_width=4, wuser_width=4,
                                  ruser_width=4, buser_width=4):
        """
        Create default field configuration for APB5 packets.

        Args:
            addr_width: Width of address field in bits
            data_width: Width of data field in bits
            strb_width: Width of strobe field in bits
            auser_width: Width of PAUSER field in bits
            wuser_width: Width of PWUSER field in bits
            ruser_width: Width of PRUSER field in bits
            buser_width: Width of PBUSER field in bits

        Returns:
            FieldConfig object with APB5 fields
        """
        config = FieldConfig()

        # APB4 compatible fields
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

        # APB5 User Signal Fields
        config.add_field(FieldDefinition(
            name="pauser",
            bits=auser_width,
            default=0,
            format="hex",
            display_width=max(1, auser_width // 4),
            description="Request User Attributes"
        ))

        config.add_field(FieldDefinition(
            name="pwuser",
            bits=wuser_width,
            default=0,
            format="hex",
            display_width=max(1, wuser_width // 4),
            description="Write Data User Attributes"
        ))

        config.add_field(FieldDefinition(
            name="pruser",
            bits=ruser_width,
            default=0,
            format="hex",
            display_width=max(1, ruser_width // 4),
            description="Read Data User Attributes"
        ))

        config.add_field(FieldDefinition(
            name="pbuser",
            bits=buser_width,
            default=0,
            format="hex",
            display_width=max(1, buser_width // 4),
            description="Response User Attributes"
        ))

        # APB5 Wake-up Field
        config.add_field(FieldDefinition(
            name="wakeup",
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Wake-up Request (from slave)"
        ))

        # Parity Error Flags (for monitoring)
        config.add_field(FieldDefinition(
            name="parity_error_wdata",
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Write Data Parity Error"
        ))

        config.add_field(FieldDefinition(
            name="parity_error_rdata",
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Read Data Parity Error"
        ))

        config.add_field(FieldDefinition(
            name="parity_error_ctrl",
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Control Signal Parity Error"
        ))

        return config

    def __str__(self):
        """
        Provide a detailed string representation of the APB5 packet.

        Returns:
            Formatted string with all fields
        """
        result = [
            "APB5 Packet:",
            f"  Direction:  {self.direction}",
            f"  Address:    {self._format_field('paddr', self.fields['paddr'])}",
        ]

        # Data fields based on direction
        if self.direction == 'WRITE':
            result.append(
                f"  Write Data: {self._format_field('pwdata', self.fields['pwdata'])}"
            )
            result.append(
                f"  Strobes:    {self._format_field('pstrb', self.fields['pstrb'])}"
            )
            result.append(
                f"  PWUSER:     {self._format_field('pwuser', self.fields['pwuser'])}"
            )
        else:
            result.append(
                f"  Read Data:  {self._format_field('prdata', self.fields['prdata'])}"
            )
            result.append(
                f"  PRUSER:     {self._format_field('pruser', self.fields['pruser'])}"
            )

        # Control and user fields
        result.append(
            f"  Protection: {self._format_field('pprot', self.fields['pprot'])}"
        )
        result.append(
            f"  PAUSER:     {self._format_field('pauser', self.fields['pauser'])}"
        )
        result.append(
            f"  PBUSER:     {self._format_field('pbuser', self.fields['pbuser'])}"
        )
        result.append(
            f"  Slave Err:  {self._format_field('pslverr', self.fields['pslverr'])}"
        )
        result.append(
            f"  Wake-up:    {self._format_field('wakeup', self.fields['wakeup'])}"
        )

        # Parity error flags if any set
        if any([
            self.fields.get('parity_error_wdata', 0),
            self.fields.get('parity_error_rdata', 0),
            self.fields.get('parity_error_ctrl', 0)
        ]):
            result.append("  Parity Errors:")
            if self.fields.get('parity_error_wdata', 0):
                result.append("    - Write Data Parity Error")
            if self.fields.get('parity_error_rdata', 0):
                result.append("    - Read Data Parity Error")
            if self.fields.get('parity_error_ctrl', 0):
                result.append("    - Control Parity Error")

        # Timing information
        if self.start_time > 0:
            result.append(f"  Start Time: {self.start_time} ns")
        if self.end_time > 0:
            result.extend([
                f"  End Time:   {self.end_time} ns",
                f"  Duration:   {self.end_time - self.start_time} ns",
            ])
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
            return self.__str__()

        # Compact representation
        fields = [
            f"time={self.start_time}",
            f"dir={self.direction}",
            f"addr={self._format_field('paddr', self.fields['paddr'])}",
        ]

        if self.direction == 'WRITE':
            fields.append(
                f"wdata={self._format_field('pwdata', self.fields['pwdata'])}"
            )
            fields.append(
                f"strb={self._format_field('pstrb', self.fields['pstrb'])}"
            )
        else:
            fields.append(
                f"rdata={self._format_field('prdata', self.fields['prdata'])}"
            )

        fields.append(f"prot={self._format_field('pprot', self.fields['pprot'])}")
        fields.append(f"auser={self._format_field('pauser', self.fields['pauser'])}")

        if self.fields.get('wakeup', 0):
            fields.append("wakeup=1")

        if self.fields['pslverr']:
            fields.append(f"err={self.fields['pslverr']}")

        return f"APB5Packet({', '.join(fields)})"

    def __eq__(self, other):
        """
        Compare packets for equality, skipping fields in skip_compare_fields.

        Args:
            other: Another packet to compare with

        Returns:
            True if all non-skipped fields match, False otherwise
        """
        if not isinstance(other, APB5Packet):
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
        if (self.direction == 'WRITE' and
            self.fields.get('pstrb', 0) != other.fields.get('pstrb', 0)):
            return False

        # Check APB5 user signals
        if (self.fields.get('pauser', 0) != other.fields.get('pauser', 0) or
            self.fields.get('pbuser', 0) != other.fields.get('pbuser', 0)):
            return False

        if self.direction == 'WRITE':
            if self.fields.get('pwuser', 0) != other.fields.get('pwuser', 0):
                return False
        else:
            if self.fields.get('pruser', 0) != other.fields.get('pruser', 0):
                return False

        return True

    def to_apb4_packet(self) -> APBPacket:
        """
        Convert this APB5 packet to an APB4 packet (drop APB5 extensions).

        Returns:
            APBPacket with APB4 fields only
        """
        return APBPacket(
            data_width=self.data_width,
            addr_width=self.addr_width,
            strb_width=self.strb_width,
            pwrite=self.fields['pwrite'],
            paddr=self.fields['paddr'],
            pwdata=self.fields['pwdata'],
            prdata=self.fields['prdata'],
            pstrb=self.fields['pstrb'],
            pprot=self.fields['pprot'],
            pslverr=self.fields['pslverr'],
        )

    @classmethod
    def from_apb4_packet(cls, apb4_pkt: APBPacket,
                          auser_width=4, wuser_width=4,
                          ruser_width=4, buser_width=4) -> 'APB5Packet':
        """
        Create an APB5 packet from an APB4 packet (with default APB5 extensions).

        Args:
            apb4_pkt: Source APB4 packet
            auser_width: Width of PAUSER field
            wuser_width: Width of PWUSER field
            ruser_width: Width of PRUSER field
            buser_width: Width of PBUSER field

        Returns:
            APB5Packet with APB5 extensions set to defaults
        """
        return cls(
            data_width=apb4_pkt.data_width,
            addr_width=apb4_pkt.addr_width,
            strb_width=apb4_pkt.strb_width,
            auser_width=auser_width,
            wuser_width=wuser_width,
            ruser_width=ruser_width,
            buser_width=buser_width,
            pwrite=apb4_pkt.fields['pwrite'],
            paddr=apb4_pkt.fields['paddr'],
            pwdata=apb4_pkt.fields['pwdata'],
            prdata=apb4_pkt.fields['prdata'],
            pstrb=apb4_pkt.fields['pstrb'],
            pprot=apb4_pkt.fields['pprot'],
            pslverr=apb4_pkt.fields['pslverr'],
            pauser=0,
            pwuser=0,
            pruser=0,
            pbuser=0,
            wakeup=0,
        )


class APB5Transaction(Randomized):
    """
    APB5 Transaction class with randomization for APB5 signals.

    This class generates APB5 packets with randomized field values
    including the APB5-specific user signals.
    """

    def __init__(self, data_width=32, addr_width=32, strb_width=4,
                 auser_width=4, wuser_width=4, ruser_width=4, buser_width=4,
                 randomizer=None, **kwargs):
        """
        Initialize APB5 Transaction generator.

        Args:
            data_width: Data width in bits
            addr_width: Address width in bits
            strb_width: Strobe width in bits
            auser_width: PAUSER width in bits
            wuser_width: PWUSER width in bits
            ruser_width: PRUSER width in bits
            buser_width: PBUSER width in bits
            randomizer: Optional randomizer dictionary or FlexRandomizer
            **kwargs: Initial values for fields
        """
        super().__init__()

        # Add randomized variables
        self.pwrite = 0
        self.paddr = 0
        self.pstrb = 0
        self.pprot = 0
        self.pauser = 0
        self.pwuser = 0

        self.add_rand("pwrite", [0, 1])
        self.add_rand("paddr", list(range(2**12)))
        self.add_rand("pstrb", list(range(2**strb_width)))
        self.add_rand("pprot", list(range(8)))
        self.add_rand("pauser", list(range(2**auser_width)))
        self.add_rand("pwuser", list(range(2**wuser_width)))

        # Store configuration
        self.data_width = data_width
        self.addr_width = addr_width
        self.strb_width = strb_width
        self.auser_width = auser_width
        self.wuser_width = wuser_width
        self.ruser_width = ruser_width
        self.buser_width = buser_width
        self.addr_mask = (strb_width - 1)

        # Setup field configuration
        self.field_config = APB5Packet.create_apb5_field_config(
            addr_width, data_width, strb_width,
            auser_width, wuser_width, ruser_width, buser_width
        )

        # Setup randomizer
        if randomizer is None:
            addr_min_hi = (4 * self.strb_width) - 1
            addr_max_lo = (4 * self.strb_width)
            addr_max_hi = (32 * self.strb_width) - 1

            self.randomizer = FlexRandomizer({
                'pwrite': ([(0, 0), (1, 1)], [1, 1]),
                'paddr': ([(0, addr_min_hi), (addr_max_lo, addr_max_hi)], [4, 1]),
                'pstrb': ([(15, 15), (0, 14)], [4, 1]),
                'pprot': ([(0, 0), (1, 7)], [4, 1]),
                'pauser': ([(0, (1 << auser_width) - 1)], [1]),
                'pwuser': ([(0, (1 << wuser_width) - 1)], [1]),
            })
        elif isinstance(randomizer, FlexRandomizer):
            self.randomizer = randomizer
        elif isinstance(randomizer, dict):
            self.randomizer = FlexRandomizer(randomizer)
        else:
            self.randomizer = FlexRandomizer(randomizer)

        # Create initial packet
        self.packet = APB5Packet(
            field_config=self.field_config,
            data_width=data_width,
            addr_width=addr_width,
            strb_width=strb_width,
            auser_width=auser_width,
            wuser_width=wuser_width,
            ruser_width=ruser_width,
            buser_width=buser_width,
            **kwargs
        )

    def next(self):
        """
        Generate next transaction using randomizer.

        Returns:
            APB5Packet: Generated packet
        """
        self.randomize()
        value_dict = self.randomizer.next()

        packet = APB5Packet(
            field_config=self.field_config,
            data_width=self.data_width,
            addr_width=self.addr_width,
            strb_width=self.strb_width,
            auser_width=self.auser_width,
            wuser_width=self.wuser_width,
            ruser_width=self.ruser_width,
            buser_width=self.buser_width,
        )

        # Set APB4 fields
        packet.fields['pwrite'] = value_dict['pwrite']
        packet.fields['paddr'] = value_dict['paddr'] & ~self.addr_mask
        packet.fields['pstrb'] = value_dict['pstrb']
        packet.fields['pprot'] = value_dict['pprot']
        packet.direction = PWRITE_MAP[packet.fields['pwrite']]

        # Set APB5 user fields
        packet.fields['pauser'] = value_dict.get('pauser', 0)
        packet.fields['pwuser'] = value_dict.get('pwuser', 0)

        # Generate random data for write
        if packet.direction == 'WRITE':
            packet.fields['pwdata'] = random.randint(0, (1 << self.data_width) - 1)

        self.packet = packet
        return packet.copy()

    def set_constrained_random(self):
        """Set fields using constrained randomization."""
        self.next()
        return self

    def __str__(self):
        """String representation using packet's formatting."""
        return f"APB5 Transaction:\n{self.packet}"

    def formatted(self, compact=False):
        """Return a formatted representation."""
        if compact:
            return f"APB5Transaction({self.packet.formatted(compact=True)})"
        return self.__str__()
