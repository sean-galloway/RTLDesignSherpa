# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXIPacket
# Purpose: GAXI Packet class - minimal protocol-specific extensions to base Packet class
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""GAXI Packet class - minimal protocol-specific extensions to base Packet class"""
from typing import Optional

from ..shared.packet import Packet
from ..shared.field_config import FieldConfig
from ..shared.flex_randomizer import FlexRandomizer


class GAXIPacket(Packet):
    """
    Packet class for GAXI protocol.

    Minimal extension of base Packet class that only adds GAXI-specific
    randomizer handling. All field management, masking, pack/unpack, and
    formatting functionality is inherited from the base Packet class.
    """

    def __init__(self, field_config: Optional[FieldConfig] = None,
                    master_randomizer: Optional[FlexRandomizer] = None,
                    slave_randomizer: Optional[FlexRandomizer] = None, **kwargs):
        """
        Initialize a GAXI packet.

        Args:
            field_config: Field configuration (or dict that will be converted)
            master_randomizer: Optional randomizer for master interface timing
            slave_randomizer: Optional randomizer for slave interface timing
            **kwargs: Initial field values passed to parent
        """
        # Call parent constructor (handles field_config conversion, field initialization, etc.)
        super().__init__(field_config, **kwargs)

        # Only add GAXI-specific properties
        self.master_randomizer = master_randomizer
        self.slave_randomizer = slave_randomizer
        self.master_delay = None
        self.slave_delay = None

    def set_master_randomizer(self, randomizer: FlexRandomizer):
        """Set the master randomizer"""
        self.master_randomizer = randomizer
        self.master_delay = None  # Reset cached delay

    def set_slave_randomizer(self, randomizer: FlexRandomizer):
        """Set the slave randomizer"""
        self.slave_randomizer = randomizer
        self.slave_delay = None  # Reset cached delay

    def get_master_delay(self) -> int:
        """
        Get the delay for the master interface (valid delay).

        Returns:
            Delay in cycles (0 if no randomizer)
        """
        if self.master_delay is None and self.master_randomizer:
            self.master_delay = self.master_randomizer.choose_valid_delay()
        return self.master_delay or 0

    def get_slave_delay(self) -> int:
        """
        Get the delay for the slave interface (ready delay).

        Returns:
            Delay in cycles (0 if no randomizer)
        """
        if self.slave_delay is None and self.slave_randomizer:
            self.slave_delay = self.slave_randomizer.choose_ready_delay()
        return self.slave_delay or 0
