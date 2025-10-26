# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBGAXIConfig
# Purpose: APB-GAXI Configuration Module
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB-GAXI Configuration Module

This module provides configurable APB-GAXI interface configurations using the FieldConfig
framework. It supports parameterized field configurations and signal mappings.

UPDATED: All field additions reversed to use MSB-first ordering scheme.
"""

from typing import Dict, Any, Optional
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class APBGAXIConfig:
    """
    Configurable APB-GAXI interface configuration factory.

    This class provides methods to create standard APB-GAXI configurations with
    customizable parameters like address width, data width, etc.
    """

    def __init__(self, addr_width: int = 32, data_width: int = 32, strb_width: Optional[int] = None):
        """
        Initialize APB-GAXI configuration with common parameters.

        Args:
            addr_width: Address bus width in bits
            data_width: Data bus width in bits
            strb_width: Strobe width in bits (defaults to data_width // 8)
        """
        self.addr_width = addr_width
        self.data_width = data_width
        self.strb_width = strb_width if strb_width is not None else (data_width // 8)

    def create_cmd_field_config(self) -> FieldConfig:
        """
        Create command interface field configuration.

        Returns:
            FieldConfig with cmd, addr, data, and strb fields in MSB-first order
        """
        config = FieldConfig()

        # REVERSED ORDER: pprot field first (gets MSB positions)
        prot_width = 3
        config.add_field(FieldDefinition(
            name="pprot",
            bits=prot_width,
            default=0,
            format="bin",
            display_width=prot_width,
            description=f"Protection attributes ({prot_width}-bit)",
            encoding={
                0b000: "NORMAL",
                0b001: "PRIVILEGED",
                0b010: "NONSECURE",
                0b011: "PRIV_NONSECURE",
                0b100: "INSTR",
                0b101: "PRIV_INSTR",
                0b110: "NONSECURE_INSTR",
                0b111: "PRIV_NONSECURE_INSTR"
            } if prot_width >= 3 else None
        ))

        # pstrb field - byte strobes
        config.add_field(FieldDefinition(
            name="pstrb",
            bits=self.strb_width,
            default=(1 << self.strb_width) - 1,  # All strobes enabled by default
            format="bin",
            display_width=self.strb_width,
            description=f"Byte strobes ({self.strb_width}-bit)"
        ))

        # pwdata field - write data
        config.add_field(FieldDefinition(
            name="pwdata",
            bits=self.data_width,
            default=0,
            format="hex",
            display_width=(self.data_width + 3) // 4,  # Hex digits needed
            description=f"Write data ({self.data_width}-bit)"
        ))

        # paddr field - address field
        config.add_field(FieldDefinition(
            name="paddr",
            bits=self.addr_width,
            default=0,
            format="hex",
            display_width=(self.addr_width + 3) // 4,  # Hex digits needed
            description=f"Address ({self.addr_width}-bit)"
        ))

        # pwrite field - 1 bit indicating read (0) or write (1) (gets LSB position)
        config.add_field(FieldDefinition(
            name="pwrite",
            bits=1,
            default=0,
            format="dec",
            description="Write enable (0=read, 1=write)",
            encoding={0: "READ", 1: "WRITE"}
        ))

        return config

    def create_rsp_field_config(self) -> FieldConfig:
        """
        Create response interface field configuration.

        Returns:
            FieldConfig with data and err fields in MSB-first order
        """
        config = FieldConfig()

        # REVERSED ORDER: pslverr field first (gets MSB position)
        config.add_field(FieldDefinition(
            name="pslverr",
            bits=1,
            default=0,
            format="dec",
            description="Slave error (0=OK, 1=ERROR)",
            encoding={0: "OK", 1: "ERROR"}
        ))

        # prdata field - read data (gets LSB positions)
        config.add_field(FieldDefinition(
            name="prdata",
            bits=self.data_width,
            default=0,
            format="hex",
            display_width=(self.data_width + 3) // 4,  # Hex digits needed
            description=f"Read data ({self.data_width}-bit)"
        ))

        return config
