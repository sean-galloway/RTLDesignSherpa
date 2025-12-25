# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5FieldConfigs
# Purpose: AXIS5 Field Configurations - Stream protocol field definitions with AMBA5 extensions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Field Configurations - Stream protocol field definitions with AMBA5 extensions

This module provides field configurations for AXI5-Stream protocol channels.
AXI5-Stream extends AXI4-Stream with:
- TWAKEUP: Wake-up signaling for power management
- TPARITY: Data parity protection

Based on the AMBA5 AXI-Stream specification.
"""

from ..shared.field_config import FieldConfig, FieldDefinition


class AXIS5FieldConfigs:
    """
    Factory class for creating AXIS5 field configurations.

    AXI5-Stream protocol extends AXI4-Stream with:
    - TWAKEUP: Wake-up signaling for power management
    - TPARITY: Data parity protection (1 bit per byte)
    """

    @staticmethod
    def create_t_field_config(data_width: int = 32, id_width: int = 8,
                               dest_width: int = 4, user_width: int = 1,
                               enable_wakeup: bool = True,
                               enable_parity: bool = False) -> FieldConfig:
        """
        Create field configuration for AXIS5 T channel.

        Args:
            data_width: Width of TDATA field (8, 16, 32, 64, 128, 256, 512, 1024)
            id_width: Width of TID field (1-16 bits)
            dest_width: Width of TDEST field (1-16 bits)
            user_width: Width of TUSER field (1-32 bits)
            enable_wakeup: Enable TWAKEUP field
            enable_parity: Enable TPARITY field

        Returns:
            FieldConfig object for AXIS5 T channel
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
            description="Stream Data"
        ))

        config.add_field(FieldDefinition(
            name="strb",
            bits=strb_width,
            default=(1 << strb_width) - 1,  # All bytes enabled by default
            format="bin",
            description="Stream Strobe (byte enables)"
        ))

        config.add_field(FieldDefinition(
            name="last",
            bits=1,
            default=0,  # Not last by default
            format="bin",
            description="Stream Last (end of packet/frame)",
            encoding={0: "Not Last", 1: "Last"}
        ))

        if id_width > 0:
            config.add_field(FieldDefinition(
                name="id",
                bits=id_width,
                default=0,
                format="hex",
                description="Stream ID"
            ))

        if dest_width > 0:
            config.add_field(FieldDefinition(
                name="dest",
                bits=dest_width,
                default=0,
                format="hex",
                description="Stream Destination"
            ))

        if user_width > 0:
            config.add_field(FieldDefinition(
                name="user",
                bits=user_width,
                default=0,
                format="bin",
                description="User Signal"
            ))

        # AXIS5 extension fields
        if enable_wakeup:
            config.add_field(FieldDefinition(
                name="wakeup",
                bits=1,
                default=0,
                format="dec",
                description="Wake-up Signal",
                encoding={0: "Inactive", 1: "Active"}
            ))

        if enable_parity:
            config.add_field(FieldDefinition(
                name="parity",
                bits=parity_width,
                default=0,
                format="bin",
                description="Data Parity (1 bit per byte)"
            ))

            config.add_field(FieldDefinition(
                name="parity_error",
                bits=1,
                default=0,
                format="dec",
                description="Parity Error Indicator",
                encoding={0: "No Error", 1: "Error"}
            ))

        return config

    @staticmethod
    def create_axis5_field_config(data_width: int = 32,
                                   enable_wakeup: bool = True,
                                   enable_parity: bool = False) -> FieldConfig:
        """
        Create default AXIS5 configuration with typical parameters.

        Args:
            data_width: Width of data field
            enable_wakeup: Enable TWAKEUP field
            enable_parity: Enable TPARITY field

        Returns:
            FieldConfig with typical AXIS5 parameters
        """
        return AXIS5FieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=8,
            dest_width=4,
            user_width=1,
            enable_wakeup=enable_wakeup,
            enable_parity=enable_parity
        )

    @staticmethod
    def create_simple_axis5_config(data_width: int = 32,
                                    enable_wakeup: bool = True,
                                    enable_parity: bool = False) -> FieldConfig:
        """
        Create simple AXIS5 configuration with minimal sideband signals.

        Args:
            data_width: Width of data field
            enable_wakeup: Enable TWAKEUP field
            enable_parity: Enable TPARITY field

        Returns:
            FieldConfig with minimal AXIS5 parameters
        """
        return AXIS5FieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=0,
            dest_width=0,
            user_width=0,
            enable_wakeup=enable_wakeup,
            enable_parity=enable_parity
        )

    @staticmethod
    def create_axis5_config_from_hw_params(data_width: int, id_width: int,
                                           dest_width: int, user_width: int,
                                           enable_wakeup: bool = True,
                                           enable_parity: bool = False) -> FieldConfig:
        """
        Create AXIS5 configuration from hardware module parameters.

        This matches the parameters used in the axis5_master/axis5_slave hardware modules.

        Args:
            data_width: AXIS_DATA_WIDTH parameter
            id_width: AXIS_ID_WIDTH parameter
            dest_width: AXIS_DEST_WIDTH parameter
            user_width: AXIS_USER_WIDTH parameter
            enable_wakeup: ENABLE_WAKEUP parameter
            enable_parity: ENABLE_PARITY parameter

        Returns:
            FieldConfig matching hardware configuration
        """
        return AXIS5FieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=id_width,
            dest_width=dest_width,
            user_width=user_width,
            enable_wakeup=enable_wakeup,
            enable_parity=enable_parity
        )

    @staticmethod
    def create_parity_only_config(data_width: int = 32) -> FieldConfig:
        """
        Create AXIS5 configuration with parity only (no wakeup).

        Args:
            data_width: Width of data field

        Returns:
            FieldConfig with parity but no wakeup
        """
        return AXIS5FieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=8,
            dest_width=4,
            user_width=1,
            enable_wakeup=False,
            enable_parity=True
        )

    @staticmethod
    def create_full_axis5_config(data_width: int = 32) -> FieldConfig:
        """
        Create AXIS5 configuration with all extensions enabled.

        Args:
            data_width: Width of data field

        Returns:
            FieldConfig with all AXIS5 features
        """
        return AXIS5FieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=8,
            dest_width=4,
            user_width=1,
            enable_wakeup=True,
            enable_parity=True
        )
