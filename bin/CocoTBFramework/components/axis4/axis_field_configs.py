# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXISFieldConfigs
# Purpose: AXIS Field Configurations - Stream protocol field definitions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Field Configurations - Stream protocol field definitions

This module provides field configurations for AXI4-Stream protocol channels.
AXI4-Stream uses a single T channel (tdata, tstrb, tlast, tid, tdest, tuser, tvalid, tready).

Based on the AXI4-Stream specification and hardware modules.
"""

from ..shared.field_config import FieldConfig, FieldDefinition


class AXISFieldConfigs:
    """
    Factory class for creating AXIS field configurations.
    
    AXI4-Stream protocol uses a single T channel containing:
    - TDATA: Data payload
    - TSTRB: Byte enables (strobe)
    - TLAST: End of packet/frame indicator
    - TID: Stream identifier
    - TDEST: Destination routing
    - TUSER: User-defined sideband data
    - TVALID/TREADY: Handshake signals
    """

    @staticmethod
    def create_t_field_config(data_width: int = 32, id_width: int = 8, 
                             dest_width: int = 4, user_width: int = 1) -> FieldConfig:
        """
        Create field configuration for AXIS T channel.

        Args:
            data_width: Width of TDATA field (8, 16, 32, 64, 128, 256, 512, 1024)
            id_width: Width of TID field (1-16 bits)
            dest_width: Width of TDEST field (1-16 bits) 
            user_width: Width of TUSER field (1-32 bits)

        Returns:
            FieldConfig object for T channel
        """
        strb_width = data_width // 8
        config = FieldConfig()

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

        return config

    @staticmethod
    def create_default_axis_config(data_width: int = 32) -> FieldConfig:
        """
        Create default AXIS configuration with typical parameters.

        Args:
            data_width: Width of data field

        Returns:
            FieldConfig with typical AXIS parameters
        """
        return AXISFieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=8,
            dest_width=4,
            user_width=1
        )

    @staticmethod
    def create_simple_axis_config(data_width: int = 32) -> FieldConfig:
        """
        Create simple AXIS configuration with minimal sideband signals.

        Args:
            data_width: Width of data field

        Returns:
            FieldConfig with minimal AXIS parameters
        """
        return AXISFieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=0,
            dest_width=0,
            user_width=0
        )

    @staticmethod
    def create_axis_config_from_hw_params(data_width: int, id_width: int,
                                         dest_width: int, user_width: int) -> FieldConfig:
        """
        Create AXIS configuration from hardware module parameters.
        
        This matches the parameters used in the axis_master/axis_slave hardware modules.

        Args:
            data_width: AXIS_DATA_WIDTH parameter
            id_width: AXIS_ID_WIDTH parameter
            dest_width: AXIS_DEST_WIDTH parameter
            user_width: AXIS_USER_WIDTH parameter

        Returns:
            FieldConfig matching hardware configuration
        """
        return AXISFieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=id_width,
            dest_width=dest_width,
            user_width=user_width
        )
