# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4FieldConfigHelper
# Purpose: AXI4 Field Configuration Helpers - Clean field configuration for AXI4 channels.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Field Configuration Helpers - Clean field configuration for AXI4 channels.

This module provides field configuration helpers that create properly configured
FieldConfig objects for each AXI4 channel type, working with the ground-up design approach.

Key Design Principles:
1. One function per AXI4 channel type
2. Sensible defaults that match AXI4 specification
3. Clean integration with existing FieldConfig infrastructure
4. Easy to customize and extend
"""

from typing import Dict, List, Tuple
from ..shared.field_config import FieldConfig, FieldDefinition


class AXI4FieldConfigHelper:
    """
    Helper class for creating AXI4 field configurations.

    Provides clean, consistent field configurations for each AXI4 channel
    that work with the existing FieldConfig infrastructure.
    """

    @staticmethod
    def create_aw_field_config(id_width: int = 8, addr_width: int = 32, user_width: int = 1) -> FieldConfig:
        """
        Create field configuration for AXI4 Write Address (AW) channel.

        Args:
            id_width: Width of AWID field (1-16 bits)
            addr_width: Width of AWADDR field (32-64 bits typically)
            user_width: Width of AWUSER field (1-32 bits)

        Returns:
            FieldConfig object for AW channel
        """
        config = FieldConfig()

        # Required AXI4 AW fields in specification order
        config.add_field(FieldDefinition(
            name="id",
            bits=id_width,
            default=0,
            format="hex",
            description="Write Address ID"
        ))

        config.add_field(FieldDefinition(
            name="addr",
            bits=addr_width,
            default=0,
            format="hex",
            description="Write Address"
        ))

        config.add_field(FieldDefinition(
            name="len",
            bits=8,
            default=0,
            format="dec",
            description="Burst Length (0-255)"
        ))

        config.add_field(FieldDefinition(
            name="size",
            bits=3,
            default=2,
            format="dec",
            description="Burst Size (bytes = 2^awsize)"
        ))

        config.add_field(FieldDefinition(
            name="burst",
            bits=2,
            default=1,
            format="dec",
            description="Burst Type (0=FIXED, 1=INCR, 2=WRAP)",
            encoding={0: "FIXED", 1: "INCR", 2: "WRAP"}
        ))

        config.add_field(FieldDefinition(
            name="lock",
            bits=1,
            default=0,
            format="bin",
            description="Lock Type (0=Normal, 1=Exclusive)",
            encoding={0: "Normal", 1: "Exclusive"}
        ))

        config.add_field(FieldDefinition(
            name="cache",
            bits=4,
            default=0,
            format="bin",
            description="Cache Type"
        ))

        config.add_field(FieldDefinition(
            name="prot",
            bits=3,
            default=0,
            format="bin",
            description="Protection Type"
        ))

        config.add_field(FieldDefinition(
            name="qos",
            bits=4,
            default=0,
            format="dec",
            description="Quality of Service"
        ))

        config.add_field(FieldDefinition(
            name="region",
            bits=4,
            default=0,
            format="dec",
            description="Region Identifier"
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
    def create_w_field_config(data_width: int = 32, user_width: int = 1) -> FieldConfig:
        """
        Create field configuration for AXI4 Write Data (W) channel.

        Args:
            data_width: Width of WDATA field (8, 16, 32, 64, 128, 256, 512, 1024)
            user_width: Width of WUSER field (1-32 bits)

        Returns:
            FieldConfig object for W channel
        """
        strb_width = data_width // 8
        config = FieldConfig()

        config.add_field(FieldDefinition(
            name="data",
            bits=data_width,
            default=0,
            format="hex",
            description="Write Data"
        ))

        config.add_field(FieldDefinition(
            name="strb",
            bits=strb_width,
            default=(1 << strb_width) - 1,  # All bytes enabled by default
            format="bin",
            description="Write Strobe (byte enables)"
        ))

        config.add_field(FieldDefinition(
            name="last",
            bits=1,
            default=1,
            format="bin",
            description="Write Last (end of burst)",
            encoding={0: "Not Last", 1: "Last"}
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
    def create_b_field_config(id_width: int = 8, user_width: int = 1) -> FieldConfig:
        """
        Create field configuration for AXI4 Write Response (B) channel.

        Args:
            id_width: Width of BID field (1-16 bits)
            user_width: Width of BUSER field (1-32 bits)

        Returns:
            FieldConfig object for B channel
        """
        config = FieldConfig()

        config.add_field(FieldDefinition(
            name="id",
            bits=id_width,
            default=0,
            format="hex",
            description="Response ID"
        ))

        config.add_field(FieldDefinition(
            name="resp",
            bits=2,
            default=0,
            format="dec",
            description="Write Response",
            encoding={0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
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
    def create_ar_field_config(id_width: int = 8, addr_width: int = 32, user_width: int = 1) -> FieldConfig:
        """
        Create field configuration for AXI4 Read Address (AR) channel.

        Args:
            id_width: Width of ARID field (1-16 bits)
            addr_width: Width of ARADDR field (32-64 bits typically)
            user_width: Width of ARUSER field (1-32 bits)

        Returns:
            FieldConfig object for AR channel
        """
        config = FieldConfig()

        # Required AXI4 AR fields (mirror AW fields with AR prefix)
        config.add_field(FieldDefinition(
            name="id",
            bits=id_width,
            default=0,
            format="hex",
            description="Read Address ID"
        ))

        config.add_field(FieldDefinition(
            name="addr",
            bits=addr_width,
            default=0,
            format="hex",
            description="Read Address"
        ))

        config.add_field(FieldDefinition(
            name="len",
            bits=8,
            default=0,
            format="dec",
            description="Burst Length (0-255)"
        ))

        config.add_field(FieldDefinition(
            name="size",
            bits=3,
            default=2,
            format="dec",
            description="Burst Size (bytes = 2^arsize)"
        ))

        config.add_field(FieldDefinition(
            name="burst",
            bits=2,
            default=1,
            format="dec",
            description="Burst Type (0=FIXED, 1=INCR, 2=WRAP)",
            encoding={0: "FIXED", 1: "INCR", 2: "WRAP"}
        ))

        config.add_field(FieldDefinition(
            name="lock",
            bits=1,
            default=0,
            format="bin",
            description="Lock Type (0=Normal, 1=Exclusive)",
            encoding={0: "Normal", 1: "Exclusive"}
        ))

        config.add_field(FieldDefinition(
            name="cache",
            bits=4,
            default=0,
            format="bin",
            description="Cache Type"
        ))

        config.add_field(FieldDefinition(
            name="prot",
            bits=3,
            default=0,
            format="bin",
            description="Protection Type"
        ))

        config.add_field(FieldDefinition(
            name="qos",
            bits=4,
            default=0,
            format="dec",
            description="Quality of Service"
        ))

        config.add_field(FieldDefinition(
            name="region",
            bits=4,
            default=0,
            format="dec",
            description="Region Identifier"
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
    def create_r_field_config(id_width: int = 8, data_width: int = 32, user_width: int = 1) -> FieldConfig:
        """
        Create field configuration for AXI4 Read Data (R) channel.

        Args:
            id_width: Width of RID field (1-16 bits)
            data_width: Width of RDATA field (8, 16, 32, 64, 128, 256, 512, 1024)
            user_width: Width of RUSER field (1-32 bits)

        Returns:
            FieldConfig object for R channel
        """
        config = FieldConfig()

        config.add_field(FieldDefinition(
            name="id",
            bits=id_width,
            default=0,
            format="hex",
            description="Read Data ID"
        ))

        config.add_field(FieldDefinition(
            name="data",
            bits=data_width,
            default=0,
            format="hex",
            description="Read Data"
        ))

        config.add_field(FieldDefinition(
            name="resp",
            bits=2,
            default=0,
            format="dec",
            description="Read Response",
            encoding={0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        ))

        config.add_field(FieldDefinition(
            name="last",
            bits=1,
            default=1,
            format="bin",
            description="Read Last (end of burst)",
            encoding={0: "Not Last", 1: "Last"}
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
    def create_all_field_configs(id_width: int = 8, addr_width: int = 32,
                                data_width: int = 32, user_width: int = 1,
                                channels: List[str] = ['AW', 'W', 'B', 'AR', 'R']) -> Dict[str, FieldConfig]:
        """
        Create field configurations for all specified AXI4 channels.

        Args:
            id_width: Width of ID fields
            addr_width: Width of address fields
            data_width: Width of data fields
            user_width: Width of user fields (0 to disable user signals)
            channels: List of channels to create configs for

        Returns:
            Dictionary mapping channel names to FieldConfig objects
        """
        creators = {
            'AW': lambda: AXI4FieldConfigHelper.create_aw_field_config(id_width, addr_width, user_width),
            'W':  lambda: AXI4FieldConfigHelper.create_w_field_config(data_width, user_width),
            'B':  lambda: AXI4FieldConfigHelper.create_b_field_config(id_width, user_width),
            'AR': lambda: AXI4FieldConfigHelper.create_ar_field_config(id_width, addr_width, user_width),
            'R':  lambda: AXI4FieldConfigHelper.create_r_field_config(id_width, data_width, user_width),
        }

        configs = {}
        for channel in channels:
            if channel in creators:
                configs[channel] = creators[channel]()
            else:
                raise ValueError(f"Unknown AXI4 channel: {channel}")

        return configs

    @staticmethod
    def validate_axi4_widths(id_width: int, addr_width: int, data_width: int, user_width: int) -> Tuple[bool, List[str]]:
        """
        Validate AXI4 field width parameters.

        Args:
            id_width: ID field width
            addr_width: Address field width
            data_width: Data field width
            user_width: User field width

        Returns:
            Tuple of (is_valid, error_messages)
        """
        errors = []

        # Validate ID width
        if not (1 <= id_width <= 16):
            errors.append(f"id_width must be 1-16 bits, got {id_width}")

        # Validate address width
        if not (1 <= addr_width <= 64):
            errors.append(f"addr_width must be 1-64 bits, got {addr_width}")

        # Validate data width (must be power of 2, 8-1024)
        valid_data_widths = [8, 16, 32, 64, 128, 256, 512, 1024]
        if data_width not in valid_data_widths:
            errors.append(f"data_width must be one of {valid_data_widths}, got {data_width}")

        # Validate user width
        if not (0 <= user_width <= 32):
            errors.append(f"user_width must be 0-32 bits, got {user_width}")

        return len(errors) == 0, errors

    @staticmethod
    def preview_field_configs(id_width: int = 8, addr_width: int = 32,
                            data_width: int = 32, user_width: int = 1,
                            channels: List[str] = ['AW', 'W', 'B', 'AR', 'R']) -> None:
        """
        Preview field configurations for debugging.

        Args:
            id_width: Width of ID fields
            addr_width: Width of address fields
            data_width: Width of data fields
            user_width: Width of user fields
            channels: List of channels to preview
        """
        print(f"\nAXI4 Field Configuration Preview")
        print(f"ID Width: {id_width}, Addr Width: {addr_width}, Data Width: {data_width}, User Width: {user_width}")
        print("-" * 70)

        # Validate widths first
        is_valid, errors = AXI4FieldConfigHelper.validate_axi4_widths(id_width, addr_width, data_width, user_width)
        if not is_valid:
            print("❌ Invalid Parameters:")
            for error in errors:
                print(f"   {error}")
            return

        # Create and preview configs
        try:
            configs = AXI4FieldConfigHelper.create_all_field_configs(id_width, addr_width, data_width, user_width, channels)

            for channel, config in configs.items():
                print(f"\n✅ {channel} Channel ({len(config)} fields, {config.get_total_bits()} total bits):")
                for field_name, field_def in config.items():
                    encoding_str = f" ({', '.join(f'{k}={v}' for k, v in field_def.encoding.items())})" if field_def.encoding else ""
                    print(f"   {field_name:10} [{field_def.bits:2d}] = {field_def.default:4d} ({field_def.format}){encoding_str}")

        except Exception as e:
            print(f"❌ Error creating configs: {e}")


# Convenience functions for common use cases
def create_channel_field_config(channel: str, id_width: int = 8, addr_width: int = 32,
                            data_width: int = 32, user_width: int = 1) -> FieldConfig:
    """
    Convenience function to create field config for a single channel.

    This is referenced in the ground-up design document.
    """
    return AXI4FieldConfigHelper.create_all_field_configs(
        id_width, addr_width, data_width, user_width, [channel]
    )[channel]


def get_axi4_field_configs(id_width: int = 8, addr_width: int = 32,
                        data_width: int = 32, user_width: int = 1,
                        channels: List[str] = ['AW', 'W', 'B', 'AR', 'R']) -> Dict[str, FieldConfig]:
    """
    Get AXI4 field configurations for all specified channels.
    
    This is the function expected by the randomization code.

    Args:
        id_width: Width of ID fields (1-16 bits)
        addr_width: Width of address fields (1-64 bits)
        data_width: Width of data fields (8, 16, 32, 64, 128, 256, 512, 1024)
        user_width: Width of user fields (0-32 bits, 0 to disable)
        channels: List of channels to create configs for

    Returns:
        Dictionary mapping channel names to FieldConfig objects

    Example:
        field_configs = get_axi4_field_configs(id_width=4, data_width=64)
        aw_config = field_configs['AW']
    """
    return AXI4FieldConfigHelper.create_all_field_configs(
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        channels=channels
    )


# Example usage for testing
if __name__ == "__main__":
    print("AXI4 Field Configuration Helpers - Testing")
    print("=" * 50)

    # Test individual channel creation
    aw_config = AXI4FieldConfigHelper.create_aw_field_config(id_width=4, addr_width=32)
    print(f"AW config: {len(aw_config)} fields, {aw_config.get_total_bits()} total bits")

    # Test validation
    is_valid, errors = AXI4FieldConfigHelper.validate_axi4_widths(4, 32, 32, 1)
    print(f"Validation: {is_valid}, errors: {errors}")

    # Test preview
    AXI4FieldConfigHelper.preview_field_configs(id_width=4, data_width=64, channels=['AW', 'W'])

    # Test the new get_axi4_field_configs function
    print("\nTesting get_axi4_field_configs function:")
    field_configs = get_axi4_field_configs(id_width=4, data_width=64, channels=['AW', 'AR'])
    print(f"Got {len(field_configs)} configurations: {list(field_configs.keys())}")
