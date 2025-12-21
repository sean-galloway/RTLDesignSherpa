# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5FieldConfigHelper
# Purpose: AXI5 Field Configuration Helpers - Clean field configuration for AXI5 channels.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-15

"""
AXI5 Field Configuration Helpers - Clean field configuration for AXI5 channels.

This module provides field configuration helpers that create properly configured
FieldConfig objects for each AXI5 channel type, working with the ground-up design approach.

Key Design Principles:
1. One function per AXI5 channel type
2. Sensible defaults that match AXI5 specification
3. Clean integration with existing FieldConfig infrastructure
4. Easy to customize and extend

AXI5 Changes from AXI4:
- Removed: ARREGION, AWREGION
- Added: NSAID, TRACE, MPAM, MECID, UNIQUE, ATOP (write only), TAGOP, TAG
- Added: CHUNKEN (AR only), CHUNKV, CHUNKNUM, CHUNKSTRB (R only)
- Added: POISON (W/R), TAGUPDATE (W), TAGMATCH (B/R)
"""

from typing import Dict, List, Tuple
from ..shared.field_config import FieldConfig, FieldDefinition


class AXI5FieldConfigHelper:
    """
    Helper class for creating AXI5 field configurations.

    Provides clean, consistent field configurations for each AXI5 channel
    that work with the existing FieldConfig infrastructure.
    """

    @staticmethod
    def create_aw_field_config(
        id_width: int = 8,
        addr_width: int = 32,
        user_width: int = 1,
        nsaid_width: int = 4,
        mpam_width: int = 11,
        mecid_width: int = 16,
        atop_width: int = 6,
        tagop_width: int = 2,
        tag_width: int = 4,
        data_width: int = 32
    ) -> FieldConfig:
        """
        Create field configuration for AXI5 Write Address (AW) channel.

        Args:
            id_width: Width of AWID field (1-16 bits)
            addr_width: Width of AWADDR field (32-64 bits typically)
            user_width: Width of AWUSER field (1-32 bits)
            nsaid_width: Width of AWNSAID field (typically 4 bits)
            mpam_width: Width of AWMPAM field (typically 11 bits)
            mecid_width: Width of AWMECID field (typically 16 bits)
            atop_width: Width of AWATOP field (typically 6 bits)
            tagop_width: Width of AWTAGOP field (typically 2 bits)
            tag_width: Width of single tag (typically 4 bits)
            data_width: Data width for calculating NUM_TAGS

        Returns:
            FieldConfig object for AW channel
        """
        # Calculate number of tags based on data width (one tag per 128 bits)
        num_tags = max(1, data_width // 128)
        total_tag_width = tag_width * num_tags

        config = FieldConfig()

        # Required AXI5 AW fields in specification order
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

        # Note: AWREGION removed in AXI5

        if user_width > 0:
            config.add_field(FieldDefinition(
                name="user",
                bits=user_width,
                default=0,
                format="bin",
                description="User Signal"
            ))

        # AXI5 specific signals
        config.add_field(FieldDefinition(
            name="atop",
            bits=atop_width,
            default=0,
            format="hex",
            description="Atomic Operation Type"
        ))

        config.add_field(FieldDefinition(
            name="nsaid",
            bits=nsaid_width,
            default=0,
            format="hex",
            description="Non-secure Access ID"
        ))

        config.add_field(FieldDefinition(
            name="trace",
            bits=1,
            default=0,
            format="bin",
            description="Transaction Trace Enable"
        ))

        config.add_field(FieldDefinition(
            name="mpam",
            bits=mpam_width,
            default=0,
            format="hex",
            description="Memory Partitioning and Monitoring"
        ))

        config.add_field(FieldDefinition(
            name="mecid",
            bits=mecid_width,
            default=0,
            format="hex",
            description="Memory Encryption Context ID"
        ))

        config.add_field(FieldDefinition(
            name="unique",
            bits=1,
            default=0,
            format="bin",
            description="Unique/Exclusive Access"
        ))

        config.add_field(FieldDefinition(
            name="tagop",
            bits=tagop_width,
            default=0,
            format="dec",
            description="Memory Tagging Operation",
            encoding={0: "Invalid", 1: "Transfer", 2: "Update", 3: "Match"}
        ))

        config.add_field(FieldDefinition(
            name="tag",
            bits=total_tag_width,
            default=0,
            format="hex",
            description="Memory Tags"
        ))

        return config

    @staticmethod
    def create_w_field_config(
        data_width: int = 32,
        user_width: int = 1,
        tag_width: int = 4
    ) -> FieldConfig:
        """
        Create field configuration for AXI5 Write Data (W) channel.

        Args:
            data_width: Width of WDATA field (8, 16, 32, 64, 128, 256, 512, 1024)
            user_width: Width of WUSER field (1-32 bits)
            tag_width: Width of single tag (typically 4 bits)

        Returns:
            FieldConfig object for W channel
        """
        strb_width = data_width // 8
        num_tags = max(1, data_width // 128)
        total_tag_width = tag_width * num_tags

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

        # AXI5 specific signals
        config.add_field(FieldDefinition(
            name="poison",
            bits=1,
            default=0,
            format="bin",
            description="Data Poison Indicator"
        ))

        config.add_field(FieldDefinition(
            name="tag",
            bits=total_tag_width,
            default=0,
            format="hex",
            description="Memory Tags"
        ))

        config.add_field(FieldDefinition(
            name="tagupdate",
            bits=num_tags,
            default=0,
            format="bin",
            description="Tag Update Indicators"
        ))

        return config

    @staticmethod
    def create_b_field_config(
        id_width: int = 8,
        user_width: int = 1,
        tag_width: int = 4,
        data_width: int = 32
    ) -> FieldConfig:
        """
        Create field configuration for AXI5 Write Response (B) channel.

        Args:
            id_width: Width of BID field (1-16 bits)
            user_width: Width of BUSER field (1-32 bits)
            tag_width: Width of single tag (typically 4 bits)
            data_width: Data width for calculating NUM_TAGS

        Returns:
            FieldConfig object for B channel
        """
        num_tags = max(1, data_width // 128)
        total_tag_width = tag_width * num_tags

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

        # AXI5 specific signals
        config.add_field(FieldDefinition(
            name="trace",
            bits=1,
            default=0,
            format="bin",
            description="Transaction Trace Enable"
        ))

        config.add_field(FieldDefinition(
            name="tag",
            bits=total_tag_width,
            default=0,
            format="hex",
            description="Memory Tags"
        ))

        config.add_field(FieldDefinition(
            name="tagmatch",
            bits=1,
            default=0,
            format="bin",
            description="Tag Match Result"
        ))

        return config

    @staticmethod
    def create_ar_field_config(
        id_width: int = 8,
        addr_width: int = 32,
        user_width: int = 1,
        nsaid_width: int = 4,
        mpam_width: int = 11,
        mecid_width: int = 16,
        tagop_width: int = 2
    ) -> FieldConfig:
        """
        Create field configuration for AXI5 Read Address (AR) channel.

        Args:
            id_width: Width of ARID field (1-16 bits)
            addr_width: Width of ARADDR field (32-64 bits typically)
            user_width: Width of ARUSER field (1-32 bits)
            nsaid_width: Width of ARNSAID field (typically 4 bits)
            mpam_width: Width of ARMPAM field (typically 11 bits)
            mecid_width: Width of ARMECID field (typically 16 bits)
            tagop_width: Width of ARTAGOP field (typically 2 bits)

        Returns:
            FieldConfig object for AR channel
        """
        config = FieldConfig()

        # Required AXI5 AR fields (mirror AW fields with AR prefix, minus ATOP)
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

        # Note: ARREGION removed in AXI5

        if user_width > 0:
            config.add_field(FieldDefinition(
                name="user",
                bits=user_width,
                default=0,
                format="bin",
                description="User Signal"
            ))

        # AXI5 specific signals
        config.add_field(FieldDefinition(
            name="nsaid",
            bits=nsaid_width,
            default=0,
            format="hex",
            description="Non-secure Access ID"
        ))

        config.add_field(FieldDefinition(
            name="trace",
            bits=1,
            default=0,
            format="bin",
            description="Transaction Trace Enable"
        ))

        config.add_field(FieldDefinition(
            name="mpam",
            bits=mpam_width,
            default=0,
            format="hex",
            description="Memory Partitioning and Monitoring"
        ))

        config.add_field(FieldDefinition(
            name="mecid",
            bits=mecid_width,
            default=0,
            format="hex",
            description="Memory Encryption Context ID"
        ))

        config.add_field(FieldDefinition(
            name="unique",
            bits=1,
            default=0,
            format="bin",
            description="Unique/Exclusive Access"
        ))

        config.add_field(FieldDefinition(
            name="chunken",
            bits=1,
            default=0,
            format="bin",
            description="Chunking Enable"
        ))

        config.add_field(FieldDefinition(
            name="tagop",
            bits=tagop_width,
            default=0,
            format="dec",
            description="Memory Tagging Operation",
            encoding={0: "Invalid", 1: "Transfer", 2: "Update", 3: "Match"}
        ))

        return config

    @staticmethod
    def create_r_field_config(
        id_width: int = 8,
        data_width: int = 32,
        user_width: int = 1,
        chunknum_width: int = 4,
        tag_width: int = 4
    ) -> FieldConfig:
        """
        Create field configuration for AXI5 Read Data (R) channel.

        Args:
            id_width: Width of RID field (1-16 bits)
            data_width: Width of RDATA field (8, 16, 32, 64, 128, 256, 512, 1024)
            user_width: Width of RUSER field (1-32 bits)
            chunknum_width: Width of RCHUNKNUM field (typically 4 bits)
            tag_width: Width of single tag (typically 4 bits)

        Returns:
            FieldConfig object for R channel
        """
        num_tags = max(1, data_width // 128)
        total_tag_width = tag_width * num_tags
        chunk_strb_width = max(1, data_width // 128)

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

        # AXI5 specific signals
        config.add_field(FieldDefinition(
            name="trace",
            bits=1,
            default=0,
            format="bin",
            description="Transaction Trace Enable"
        ))

        config.add_field(FieldDefinition(
            name="poison",
            bits=1,
            default=0,
            format="bin",
            description="Data Poison Indicator"
        ))

        config.add_field(FieldDefinition(
            name="chunkv",
            bits=1,
            default=0,
            format="bin",
            description="Chunk Valid"
        ))

        config.add_field(FieldDefinition(
            name="chunknum",
            bits=chunknum_width,
            default=0,
            format="dec",
            description="Chunk Number"
        ))

        config.add_field(FieldDefinition(
            name="chunkstrb",
            bits=chunk_strb_width,
            default=0,
            format="bin",
            description="Chunk Strobe"
        ))

        config.add_field(FieldDefinition(
            name="tag",
            bits=total_tag_width,
            default=0,
            format="hex",
            description="Memory Tags"
        ))

        config.add_field(FieldDefinition(
            name="tagmatch",
            bits=1,
            default=0,
            format="bin",
            description="Tag Match Result"
        ))

        return config

    @staticmethod
    def create_all_field_configs(
        id_width: int = 8,
        addr_width: int = 32,
        data_width: int = 32,
        user_width: int = 1,
        nsaid_width: int = 4,
        mpam_width: int = 11,
        mecid_width: int = 16,
        atop_width: int = 6,
        tagop_width: int = 2,
        tag_width: int = 4,
        chunknum_width: int = 4,
        channels: List[str] = None
    ) -> Dict[str, FieldConfig]:
        """
        Create field configurations for all specified AXI5 channels.

        Args:
            id_width: Width of ID fields
            addr_width: Width of address fields
            data_width: Width of data fields
            user_width: Width of user fields (0 to disable user signals)
            nsaid_width: Width of NSAID fields
            mpam_width: Width of MPAM fields
            mecid_width: Width of MECID fields
            atop_width: Width of ATOP field (AW only)
            tagop_width: Width of TAGOP fields
            tag_width: Width of single tag
            chunknum_width: Width of CHUNKNUM field (R only)
            channels: List of channels to create configs for

        Returns:
            Dictionary mapping channel names to FieldConfig objects
        """
        if channels is None:
            channels = ['AW', 'W', 'B', 'AR', 'R']

        creators = {
            'AW': lambda: AXI5FieldConfigHelper.create_aw_field_config(
                id_width, addr_width, user_width, nsaid_width, mpam_width,
                mecid_width, atop_width, tagop_width, tag_width, data_width
            ),
            'W': lambda: AXI5FieldConfigHelper.create_w_field_config(
                data_width, user_width, tag_width
            ),
            'B': lambda: AXI5FieldConfigHelper.create_b_field_config(
                id_width, user_width, tag_width, data_width
            ),
            'AR': lambda: AXI5FieldConfigHelper.create_ar_field_config(
                id_width, addr_width, user_width, nsaid_width, mpam_width,
                mecid_width, tagop_width
            ),
            'R': lambda: AXI5FieldConfigHelper.create_r_field_config(
                id_width, data_width, user_width, chunknum_width, tag_width
            ),
        }

        configs = {}
        for channel in channels:
            if channel in creators:
                configs[channel] = creators[channel]()
            else:
                raise ValueError(f"Unknown AXI5 channel: {channel}")

        return configs

    @staticmethod
    def validate_axi5_widths(
        id_width: int,
        addr_width: int,
        data_width: int,
        user_width: int,
        nsaid_width: int = 4,
        mpam_width: int = 11,
        mecid_width: int = 16,
        tag_width: int = 4
    ) -> Tuple[bool, List[str]]:
        """
        Validate AXI5 field width parameters.

        Args:
            id_width: ID field width
            addr_width: Address field width
            data_width: Data field width
            user_width: User field width
            nsaid_width: NSAID field width
            mpam_width: MPAM field width
            mecid_width: MECID field width
            tag_width: Single tag width

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

        # Validate AXI5-specific widths
        if not (1 <= nsaid_width <= 8):
            errors.append(f"nsaid_width must be 1-8 bits, got {nsaid_width}")

        if not (1 <= mpam_width <= 16):
            errors.append(f"mpam_width must be 1-16 bits, got {mpam_width}")

        if not (1 <= mecid_width <= 32):
            errors.append(f"mecid_width must be 1-32 bits, got {mecid_width}")

        if not (1 <= tag_width <= 8):
            errors.append(f"tag_width must be 1-8 bits, got {tag_width}")

        return len(errors) == 0, errors

    @staticmethod
    def preview_field_configs(
        id_width: int = 8,
        addr_width: int = 32,
        data_width: int = 32,
        user_width: int = 1,
        nsaid_width: int = 4,
        mpam_width: int = 11,
        mecid_width: int = 16,
        channels: List[str] = None
    ) -> None:
        """
        Preview field configurations for debugging.

        Args:
            id_width: Width of ID fields
            addr_width: Width of address fields
            data_width: Width of data fields
            user_width: Width of user fields
            nsaid_width: Width of NSAID fields
            mpam_width: Width of MPAM fields
            mecid_width: Width of MECID fields
            channels: List of channels to preview
        """
        if channels is None:
            channels = ['AW', 'W', 'B', 'AR', 'R']

        print(f"\nAXI5 Field Configuration Preview")
        print(f"ID Width: {id_width}, Addr Width: {addr_width}, Data Width: {data_width}, User Width: {user_width}")
        print(f"NSAID Width: {nsaid_width}, MPAM Width: {mpam_width}, MECID Width: {mecid_width}")
        print("-" * 80)

        # Validate widths first
        is_valid, errors = AXI5FieldConfigHelper.validate_axi5_widths(
            id_width, addr_width, data_width, user_width, nsaid_width, mpam_width, mecid_width
        )
        if not is_valid:
            print("Invalid Parameters:")
            for error in errors:
                print(f"   {error}")
            return

        # Create and preview configs
        try:
            configs = AXI5FieldConfigHelper.create_all_field_configs(
                id_width, addr_width, data_width, user_width,
                nsaid_width, mpam_width, mecid_width, channels=channels
            )

            for channel, config in configs.items():
                print(f"\n{channel} Channel ({len(config)} fields, {config.get_total_bits()} total bits):")
                for field_name, field_def in config.items():
                    encoding_str = f" ({', '.join(f'{k}={v}' for k, v in field_def.encoding.items())})" if field_def.encoding else ""
                    print(f"   {field_name:12} [{field_def.bits:3d}] = {field_def.default:6d} ({field_def.format}){encoding_str}")

        except Exception as e:
            print(f"Error creating configs: {e}")


# Convenience functions for common use cases
def create_channel_field_config(
    channel: str,
    id_width: int = 8,
    addr_width: int = 32,
    data_width: int = 32,
    user_width: int = 1,
    nsaid_width: int = 4,
    mpam_width: int = 11,
    mecid_width: int = 16
) -> FieldConfig:
    """
    Convenience function to create field config for a single channel.

    This is referenced in the ground-up design document.
    """
    return AXI5FieldConfigHelper.create_all_field_configs(
        id_width, addr_width, data_width, user_width,
        nsaid_width, mpam_width, mecid_width, channels=[channel]
    )[channel]


def get_axi5_field_configs(
    id_width: int = 8,
    addr_width: int = 32,
    data_width: int = 32,
    user_width: int = 1,
    nsaid_width: int = 4,
    mpam_width: int = 11,
    mecid_width: int = 16,
    atop_width: int = 6,
    tagop_width: int = 2,
    tag_width: int = 4,
    chunknum_width: int = 4,
    channels: List[str] = None
) -> Dict[str, FieldConfig]:
    """
    Get AXI5 field configurations for all specified channels.

    This is the function expected by the randomization code.

    Args:
        id_width: Width of ID fields (1-16 bits)
        addr_width: Width of address fields (1-64 bits)
        data_width: Width of data fields (8, 16, 32, 64, 128, 256, 512, 1024)
        user_width: Width of user fields (0-32 bits, 0 to disable)
        nsaid_width: Width of NSAID fields (1-8 bits)
        mpam_width: Width of MPAM fields (1-16 bits)
        mecid_width: Width of MECID fields (1-32 bits)
        atop_width: Width of ATOP field (AW only)
        tagop_width: Width of TAGOP fields
        tag_width: Width of single tag
        chunknum_width: Width of CHUNKNUM field (R only)
        channels: List of channels to create configs for

    Returns:
        Dictionary mapping channel names to FieldConfig objects

    Example:
        field_configs = get_axi5_field_configs(id_width=4, data_width=64)
        aw_config = field_configs['AW']
    """
    if channels is None:
        channels = ['AW', 'W', 'B', 'AR', 'R']

    return AXI5FieldConfigHelper.create_all_field_configs(
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        nsaid_width=nsaid_width,
        mpam_width=mpam_width,
        mecid_width=mecid_width,
        atop_width=atop_width,
        tagop_width=tagop_width,
        tag_width=tag_width,
        chunknum_width=chunknum_width,
        channels=channels
    )


# Example usage for testing
if __name__ == "__main__":
    print("AXI5 Field Configuration Helpers - Testing")
    print("=" * 60)

    # Test individual channel creation
    aw_config = AXI5FieldConfigHelper.create_aw_field_config(id_width=4, addr_width=32)
    print(f"AW config: {len(aw_config)} fields, {aw_config.get_total_bits()} total bits")

    # Test validation
    is_valid, errors = AXI5FieldConfigHelper.validate_axi5_widths(4, 32, 32, 1)
    print(f"Validation: {is_valid}, errors: {errors}")

    # Test preview
    AXI5FieldConfigHelper.preview_field_configs(id_width=4, data_width=128, channels=['AW', 'W', 'R'])

    # Test the new get_axi5_field_configs function
    print("\nTesting get_axi5_field_configs function:")
    field_configs = get_axi5_field_configs(id_width=4, data_width=64, channels=['AW', 'AR'])
    print(f"Got {len(field_configs)} configurations: {list(field_configs.keys())}")
