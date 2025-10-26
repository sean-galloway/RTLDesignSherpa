# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL4FieldConfigHelper
# Purpose: AXIL4 (AXI4-Lite) Field Configurations - COMPLETE UPDATED FILE
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 (AXI4-Lite) Field Configurations - COMPLETE UPDATED FILE

CHANGES:
1. ✅ SIMPLIFIED: Removed all user signal support (not in AXIL4 spec)
2. ✅ CLEANED: Only essential AXIL4 signals included
3. ✅ OPTIMIZED: Minimal field configurations for register access

This file is ready to replace the existing axil4_field_configs.py
"""

from typing import Dict, List, Tuple
from ..shared.field_config import FieldConfig, FieldDefinition


class AXIL4FieldConfigHelper:
    """
    Helper class for creating AXIL4 (AXI4-Lite) field configurations.
    
    AXIL4-COMPLIANT: Only includes signals actually in the AXIL4 specification.
    No user signals, no burst fields, minimal register-oriented design.
    """

    @staticmethod
    def create_aw_field_config(addr_width: int = 32) -> FieldConfig:
        """
        Create field configuration for AXIL4 Write Address (AW) channel.
        
        AXIL4-COMPLIANT: Only AWADDR and AWPROT (no user signals).
        
        Args:
            addr_width: Width of AWADDR field (32-64 bits typically)
        
        Returns:
            FieldConfig object for AXIL4 AW channel
        """
        config = FieldConfig()

        # AXIL4 AW channel signals (specification compliant)
        config.add_field(FieldDefinition(
            name="addr",
            bits=addr_width,
            default=0,
            format="hex",
            description="Write Address"
        ))

        config.add_field(FieldDefinition(
            name="prot",
            bits=3,
            default=0,
            format="bin",
            description="Protection Type"
        ))

        return config

    @staticmethod
    def create_w_field_config(data_width: int = 32) -> FieldConfig:
        """
        Create field configuration for AXIL4 Write Data (W) channel.
        
        AXIL4-COMPLIANT: Only WDATA and WSTRB (no user signals).
        
        Args:
            data_width: Width of WDATA field (8, 16, 32, 64 bits typically)
        
        Returns:
            FieldConfig object for AXIL4 W channel
        """
        config = FieldConfig()

        config.add_field(FieldDefinition(
            name="data",
            bits=data_width,
            default=0,
            format="hex",
            description="Write Data"
        ))

        # Write strobes for byte-level write enable
        strb_width = data_width // 8
        config.add_field(FieldDefinition(
            name="strb",
            bits=strb_width,
            default=(1 << strb_width) - 1,  # All strobes enabled by default
            format="bin",
            description="Write Strobes"
        ))

        return config

    @staticmethod
    def create_b_field_config() -> FieldConfig:
        """
        Create field configuration for AXIL4 Write Response (B) channel.
        
        AXIL4-COMPLIANT: Only BRESP (no user signals).
        
        Returns:
            FieldConfig object for AXIL4 B channel
        """
        config = FieldConfig()

        config.add_field(FieldDefinition(
            name="resp",
            bits=2,
            default=0,
            format="dec",
            description="Write Response",
            encoding={0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        ))

        return config

    @staticmethod
    def create_ar_field_config(addr_width: int = 32) -> FieldConfig:
        """
        Create field configuration for AXIL4 Read Address (AR) channel.
        
        AXIL4-COMPLIANT: Only ARADDR and ARPROT (no user signals).
        
        Args:
            addr_width: Width of ARADDR field (32-64 bits typically)
        
        Returns:
            FieldConfig object for AXIL4 AR channel
        """
        config = FieldConfig()

        config.add_field(FieldDefinition(
            name="addr",
            bits=addr_width,
            default=0,
            format="hex",
            description="Read Address"
        ))

        config.add_field(FieldDefinition(
            name="prot",
            bits=3,
            default=0,
            format="bin",
            description="Protection Type"
        ))

        return config

    @staticmethod
    def create_r_field_config(data_width: int = 32) -> FieldConfig:
        """
        Create field configuration for AXIL4 Read Data (R) channel.
        
        AXIL4-COMPLIANT: Only RDATA and RRESP (no user signals).
        
        Args:
            data_width: Width of RDATA field (8, 16, 32, 64 bits typically)
        
        Returns:
            FieldConfig object for AXIL4 R channel
        """
        config = FieldConfig()

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

        return config

    @staticmethod
    def create_all_field_configs(addr_width: int = 32, data_width: int = 32,
                                channels: List[str] = ['AW', 'W', 'B', 'AR', 'R']) -> Dict[str, FieldConfig]:
        """
        Create field configurations for all specified AXIL4 channels.
        
        SIMPLIFIED: No user_width parameter - AXIL4 doesn't use user signals.
        
        Args:
            addr_width: Address bus width
            data_width: Data bus width
            channels: List of channels to create configs for
        
        Returns:
            Dictionary mapping channel names to FieldConfig objects
        """
        configs = {}
        
        if 'AW' in channels:
            configs['AW'] = AXIL4FieldConfigHelper.create_aw_field_config(addr_width)
        
        if 'W' in channels:
            configs['W'] = AXIL4FieldConfigHelper.create_w_field_config(data_width)
        
        if 'B' in channels:
            configs['B'] = AXIL4FieldConfigHelper.create_b_field_config()
        
        if 'AR' in channels:
            configs['AR'] = AXIL4FieldConfigHelper.create_ar_field_config(addr_width)
        
        if 'R' in channels:
            configs['R'] = AXIL4FieldConfigHelper.create_r_field_config(data_width)
        
        return configs


# Convenience function for standard configurations
def get_axil4_field_configs(addr_width: int = 32, data_width: int = 32) -> Dict[str, FieldConfig]:
    """
    Get standard AXIL4 field configurations for all channels.
    
    SIMPLIFIED: No user_width parameter - AXIL4 is specification-compliant minimal.
    
    Args:
        addr_width: Address width (default: 32)
        data_width: Data width (default: 32)  
    
    Returns:
        Dictionary with all AXIL4 channel field configurations
    """
    return AXIL4FieldConfigHelper.create_all_field_configs(addr_width, data_width)


# Example usage and testing
if __name__ == "__main__":
    print("AXIL4 Field Configurations - Specification Compliant")
    print("=" * 60)
    
    # Test individual channel configs
    aw_config = AXIL4FieldConfigHelper.create_aw_field_config()
    print(f"AW Config: {len(aw_config.field_definitions)} fields")
    for field in aw_config.field_definitions:
        print(f"  - {field.name}: {field.bits} bits, default=0x{field.default:X}")
    
    # Test W config
    w_config = AXIL4FieldConfigHelper.create_w_field_config(data_width=32)
    print(f"\nW Config: {len(w_config.field_definitions)} fields")
    for field in w_config.field_definitions:
        print(f"  - {field.name}: {field.bits} bits")
    
    # Test all configs
    all_configs = get_axil4_field_configs(addr_width=32, data_width=32)
    print(f"\nAll AXIL4 Configs: {list(all_configs.keys())}")
    
    # Show total field count
    total_fields = sum(len(config.field_definitions) for config in all_configs.values())
    print(f"Total fields across all channels: {total_fields}")
    
    print("\n✅ AXIL4 field configurations - SPECIFICATION COMPLIANT!")
    print("IMPROVEMENTS:")
    print("  ❌ Removed: All USER signals (not in AXIL4 spec)")
    print("  ✅ Kept: Only essential AXIL4 signals")
    print("  ✅ Simplified: Minimal field configurations")
    print("  ✅ Optimized: Perfect for register access")
