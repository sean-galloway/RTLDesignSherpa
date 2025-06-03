"""
APB-GAXI Configuration Module

This module provides configurable APB-GAXI interface configurations using the FieldConfig
framework. It supports parameterized field configurations and signal mappings.
"""

from typing import Dict, Any, Optional
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition


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
            FieldConfig with cmd, addr, data, and strb fields
        """
        config = FieldConfig()

        # Command field (read/write)
        config.add_field(FieldDefinition(
            name="cmd",
            bits=1,
            default=0,
            format="bin",
            display_width=1,
            active_bits=(0, 0),
            description="Command (0=Read, 1=Write)",
            encoding={0: "READ", 1: "WRITE"}
        ))

        # Address field
        config.add_field(FieldDefinition(
            name="addr",
            bits=self.addr_width,
            default=0,
            format="hex",
            display_width=(self.addr_width + 3) // 4,  # Hex digits needed
            active_bits=(self.addr_width - 1, 0),
            description="Address"
        ))

        # Data field
        config.add_field(FieldDefinition(
            name="data",
            bits=self.data_width,
            default=0,
            format="hex",
            display_width=(self.data_width + 3) // 4,  # Hex digits needed
            active_bits=(self.data_width - 1, 0),
            description="Data"
        ))

        # Strobe field
        config.add_field(FieldDefinition(
            name="strb",
            bits=self.strb_width,
            default=(1 << self.strb_width) - 1,  # All bits set by default
            format="bin",
            display_width=self.strb_width,
            active_bits=(self.strb_width - 1, 0),
            description="Byte strobe"
        ))

        return config

    def create_rsp_field_config(self) -> FieldConfig:
        """
        Create response interface field configuration.

        Returns:
            FieldConfig with data and err fields
        """
        config = FieldConfig()

        # Data field
        config.add_field(FieldDefinition(
            name="data",
            bits=self.data_width,
            default=0,
            format="hex",
            display_width=(self.data_width + 3) // 4,  # Hex digits needed
            active_bits=(self.data_width - 1, 0),
            description="Response data"
        ))

        # Error field
        config.add_field(FieldDefinition(
            name="err",
            bits=1,
            default=0,
            format="bin",
            display_width=1,
            active_bits=(0, 0),
            description="Error flag",
            encoding={0: "OK", 1: "ERROR"}
        ))

        return config

    def get_master_cmd_signal_maps(self) -> Dict[str, str]:
        """Get master command interface signal mapping."""
        return {
            'ctl': {
                'm2s_valid': 'o_cmd_valid',
                's2m_ready': 'i_cmd_ready'
            },
            'opt': {
                'm2s_pkt_cmd': 'o_cmd_pwrite',
                'm2s_pkt_addr': 'o_cmd_paddr',
                'm2s_pkt_data': 'o_cmd_pwdata',
                'm2s_pkt_strb': 'o_cmd_pstrb'
            }
        }

    def get_slave_cmd_signal_maps(self) -> Dict[str, str]:
        """Get slave command interface optional signal mapping."""
        return {
            'ctl':{
                'm2s_valid': 'i_cmd_valid',
                's2m_ready': 'o_cmd_ready'
            },
            'opt': {
                'm2s_pkt_cmd': 'i_cmd_pwrite',
                'm2s_pkt_addr': 'i_cmd_paddr',
                'm2s_pkt_data': 'i_cmd_pwdata',
                'm2s_pkt_strb': 'i_cmd_pstrb',
                'm2s_pkt_prot': 'i_cmd_pprot'
            }
        }

    def get_master_rsp_signal_maps(self) -> Dict[str, str]:
        """Get master response interface signal mapping."""
        return {
            'ctl': {
                'm2s_valid': 'o_rsp_valid',
                's2m_ready': 'i_rsp_ready'
            },
            'opt': {
                'm2s_pkt_data': 'o_rsp_prdata',
                'm2s_pkt_err': 'o_rsp_pslverr'
            }
        }

    def get_slave_rsp_signal_maps(self) -> Dict[str, str]:
        """Get slave response interface signal mapping."""
        return {
            'ctl': {
                'm2s_valid': 'i_rsp_valid',
                's2m_ready': 'o_rsp_ready'
            },
            'opt': {
                'm2s_pkt_data': 'i_rsp_prdata',
                'm2s_pkt_err': 'i_rsp_pslverr'
            }
        }
