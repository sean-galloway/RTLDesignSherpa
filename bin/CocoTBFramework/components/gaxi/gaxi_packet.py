"""GAXI Packet Implementation"""
from typing import Dict, Any, List, Optional, Union
from CocoTBFramework.components.packet import Packet
from CocoTBFramework.components.field_config import FieldConfig


class GAXIPacket(Packet):
    """
    GAXI-specific packet class for handling GAXI transactions.
    
    This class extends the base Packet class with GAXI-specific functionality.
    It provides backward compatibility with the original GAXIPacket implementation.
    """
    
    def __init__(self, field_config: Union[FieldConfig, Dict[str, Dict[str, Any]]] = None, 
                 skip_compare_fields: Optional[List[str]] = None, **kwargs):
        """
        Initialize a GAXI packet with the given field configuration.
        
        Args:
            field_config: Either a FieldConfig object or a dictionary of field definitions
            skip_compare_fields: List of field names to skip during comparison operations
            **kwargs: Initial values for fields (e.g., addr=0x123, data=0xABC)
        """
        # Use default GAXI field config if none provided
        if field_config is None:
            field_config = self._get_default_field_config()
            
        # Initialize base class
        super().__init__(field_config, skip_compare_fields, **kwargs)
    
    @staticmethod
    def _get_default_field_config():
        """
        Get default field configuration for GAXI packets.
        
        Returns:
            Default GAXI field configuration
        """
        config = FieldConfig()
        config.add_field_dict("data", {
            'bits': 32,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (31, 0),
            'description': 'Data value'
        })
        return config
    
    @classmethod
    def create_with_cmd_addr_data(cls, cmd_width=1, addr_width=32, data_width=32):
        """
        Create a GAXI packet with command, address, and data fields.
        
        Args:
            cmd_width: Width of the command field in bits
            addr_width: Width of the address field in bits
            data_width: Width of the data field in bits
            
        Returns:
            New GAXIPacket with cmd/addr/data field configuration
        """
        # Create field configuration
        config = FieldConfig()
        
        # Add command field (0=read, 1=write)
        config.add_field_dict("cmd", {
            'bits': cmd_width,
            'default': 0,
            'format': 'bin',
            'display_width': cmd_width,
            'active_bits': (cmd_width-1, 0),
            'description': 'Command (0=Read, 1=Write)'
        })
        
        # Add address field
        config.add_field_dict("addr", {
            'bits': addr_width,
            'default': 0,
            'format': 'hex',
            'display_width': addr_width // 4,
            'active_bits': (addr_width-1, 0),
            'description': 'Address'
        })
        
        # Add data field
        config.add_field_dict("data", {
            'bits': data_width,
            'default': 0,
            'format': 'hex',
            'display_width': data_width // 4,
            'active_bits': (data_width-1, 0),
            'description': 'Data'
        })
        
        return cls(config)
    
    @classmethod
    def create_with_addr_ctrl_data(cls, addr_width=4, ctrl_width=4, data_width=8, num_data=2):
        """
        Create a GAXI packet with address, control, and multiple data fields.
        
        Args:
            addr_width: Width of the address field in bits
            ctrl_width: Width of the control field in bits
            data_width: Width of each data field in bits
            num_data: Number of data fields
            
        Returns:
            New GAXIPacket with multi-data field configuration
        """
        # Create field configuration
        config = FieldConfig()
        
        # Add address field
        config.add_field_dict("addr", {
            'bits': addr_width,
            'default': 0,
            'format': 'hex',
            'display_width': (addr_width + 3) // 4,
            'active_bits': (addr_width-1, 0),
            'description': 'Address'
        })
        
        # Add control field
        config.add_field_dict("ctrl", {
            'bits': ctrl_width,
            'default': 0,
            'format': 'hex',
            'display_width': (ctrl_width + 3) // 4,
            'active_bits': (ctrl_width-1, 0),
            'description': 'Control'
        })
        
        # Add data fields
        for i in range(num_data):
            config.add_field_dict(f"data{i}", {
                'bits': data_width,
                'default': 0,
                'format': 'hex',
                'display_width': (data_width + 3) // 4,
                'active_bits': (data_width-1, 0),
                'description': f'Data {i}'
            })
            
        return cls(config)