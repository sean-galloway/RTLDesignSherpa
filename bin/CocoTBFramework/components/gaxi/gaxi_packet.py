"""GAXI Packet class with value masking implementation"""
from typing import Dict, Any, Optional

from CocoTBFramework.components.packet import Packet
from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.flex_randomizer import FlexRandomizer


class GAXIPacket(Packet):
    """
    Packet class for GAXI protocol with value masking to ensure values stay within field boundaries
    """

    def __init__(self, field_config: Optional[FieldConfig] = None, fields: Optional[Dict[str, int]] = None,
                 master_randomizer: Optional[FlexRandomizer] = None,
                 slave_randomizer: Optional[FlexRandomizer] = None):
        """
        Initialize a GAXI packet with field masking.

        Args:
            field_config: Field configuration
            fields: Optional initial field values
            master_randomizer: Optional randomizer for master interface
            slave_randomizer: Optional randomizer for slave interface
        """
        # Call parent constructor
        super().__init__(field_config, fields)
        
        # Initialize GAXI-specific properties
        self.master_randomizer = master_randomizer
        self.slave_randomizer = slave_randomizer
        self.master_delay = None
        self.slave_delay = None

    def _mask_field_value(self, field, value):
        """
        Mask a field value according to its maximum allowed value.
        
        Args:
            field: Field name
            value: Original value
            
        Returns:
            Masked value
        """
        # Get field width from field_config
        if self.field_config and field in self.field_config.field_names():
            field_def = self.field_config.get_field(field)
            field_width = field_def.bits
            max_value = (1 << field_width) - 1
            
            # Apply mask
            masked_value = value & max_value
            if masked_value != value:
                self.log.warning(f"{field} value 0x{value:x} exceeds field width ({field_width} bits), masked to 0x{masked_value:x}")
            return masked_value
            
        # If no field config or field not defined, return original value
        return value

    def __setitem__(self, field, value):
        """Set a field value with masking"""
        # Apply masking to the value
        masked_value = self._mask_field_value(field, value)
        # Use parent class's field storage
        super().__setitem__(field, masked_value)

    def set_master_randomizer(self, randomizer):
        """Set the master randomizer"""
        self.master_randomizer = randomizer

    def set_slave_randomizer(self, randomizer):
        """Set the slave randomizer"""
        self.slave_randomizer = randomizer

    def get_master_delay(self):
        """
        Get the delay for the master interface.
        
        Returns:
            Delay in cycles (0 if no randomizer)
        """
        # Calculate and cache the delay if not already done
        if self.master_delay is None and self.master_randomizer:
            self.master_delay = self.master_randomizer.choose_valid_delay()
        return self.master_delay or 0

    def get_slave_delay(self):
        """
        Get the delay for the slave interface.
        
        Returns:
            Delay in cycles (0 if no randomizer)
        """
        # Calculate and cache the delay if not already done
        if self.slave_delay is None and self.slave_randomizer:
            self.slave_delay = self.slave_randomizer.choose_ready_delay()
        return self.slave_delay or 0

