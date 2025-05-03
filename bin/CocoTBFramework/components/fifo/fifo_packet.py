"""FIFO Packet class with value masking implementation and mask caching optimization"""
from typing import Dict, Optional, Any, Set

from ..packet import Packet
from ..field_config import FieldConfig
from ..flex_randomizer import FlexRandomizer


class FIFOPacket(Packet):
    """
    Packet class for FIFO protocol with value masking to ensure values stay within field boundaries
    and mask caching for improved performance
    """

    def __init__(self, field_config: Optional[FieldConfig] = None, fields: Optional[Dict[str, int]] = None,
                    master_randomizer: Optional[FlexRandomizer] = None,
                    slave_randomizer: Optional[FlexRandomizer] = None):
        """
        Initialize a FIFO packet with field masking.

        Args:
            field_config: Field configuration
            fields: Optional initial field values
            master_randomizer: Optional randomizer for master interface
            slave_randomizer: Optional randomizer for slave interface
        """
        # Call parent constructor
        super().__init__(field_config, fields)

        # Initialize FIFO-specific properties
        self.master_randomizer = master_randomizer
        self.slave_randomizer = slave_randomizer
        self.master_delay = None
        self.slave_delay = None
        
        # Add mask cache to improve performance
        self._field_masks = {}
        
        # Transaction dependency tracking
        self.depends_on_index = None
        self.dependency_type = None
        self.is_completed = False
        
        # Additional metadata
        self.fifo_metadata = {}
        self.transaction_id = None

    def _mask_field_value(self, field, value):
        """
        Mask a field value according to its maximum allowed value.
        Uses caching for improved performance.

        Args:
            field: Field name
            value: Original value

        Returns:
            Masked value
        """
        # Check cache first
        if field in self._field_masks:
            mask = self._field_masks[field]
            masked_value = value & mask
            if masked_value != value:
                self.log.warning(f"{field} value 0x{value:x} exceeds field width, masked to 0x{masked_value:x}")
            return masked_value
        
        # Calculate mask if not cached
        if self.field_config and field in self.field_config.field_names():
            field_def = self.field_config.get_field(field)
            field_width = field_def.bits
            mask = (1 << field_width) - 1
            
            # Cache the mask for future use
            self._field_masks[field] = mask
            
            # Apply mask
            masked_value = value & mask
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
        
    def __getitem__(self, field):
        """Get a field value with lazy loading from memory model if needed"""
        if field in self._fields:
            return self._fields[field]
        # Allow default field access to fall through to parent
        return super().__getitem__(field)

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
            self.master_delay = self.master_randomizer.choose_write_delay()
        return self.master_delay or 0

    def get_slave_delay(self):
        """
        Get the delay for the slave interface.

        Returns:
            Delay in cycles (0 if no randomizer)
        """
        # Calculate and cache the delay if not already done
        if self.slave_delay is None and self.slave_randomizer:
            self.slave_delay = self.master_randomizer.choose_read_delay()
        return self.slave_delay or 0

    def clear_cache(self):
        """
        Clear the mask cache.
        Useful when field configurations change.
        """
        self._field_masks.clear()
        
    def get_cache_stats(self):
        """
        Get cache statistics.
        
        Returns:
            Dictionary with cache information
        """
        return {
            "cache_size": len(self._field_masks),
            "cached_fields": list(self._field_masks.keys())
        }
        
    def set_fifo_metadata(self, depth, capacity):
        """
        Set FIFO-specific metadata for transaction tracking.
        
        Args:
            depth: Current FIFO depth when transaction was created
            capacity: FIFO capacity
        """
        self.fifo_metadata = {
            'depth': depth,
            'capacity': capacity,
            'fullness_percentage': (depth / capacity * 100) if capacity > 0 else 0
        }
        
    def set_dependency(self, depends_on_index, dependency_type="after"):
        """
        Set dependency information for the packet.
        
        Args:
            depends_on_index: Index of transaction this depends on
            dependency_type: Type of dependency ("after", "immediate", "conditional")
        """
        self.depends_on_index = depends_on_index
        self.dependency_type = dependency_type
        
    def mark_completed(self):
        """Mark the transaction as completed."""
        self.is_completed = True
        
    def pack_for_fifo(self) -> Dict[str, Any]:
        """
        Pack fields for FIFO transmission with automatic masking.
        
        This method prepares the packet's fields for transmission through
        the FIFO interface, applying appropriate field masking to ensure values
        fit within their specified bit widths.
        
        Returns:
            Dictionary mapping field names to masked field values
        """
        result = {}
        
        # Process all fields in the order specified by field_config if available
        if self.field_config:
            for field_name in self.field_config.field_names():
                if hasattr(self, field_name) and getattr(self, field_name) is not None:
                    value = getattr(self, field_name)
                    # Ensure value is properly masked
                    masked_value = self._mask_field_value(field_name, value)
                    result[field_name] = masked_value
        else:
            # Handle cases where field_config is not available
            # Just include all fields in the packet
            for field_name, value in self._fields.items():
                if value is not None:
                    result[field_name] = value
                    
        return result
        
    def unpack_from_fifo(self, data_dict: Dict[str, Any]):
        """
        Unpack values from FIFO into packet fields with masking.
        
        Args:
            data_dict: Dictionary of field values from FIFO
        """
        for field_name, value in data_dict.items():
            if value is not None:
                # Apply masking as needed
                masked_value = self._mask_field_value(field_name, value)
                setattr(self, field_name, masked_value)
    
    def get_all_field_names(self) -> Set[str]:
        """
        Get all field names from both the field_config and the packet's fields.
        
        Returns:
            Set of all field names
        """
        field_names = set(self._fields.keys())
        
        # Add fields from field_config if available
        if self.field_config and hasattr(self.field_config, 'field_names'):
            field_names.update(self.field_config.field_names())
            
        return field_names
