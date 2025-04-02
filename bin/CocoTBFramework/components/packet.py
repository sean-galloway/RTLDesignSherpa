"""
Generic Packet Class for Protocol Testing

This module provides a base Packet class that can be used across different protocols
(GAXI, APB, etc.) to handle common packet operations like field management, formatting,
and comparisons.
"""
from typing import Dict, Any, List, Optional, Set, Union, Tuple
from .field_config import FieldConfig, FieldDefinition


class Packet:
    """
    Generic packet class for handling protocol transactions.
    
    This class provides a flexible way to define packets with custom fields without
    requiring subclassing for each protocol. Fields are defined through a FieldConfig
    object, and the class handles bit field transformations automatically during 
    packing/unpacking.
    
    Features:
    - Support for complex field configurations with active bit ranges
    - Customizable field value formatting
    - Automatic bit shifting for field packing/unpacking
    - Support for comparing packets with customizable field skipping
    """
    
    def __init__(self, field_config: Union[FieldConfig, Dict[str, Dict[str, Any]]], 
                 skip_compare_fields: Optional[List[str]] = None, **kwargs):
        """
        Initialize a packet with the given field configuration.
        
        Args:
            field_config: Either a FieldConfig object or a dictionary of field definitions
            skip_compare_fields: List of field names to skip during comparison operations
            **kwargs: Initial values for fields (e.g., addr=0x123, data=0xABC)
        """
        # Initialize core attributes using object.__setattr__ to avoid recursion
        object.__setattr__(self, 'start_time', 0)
        object.__setattr__(self, 'end_time', 0)
        object.__setattr__(self, 'fields', {})
        
        # Convert dictionary field_config to FieldConfig object if needed
        if isinstance(field_config, dict):
            object.__setattr__(self, 'field_config', FieldConfig.validate_and_create(field_config))
        else:
            object.__setattr__(self, 'field_config', field_config)
            
        # Set fields to skip during comparison
        object.__setattr__(self, 'skip_compare_fields', skip_compare_fields or ['start_time', 'end_time'])
        
        # Initialize all fields with their default values
        for name, field_def in self.field_config.items():
            self.fields[name] = field_def.default
            
        # Set any provided initial values
        for field_name, value in kwargs.items():
            if field_name in self.fields:
                self.fields[field_name] = value

    def __getattr__(self, name):
        """
        Support direct attribute access for fields.
        
        Args:
            name: Field name to access
            
        Returns:
            Field value if it exists
            
        Raises:
            AttributeError: If the field doesn't exist
        """
        # This method is only called for attributes that don't exist in the instance's __dict__
        if 'fields' in self.__dict__ and name in self.__dict__['fields']:
            return self.__dict__['fields'][name]
        raise AttributeError(f"'{self.__class__.__name__}' object has no attribute '{name}'")
    
    def __setattr__(self, name, value):
        """
        Support direct attribute assignment for fields.
        
        Args:
            name: Field name to set
            value: Value to assign
        """
        # Check if we have fields initialized and if name is a field
        if 'fields' in self.__dict__ and name in self.__dict__['fields']:
            # Set field value in the fields dictionary
            self.__dict__['fields'][name] = value
        else:
            # Set as regular attribute
            object.__setattr__(self, name, value)
    
    def shift_for_fifo(self, value, field_name):
        """
        Convert a full field value to its FIFO representation by right-shifting.
        For example, if addr[31:5] is 0x12345678, this returns 0x91A2B3 (shifted right by 5).
        
        Args:
            value: The full field value
            field_name: Name of the field
            
        Returns:
            Value adjusted according to active_bits configuration for FIFO
        """
        if not self.field_config.has_field(field_name):
            return value
            
        field_def = self.field_config[field_name]
        active_bits = field_def.active_bits
        
        if active_bits[1] == 0:
            return value
            
        # Extract only the active bits by right-shifting
        msb, lsb = active_bits
        shifted_value = value >> lsb
        
        # Create a mask for the active bits
        active_width = msb - lsb + 1
        mask = (1 << active_width) - 1
        
        # Apply the mask to ensure we only keep the active bits
        return shifted_value & mask
    
    def expand_from_fifo(self, value, field_name):
        """
        Expand a FIFO value to its full field representation by left-shifting.
        For example, if addr[31:5] in FIFO is 0x91A2B3, this returns 0x12345660 (shifted left by 5).
        Note that the lowest 5 bits will be zeros due to the shifting process.
        
        Args:
            value: The FIFO field value
            field_name: Name of the field
            
        Returns:
            Value expanded according to active_bits configuration
        """
        if not self.field_config.has_field(field_name):
            return value

        field_def = self.field_config[field_name]
        active_bits = field_def.active_bits

        return value if active_bits[1] == 0 else value << active_bits[1]
    
    def pack_for_fifo(self):
        """
        Pack the packet into a dictionary suitable for FIFO transmission,
        applying appropriate bit field adjustments.
        
        Returns:
            Dictionary with field name and FIFO-adjusted values
        """
        fifo_data = {}
        for field_name, value in self.fields.items():
            # Apply bit shifting for FIFO
            fifo_value = self.shift_for_fifo(value, field_name)
            fifo_data[field_name] = fifo_value
        return fifo_data
    
    def unpack_from_fifo(self, fifo_data):
        """
        Unpack FIFO data into full field values, applying appropriate bit field expansions.
        
        Args:
            fifo_data: Dictionary with field values from FIFO, or a single integer value
                (which will be assigned to 'data' field if present)
                
        Returns:
            Self for chaining
        """
        # Handle both dictionary input and single value input
        if isinstance(fifo_data, dict):
            # Process dictionary of field values
            for field_name, fifo_value in fifo_data.items():
                if field_name in self.fields:
                    # Expand from FIFO value to full field value
                    full_value = self.expand_from_fifo(fifo_value, field_name)
                    self.fields[field_name] = full_value
        elif isinstance(fifo_data, int) and 'data' in self.fields:
            # Handle case when a single integer value is provided
            self.fields['data'] = self.expand_from_fifo(fifo_data, 'data')
            
        return self
    
    def get_total_bits(self):
        """
        Calculate the total number of bits in the packet.
        
        Returns:
            Total number of bits across all fields
        """
        return self.field_config.get_total_bits()
    
    def _format_field(self, field_name, value):
        """
        Format a field value according to its configuration.
        
        Args:
            field_name: Name of the field to format
            value: Value to format
            
        Returns:
            Formatted string representation of the value
        """
        if not self.field_config.has_field(field_name):
            return str(value)
            
        field_def = self.field_config[field_name]
        fmt = field_def.format
        bits = field_def.bits
        display_width = field_def.display_width
        active_bits = field_def.active_bits
        
        # Check for undefined values
        if value == -1:
            return "X/Z"  # Indicate undefined value
            
        # Calculate appropriate width based on bits or display_width
        width = display_width
            
        # Format based on specified format
        if fmt == 'bin':
            formatted = f"0b{value:0{width}b}"
        elif fmt == 'dec':
            formatted = f"{value:{width}d}"
        else:
            # Default to hex if unknown format
            formatted = f"0x{value:0{width}X}"
            
        # Include active bit range in display if specified
        if active_bits is not None:
            msb, lsb = active_bits
            if msb != bits - 1 or lsb != 0:
                # Only show bit range if it's not the full field
                if msb == lsb:
                    formatted = f"{formatted}[{msb}]"
                else:
                    formatted = f"{formatted}[{msb}:{lsb}]"
                    
        return formatted
    
    def __str__(self):
        """
        Provide a detailed string representation of the packet.
        Fields are displayed in the order they were defined in the field_config.
        
        Returns:
            Formatted string with all fields
        """
        result = [f"{self.__class__.__name__}:"]
        
        # Find the longest field description for alignment
        max_desc_len = max(
            len(field_def.description)
            for field_def in self.field_config.fields()
        )
        
        # Add all fields with their formatted values
        for field_name, field_def in self.field_config.items():
            value = self.fields[field_name]
            description = field_def.description
            formatted_value = self._format_field(field_name, value)
            
            # Pad the description to align values
            padded_desc = description.ljust(max_desc_len)
            result.append(f"  {padded_desc}: {formatted_value}")
            
            # If this is a partial field, also show the FIFO value
            active_bits = field_def.active_bits
            if active_bits[1] > 0 and value != -1:  # Skip FIFO display for X/Z values
                fifo_value = self.shift_for_fifo(value, field_name)
                fifo_formatted = self._format_field(field_name, fifo_value)
                result.append(f"  {' ' * max_desc_len}  FIFO: {fifo_formatted}")
                
        # Add timing information if available
        if self.start_time > 0:
            result.append(f"  Start Time: {self.start_time} ns")
        if self.end_time > 0:
            result.extend(
                (
                    f"  End Time: {self.end_time} ns",
                    f"  Duration: {self.end_time - self.start_time} ns",
                )
            )
        return "\n".join(result)
    
    def formatted(self, compact=False, show_fifo=False):
        """
        Return a formatted string representation.
        
        Args:
            compact: If True, return a more compact representation
            show_fifo: If True, show FIFO values instead of full field values
            
        Returns:
            Formatted string representation
        """
        if not compact:
            # Use the full string representation
            return self.__str__()
            
        # Compact representation with just field values
        fields = []
        for field_name, field_def in self.field_config.items():
            value = self.fields[field_name]
            if show_fifo and value != -1:  # Skip FIFO calculation for X/Z values
                value = self.shift_for_fifo(value, field_name)
            formatted_value = self._format_field(field_name, value)
            fields.append(f"{field_name}={formatted_value}")
        return f"{self.__class__.__name__}({', '.join(fields)})"
    
    def __eq__(self, other):
        """
        Compare packets for equality, skipping fields in skip_compare_fields.
        Also checks for undefined values (X/Z), which are typically represented as -1.
        
        Args:
            other: Another packet to compare with
            
        Returns:
            True if all non-skipped fields match and have defined values, False otherwise
        """
        if not isinstance(other, Packet):
            return NotImplemented
            
        # Compare all non-skipped fields
        for field_name in self.field_config.field_names():
            # Skip fields that are configured to be skipped during comparison
            if field_name in self.skip_compare_fields:
                continue
                
            # Check if field exists in both packets
            if field_name not in self.fields or field_name not in other.fields:
                return False
                
            self_value = self.fields[field_name]
            other_value = other.fields[field_name]
            
            # Check for undefined values (X/Z represented as -1 in simulation)
            if self_value == -1 or other_value == -1:
                return False  # Undefined values should cause comparison to fail
                
            # Check if values match
            if self_value != other_value:
                return False
                
        return True
    
    def copy(self):
        """
        Create a copy of this packet.
        
        Returns:
            New packet with the same field values
        """
        # Create new packet with same field config
        new_packet = self.__class__(self.field_config, self.skip_compare_fields)
        
        # Copy field values
        for field_name, value in self.fields.items():
            new_packet.fields[field_name] = value
            
        # Copy timing information
        new_packet.start_time = self.start_time
        new_packet.end_time = self.end_time
        
        return new_packet