class GAXIPacket:
    """
    Highly configurable packet class for AXI protocol transactions.
    
    This class provides a flexible way to define packets with custom fields without
    requiring subclassing. Fields are defined through a configuration dictionary,
    and the ordering of fields in this dictionary determines their display order.
    
    The class handles bit field transformations automatically during packing/unpacking:
    - When packing: Full field values are adjusted according to active_bits for FIFO loading
    - When unpacking: FIFO values are expanded back to full field values
    
    Basic usage:
        # 1. Define field configuration once
        field_config = {
            'addr': {
                'bits': 32,
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (31, 5),  # Only bits 31:5 are active in FIFO
                'description': 'Address'
            },
            'data': {
                'bits': 32,
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (31, 0),  # All bits are active
                'description': 'Data'
            }
        }
        
        # 2. In master: Create packet with full values and pack for FIFO
        master_packet = AXIPacket(field_config, addr=0x12345678, data=0xABCD1234)
        fifo_data = master_packet.pack_for_fifo()  # addr becomes right-shifted to fit active_bits
        
        # 3. In slave: Unpack from FIFO data to get full field values
        slave_packet = AXIPacket(field_config)
        slave_packet.unpack_from_fifo(fifo_data)  # addr is automatically left-shifted back
        
        # 4. Compare packets (skipping specified fields)
        are_equal = master_packet == slave_packet  # Will skip comparing fields in skip_compare_fields
    """
    def __init__(self, field_config=None, skip_compare_fields=None, **kwargs):
        """
        Initialize a configurable AXI packet.
        
        Args:
            field_config: Dictionary of field definitions with configuration for each field.
                Note: The order of fields in this dictionary determines their display order.
                
                Each field should have: 
                - 'bits': number of bits in the hardware field
                - 'default': default value
                - 'format': format string (e.g., 'hex', 'bin', 'dec')
                - 'display_width': fixed width for display (e.g., 8 for 8 hex chars)
                - 'active_bits': tuple of (msb, lsb) for partial fields
                - 'description': field description for display purposes
            
            skip_compare_fields: List of field names to skip during comparison operations.
                Defaults to ['start_time', 'end_time'] if None.
                
            **kwargs: Initial values for fields (e.g., addr=0x123, data=0xABC)
        """
        self.start_time = 0
        self.end_time = 0
        
        # Default to a simple data field if no config provided
        self.field_config = field_config or {
            'data': {
                'bits': 32, 
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (31, 0),
                'description': 'Data value'
            }
        }
        
        # Set fields to skip during comparison
        self.skip_compare_fields = skip_compare_fields or ['start_time', 'end_time']
        
        # Initialize all fields with their default values
        self.fields = {}
        for field_name, config in self.field_config.items():
            # Get default from config or use 0
            default_value = config.get('default', 0)
            self.fields[field_name] = default_value
        
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
        if name in self.fields:
            return self.fields[name]
        raise AttributeError(f"'{self.__class__.__name__}' object has no attribute '{name}'")
    
    def __setattr__(self, name, value):
        """
        Support direct attribute assignment for fields.
        
        Args:
            name: Field name to set
            value: Value to assign
        """
        if name in ['start_time', 'end_time', 'field_config', 'fields', 'skip_compare_fields']:
            # These are class attributes, not packet fields
            super().__setattr__(name, value)
        elif hasattr(self, 'fields') and name in self.fields:
            # Set field value in the fields dictionary
            self.fields[name] = value
        else:
            # Set as regular attribute
            super().__setattr__(name, value)
    
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
        if field_name not in self.field_config:
            return value
            
        config = self.field_config[field_name]
        active_bits = config.get('active_bits', None)
        
        if active_bits is None or active_bits[1] == 0:
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
        For example, if addr[31:5] in FIFO is 0x91A2B3, this returns 0x12345678 (shifted left by 5).
        
        Args:
            value: The FIFO field value
            field_name: Name of the field
            
        Returns:
            Value expanded according to active_bits configuration
        """
        if field_name not in self.field_config:
            return value

        config = self.field_config[field_name]
        active_bits = config.get('active_bits', None)

        if active_bits is None or active_bits[1] == 0:
            return value

        # Left-shift to get the full field value
        lsb = active_bits[1]
        return value << lsb
    
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
            fifo_data: Dictionary with field values from FIFO
            
        Returns:
            Self for chaining
        """
        for field_name, fifo_value in fifo_data.items():
            if field_name in self.fields:
                # Expand from FIFO value to full field value
                full_value = self.expand_from_fifo(fifo_value, field_name)
                self.fields[field_name] = full_value
        return self
    
    def get_total_bits(self):
        """
        Calculate the total number of bits in the packet.
        
        Returns:
            Total number of bits across all fields
        """
        return sum(
            config.get('bits', 0)
            for _, config in self.field_config.items()
        )
    
    def _format_field(self, field_name, value):
        """
        Format a field value according to its configuration.
        
        Args:
            field_name: Name of the field to format
            value: Value to format
            
        Returns:
            Formatted string representation of the value
        """
        if field_name not in self.field_config:
            return str(value)

        config = self.field_config[field_name]
        fmt = config.get('format', 'hex')
        bits = config.get('bits', 32)
        display_width = config.get('display_width', 0)
        active_bits = config.get('active_bits', None)

        # Calculate appropriate width based on bits or display_width
        if display_width > 0:
            # Use explicit display width if provided
            width = display_width
        elif fmt == 'bin':
            width = bits
        elif fmt == 'hex':
            width = (bits + 3) // 4  # Round up to nearest 4 bits
        else:
            width = 1  # Default for decimal is no padding

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
            len(config.get('description', field_name))
            for field_name, config in self.field_config.items()
        )

        # Add all fields with their formatted values
        # Note: We iterate through field_config to preserve field order
        for field_name, config in self.field_config.items():
            value = self.fields[field_name]
            description = config.get('description', field_name)
            formatted_value = self._format_field(field_name, value)

            # Pad the description to align values
            padded_desc = description.ljust(max_desc_len)
            result.append(f"  {padded_desc}: {formatted_value}")

            # If this is a partial field, also show the FIFO value
            active_bits = config.get('active_bits', None)
            if active_bits and active_bits[1] > 0:
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
        for field_name, config in self.field_config.items():
            value = self.fields[field_name]
            if show_fifo:
                value = self.shift_for_fifo(value, field_name)
            formatted_value = self._format_field(field_name, value)
            fields.append(f"{field_name}={formatted_value}")
        return f"{self.__class__.__name__}({', '.join(fields)})"
    
    def __eq__(self, other):
        """
        Compare packets for equality, skipping fields in skip_compare_fields.
        
        Args:
            other: Another packet to compare with
            
        Returns:
            True if all non-skipped fields match, False otherwise
        """
        if not isinstance(other, GAXIPacket):
            return NotImplemented
        
        # Compare all fields except those in skip_compare_fields
        for field_name, value in self.fields.items():
            if field_name in self.skip_compare_fields:
                continue  # Skip comparing this field
                
            if field_name not in other.fields or other.fields[field_name] != value:
                return False
        
        return True


# Example usage demonstrating master and slave workflow with comparison
if __name__ == "__main__":
    # 1. Define field configuration once
    field_config = {
        'addr': {
            'bits': 32,              # Total bits in the field
            'default': 0,            # Default value when not specified
            'format': 'hex',         # Display format (hex, bin, dec)
            'display_width': 8,      # Always display as 8 hex chars
            'active_bits': (31, 5),  # Only bits 31:5 are used in FIFO (msb, lsb)
            'description': 'Address' # Description for display
        },
        'data': {
            'bits': 32,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (31, 0),  # All bits are used
            'description': 'Data'
        },
        'metadata': {
            'bits': 8,
            'default': 0,
            'format': 'hex',
            'display_width': 2,
            'active_bits': (7, 0),
            'description': 'Metadata'
        }
    }
    
    print("MASTER SIDE:")
    # 2. In master: Create packet with full values, specifying fields to skip during comparison
    master_packet = GAXIPacket(
        field_config, 
        skip_compare_fields=['metadata', 'start_time', 'end_time'],
        addr=0x12345678, 
        data=0xABCD1234,
        metadata=0xAA
    )
    print(master_packet)
    
    # Set timing info
    master_packet.start_time = 100
    master_packet.end_time = 150
    
    # Pack for FIFO transmission
    fifo_data = master_packet.pack_for_fifo()
    print(f"\nPacked for FIFO transmission: {fifo_data}")
    print(f"  addr: 0x{fifo_data['addr']:X} (shifted right by 5 bits)")
    print(f"  data: 0x{fifo_data['data']:X}")
    print(f"  metadata: 0x{fifo_data['metadata']:X}")
    
    print("\nSLAVE SIDE:")
    # 3. In slave: Unpack from FIFO to get full field values
    # Note: Using the same skip_compare_fields configuration
    slave_packet = GAXIPacket(
        field_config,
        skip_compare_fields=['metadata', 'start_time', 'end_time']
    )
    slave_packet.unpack_from_fifo(fifo_data)
    
    # Set different timing info and metadata
    slave_packet.start_time = 200
    slave_packet.end_time = 250
    slave_packet.metadata = 0xBB  # Different from master
    
    print(slave_packet)
    
    # Verify that the non-skipped field values match between master and slave
    print("\nVERIFICATION:")
    print(f"Master addr: 0x{master_packet.addr:X}")
    print(f"Slave addr:  0x{slave_packet.addr:X}")
    
    print(f"Master data: 0x{master_packet.data:X}")
    print(f"Slave data:  0x{slave_packet.data:X}")
    
    print(f"Master metadata: 0x{master_packet.metadata:X}")
    print(f"Slave metadata:  0x{slave_packet.metadata:X}")
    
    print(f"Master start_time: {master_packet.start_time}")
    print(f"Slave start_time:  {slave_packet.start_time}")
    
    # Compare packets (should be equal because we're skipping metadata and timing)
    print(f"\nPackets equal despite different metadata and timing: {master_packet == slave_packet}")
    
    # Change a non-skipped field
    slave_packet.data = 0x99887766
    print(f"Packets equal after changing data: {master_packet == slave_packet}")
