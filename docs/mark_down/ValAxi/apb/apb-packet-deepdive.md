# APB Packet Deep Dive

This document provides a detailed analysis of the `APBPacket` and `APBTransaction` classes from `apb_packet.py`.

## Core Concepts

The APB packet implementation is built on two fundamental concepts:

1. **Field-oriented design**: Each packet field is defined with specific attributes (width, format, etc.)
2. **Protocol-aware representation**: The packet understands APB protocol details (read/write, strobes, etc.)

## APBPacket Class

### Class Structure

The `APBPacket` class extends the base `Packet` class and adds APB-specific functionality:

```python
class APBPacket(Packet):
    def __init__(self, field_config=None, skip_compare_fields=None,
                 data_width=32, addr_width=32, strb_width=4, **kwargs):
        # Initialize attributes
        object.__setattr__(self, 'data_width', data_width)
        object.__setattr__(self, 'addr_width', addr_width)
        object.__setattr__(self, 'strb_width', strb_width)
        object.__setattr__(self, 'count', kwargs.get('count', 0))

        # Use default APB field config if none provided
        if field_config is None:
            field_config = APBPacket._create_default_field_config(addr_width, data_width, strb_width)

        # Set default skip_compare_fields if none provided
        if skip_compare_fields is None:
            skip_compare_fields = ['start_time', 'end_time', 'count']

        # Initialize base class
        super().__init__(field_config, skip_compare_fields, **kwargs)

        # Derive APB-specific attributes after base initialization
        self.direction = PWRITE_MAP[self.fields.get('pwrite', 0)]

        # For backward compatibility
        self.cycle = self  # In case code expects to access a 'cycle' attribute
```

### Field Configuration

The packet uses a detailed field configuration that defines each APB field:

```python
@staticmethod
def _create_default_field_config(addr_width, data_width, strb_width):
    """Create default field configuration for APB packets."""
    config = FieldConfig()

    # Add fields
    config.add_field(FieldDefinition(
        name="pwrite",
        bits=1,
        default=0,
        format="dec",
        display_width=1,
        description="Write Enable (0=Read, 1=Write)"
    ))

    config.add_field(FieldDefinition(
        name="paddr",
        bits=addr_width,
        default=0,
        format="hex",
        display_width=addr_width // 4,
        description="Address"
    ))

    # Additional fields (pwdata, prdata, pstrb, pprot, pslverr)
    # ...

    return config
```

### Key Methods

1. **String Representation**: The `__str__` and `formatted` methods provide detailed or compact representations:

```python
def __str__(self):
    """Provide a detailed string representation of the APB packet."""
    result = [
        "APB Packet:",
        f"  Direction:  {self.direction}",
        f"  Address:    {self._format_field('paddr', self.fields['paddr'])}",
    ]
    
    # Data fields based on direction
    if self.direction == 'WRITE':
        result.append(f"  Write Data: {self._format_field('pwdata', self.fields['pwdata'])}")
        result.append(f"  Strobes:    {self._format_field('pstrb', self.fields['pstrb'])}")
    else:
        result.append(f"  Read Data:  {self._format_field('prdata', self.fields['prdata'])}")
    
    # Additional fields...
    
    return "\n".join(result)

def formatted(self, compact=False):
    """Return a formatted string representation."""
    if not compact:
        return self.__str__()
    
    # Compact representation
    fields = [
        f"time={self.start_time}",
        f"dir={self.direction}",
        f"addr={self._format_field('paddr', self.fields['paddr'])}",
    ]
    
    # Additional fields based on direction...
    
    return f"APBPacket({', '.join(fields)})"
```

2. **Equality Comparison**: The `__eq__` method compares packets while respecting the read/write direction:

```python
def __eq__(self, other):
    """Compare packets for equality, skipping fields in skip_compare_fields."""
    if not isinstance(other, APBPacket):
        return NotImplemented

    # Compare the relevant data field based on direction
    if self.direction == 'WRITE':
        data_self = self.fields.get('pwdata', 0)
        data_other = other.fields.get('pwdata', 0)
    else:
        data_self = self.fields.get('prdata', 0)
        data_other = other.fields.get('prdata', 0)

    # Basic checks for key fields
    if (self.direction != other.direction or
        self.fields.get('paddr', 0) != other.fields.get('paddr', 0) or
        data_self != data_other):
        return False
    
    # Additional field checks...
    
    return True
```

## APBTransaction Class

The `APBTransaction` class extends `Randomized` to provide randomized APB packet generation:

```python
class APBTransaction(Randomized):
    """APB Transaction class with improved randomization and configuration."""

    def __init__(self, data_width=32, addr_width=32, strb_width=4, constraints=None, **kwargs):
        # Initialize the Randomized base class
        super().__init__()

        # Add randomized variables
        self.pwrite = 0
        self.paddr = 0
        self.pstrb = 0 
        self.pprot = 0

        # Add these variables to be randomized
        self.add_rand("pwrite", [0, 1])
        self.add_rand("paddr", list(range(2**12)))
        self.add_rand("pstrb", list(range(2**strb_width)))
        self.add_rand("pprot", list(range(8)))

        # Store configuration
        self.data_width = data_width
        self.addr_width = addr_width
        self.strb_width = strb_width
        self.addr_mask = (strb_width - 1)

        # Setup randomizer
        if constraints is None:
            # Default constraints
            self.randomizer = FlexRandomizer({
                'pwrite': ([(0, 0), (1, 1)], [1, 1]),
                'paddr': ([(0, addr_min_hi), (addr_max_lo, addr_max_hi)], [4, 1]),
                'pstrb': ([(15, 15), (0, 14)], [4, 1]),
                'pprot': ([(0, 0), (1, 7)], [4, 1])
            })
        else:
            # Use provided constraints
            self.randomizer = FlexRandomizer(constraints)

        # Create initial packet
        self.packet = APBPacket(
            field_config=self.field_config,
            data_width=data_width,
            addr_width=addr_width,
            strb_width=strb_width,
            **kwargs
        )
```

### Randomization Methods

The `next` method generates a new randomized transaction:

```python
def next(self):
    """Generate next transaction using randomizer."""
    # Use Randomized's randomize method to set self.pwrite, self.paddr, etc.
    self.randomize()
    
    # Also get values from FlexRandomizer
    value_dict = self.randomizer.next()

    # Create a new packet
    packet = APBPacket(
        field_config=self.field_config,
        data_width=self.data_width,
        addr_width=self.addr_width,
        strb_width=self.strb_width
    )

    # Use FlexRandomizer for consistency with original implementation
    packet.fields['pwrite'] = value_dict['pwrite']
    packet.fields['paddr'] = value_dict['paddr'] & ~self.addr_mask
    packet.fields['pstrb'] = value_dict['pstrb']
    packet.fields['pprot'] = value_dict['pprot']
    packet.direction = PWRITE_MAP[packet.fields['pwrite']]

    # Generate random data for write
    if packet.direction == 'WRITE':
        packet.fields['pwdata'] = random.randint(0, (1 << self.data_width) - 1)

    # Update internal packet and return a copy
    self.packet = packet
    return packet.copy()
```

## Implementation Notes

### Direct Field Access vs. Properties

The implementation uses direct field access via a dictionary rather than properties:
- `self.fields['paddr']` instead of `self.paddr`
- This approach provides more flexibility for generic field handling

### Copy vs. Reference

The `copy` method is crucial for creating independent copies of packets:
```python
def copy(self):
    """Create a deep copy of the packet."""
    new_packet = APBPacket(
        field_config=self.field_config,
        skip_compare_fields=self.skip_compare_fields,
        data_width=self.data_width,
        addr_width=self.addr_width,
        strb_width=self.strb_width
    )
    
    # Copy all fields
    for field_name, field_value in self.fields.items():
        new_packet.fields[field_name] = field_value
    
    # Copy attributes
    new_packet.direction = self.direction
    new_packet.start_time = self.start_time
    new_packet.end_time = self.end_time
    
    return new_packet
```

### Direction Mapping

The code uses a simple array to map between numeric `pwrite` values and string directions:
```python
PWRITE_MAP = ['READ', 'WRITE']
```

This allows easy conversion: `direction = PWRITE_MAP[pwrite]`

## Key Insights

1. **Field-based structure**: The packet is built on a generic field structure, making it adaptable
2. **Protocol awareness**: Direction affects which fields are active (pwdata vs prdata)
3. **Dual randomization**: Uses both Randomized and FlexRandomizer for flexibility
4. **Comparison intelligence**: Compare only relevant fields based on direction
5. **Clean representation**: Detailed formatting with direction-aware output
