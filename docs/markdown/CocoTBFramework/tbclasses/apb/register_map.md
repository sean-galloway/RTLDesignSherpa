# Register Map Deep Dive

This document provides a detailed analysis of the `RegisterMap` class from `register_map.py`, which handles register information for APB verification.

## Core Concept

The `RegisterMap` class provides a bridge between the abstract register definitions from UVM (Universal Verification Methodology) files and the concrete APB transactions needed to access those registers. It handles:

1. Loading register definitions from UVM files
2. Tracking register state
3. Generating APB transactions for register access
4. Validating register read/write operations

## Class Architecture

The `RegisterMap` class is designed to parse and interact with UVM register definitions:

```python
class RegisterMap:
    """Grabs the register information from the uvm.py files"""
    def __init__(self, filename, apb_data_width, apb_addr_width, start_address, log):
        self.log = log
        self.filename = filename
        raw_dict = self._load_registers(filename)
        self.registers = self._process_registers(raw_dict)
        msg = f'Dumping {filename} registers:\n%s', pprint.pformat(self.registers)
        self.log.debug(msg)
        self.log.debug(pprint.pprint(self.registers))
        self.current_state = self._initialize_state()
        self.write_storage = {}
        self.apb_data_width = apb_data_width
        self.apb_addr_width = apb_addr_width
        self.start_address = start_address
        self.addr_mask = (1 << apb_addr_width) - 1
        self.data_mask = (1 << apb_data_width) - 1
        self.bytes_per_word = apb_data_width // 8
```

The initialization process:
1. Loads register definitions from the UVM file
2. Processes the raw dictionary into a structured format
3. Initializes the current register state
4. Sets up configuration values (address width, data width, etc.)

## Register Loading and Processing

The register map loads register definitions from a UVM Python file:

```python
def _load_registers(self, filename):
    spec = importlib.util.spec_from_file_location("register_dict", filename)
    register_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(register_module)

    # Assuming the dictionary in the file is named 'top_block'
    return register_module.top_block
```

Then processes the raw dictionary to extract register information:

```python
def _process_registers(self, raw_dict):
    def recursive_search(d):
        if isinstance(d, dict):
            if 'type' in d:
                yield d
            for v in d.values():
                yield from recursive_search(v)
        elif isinstance(d, list):
            for item in d:
                yield from recursive_search(item)

    processed_registers = {}
    for item in recursive_search(raw_dict):
        if item['type'] == 'reg':
            reg_name = item.get('name', '')
            msg = f'processing: {reg_name}'
            self.log.debug(msg)
            if reg_name:
                processed_registers[reg_name] = item

    return processed_registers
```

This method:
1. Recursively searches the dictionary for items with a 'type' field
2. Extracts items with type 'reg' (registers)
3. Organizes them by register name

## Register State Management

The `RegisterMap` initializes and tracks the current state of all registers:

```python
def _initialize_state(self):
    state = {}
    msg = f'Init: {self.filename}'
    self.log.debug(msg)
    for reg_name, reg_info in self.registers.items():
        msg = f'Loop: {reg_name}'
        self.log.debug(msg)
        if 'count' in reg_info:
            state[reg_name] = [int(reg_info['default'], 16)] * int(reg_info['count'])
        else:
            state[reg_name] = int(reg_info['default'], 16)
    return state
```

This method:
1. Creates a state dictionary to track register values
2. Handles both scalar registers and register arrays
3. Initializes each register to its default value

## Register Access Methods

### Field-Oriented Write Method

The `write` method provides field-oriented register access:

```python
def write(self, register, field, value):
    if register not in self.registers:
        raise ValueError(f"Register {register} not found")
    if field not in self.registers[register]:
        raise ValueError(f"Field {field} not found in register {register}")

    reg_info = self.registers[register]
    field_info = reg_info[field]

    mask = self._create_mask(field_info['offset'])
    field_width = self._get_field_width(field_info['offset'])
    num_words = (field_width + self.apb_data_width - 1) // self.apb_data_width

    if 'count' in reg_info:
        # Handle register arrays
        if register not in self.write_storage:
            self.write_storage[register] = [None] * int(reg_info['count'])
        for i in range(int(reg_info['count'])):
            if self.write_storage[register][i] is None:
                self.write_storage[register][i] = self.current_state[register][i]
            # Apply write to each register in the array
            # ...
    else:
        # Handle scalar registers
        if register not in self.write_storage:
            self.write_storage[register] = [self.current_state[register]] * num_words
        # Apply write to the register
        # ...
```

This method:
1. Validates the register and field names
2. Creates a bit mask for the field
3. Handles both scalar registers and register arrays
4. Applies the write to the appropriate storage

### Helper Methods for Field Access

The `RegisterMap` includes helper methods for field manipulation:

```python
def _create_mask(self, offset):
    """Create a bit mask for a field."""
    if ':' not in offset:
        return 1 << int(offset)
    high, low = map(int, offset.split(':'))
    return ((1 << (high - low + 1)) - 1) << low

def _get_field_width(self, offset):
    """Get the width of a field in bits."""
    if ':' not in offset:
        return 1
    high, low = map(int, offset.split(':'))
    return high - low + 1
```

These methods:
1. Parse field offset specifications (e.g., "31:0" for a 32-bit field)
2. Create appropriate bit masks for field access
3. Calculate field widths for multi-word fields

## APB Transaction Generation

The `generate_apb_cycles` method generates APB packets for pending register writes:

```python
def generate_apb_cycles(self) -> List[APBPacket]:
    apb_cycles = []
    for register, value in self.write_storage.items():
        reg_info = self.registers[register]
        base_address = (self.start_address + int(reg_info['address'], 16)) & self.addr_mask
        for i, v in enumerate(value):
            if (
                isinstance(value, list)
                and v is not None
                or not isinstance(value, list)
            ):
                address = (base_address + i * self.bytes_per_word) & self.addr_mask
                apb_cycles.append(APBPacket(
                    start_time=0,  # Set at transmission time
                    count=i,
                    direction='WRITE',
                    pwrite=1,
                    paddr=address,
                    pwdata=v,
                    pstrb=(1 << (self.bytes_per_word)) - 1,  # Full write strobe
                    prdata=0,
                    pprot=0,
                    pslverr=0
                ))
    self._update_current_state()
    self.write_storage.clear()

    return apb_cycles
```

This method:
1. Converts pending register writes to APB packets
2. Calculates the correct address for each register
3. Handles multi-word registers and register arrays
4. Updates the current state and clears the write storage

## Register Verification

The `compare_transactions` method compares expected and actual transactions:

```python
def compare_transactions(self, expected: List[APBPacket], found: List[APBPacket], title: str) -> List[Dict]:
    miscompares = []
    for exp, fnd in zip(expected, found):
        if exp.paddr != fnd.paddr:
            continue  # Skip if addresses don't match

        exp_bits = format(exp.prdata, f'0{self.apb_data_width}b')
        fnd_bits = format(fnd.prdata, f'0{self.apb_data_width}b')

        for register, info in self.registers.items():
            reg_address = (self.start_address + int(info['address'], 16)) & self.addr_mask
            if reg_address == exp.paddr:
                for field_name, field_info in info.items():
                    if isinstance(field_info, dict) and field_info.get('type') == 'field':
                        field_offset = self._parse_offset(field_info['offset'])
                        start = field_offset[0] % self.apb_data_width
                        end = min(field_offset[1] % self.apb_data_width + 1, self.apb_data_width)

                        exp_field = exp_bits[start:end]
                        fnd_field = fnd_bits[start:end]

                        if 'X' not in exp_field and exp_field != fnd_field:
                            miscompares.append({
                                'title': title,
                                'register': register,
                                'field': field_name,
                                'address': f'0x{exp.paddr:X}',
                                'expected': exp_field,
                                'found': fnd_field,
                                'bit_positions': f'{start}-{end-1}'
                            })

    return miscompares
```

This method:
1. Compares expected and actual APB transactions
2. Detects miscompares at the field level
3. Provides detailed information about miscompares
4. Handles 'X' (don't care) bits in expected values

## Register Map Utilities

The `RegisterMap` provides utility methods for register analysis:

```python
def get_register_field_map(self):
    """Get a mapping of registers to their fields."""
    register_field_map = {}
    for register_name, register_info in self.registers.items():
        fields = [field for field in register_info.keys() if register_info[field]['type'] == 'field']
        register_field_map[register_name] = fields
    return register_field_map

def get_register_offset_map(self):
    """Get a mapping of register names to their offsets."""
    return {reg_name: int(reg_info['offset'], 16) for reg_name, reg_info in self.registers.items()}

def get_combined_register_map(self):
    """Get a combined map of register fields and offsets."""
    field_map = self.get_register_field_map()
    offset_map = self.get_register_offset_map()
    return {
        reg: {'fields': field_map[reg], 'offset': offset}
        for reg, offset in offset_map.items()
    }
```

These methods provide different views of the register map for analysis and debugging.

## Advanced Features

### Read Transaction Generation

The `generate_read_transactions` method creates transactions to read registers:

```python
def generate_read_transactions(self) -> List[APBPacket]:
    read_transactions = []
    for register, info in self.registers.items():
        address = (self.start_address + int(info['address'], 16)) & self.addr_mask
        size = int(info['size'])
        count = int(info.get('count', '1'))

        for i in range(count):
            expected_data = ''
            for j in range(0, size * 8, self.apb_data_width):
                word_address = (address + (i * size) + (j // 8)) & self.addr_mask
                word_expected = ''

                # Process fields to determine expected values
                # ...

                read_transactions.append(APBPacket(
                    start_time=0,
                    count=i,
                    direction='READ',
                    pwrite=0,
                    paddr=word_address,
                    pwdata=0,
                    pstrb=0,
                    prdata=int(word_expected.replace('X', '0'), 2),
                    pprot=0,
                    pslverr=0
                ))

    return read_transactions
```

This method:
1. Creates read transactions for all registers
2. Calculates expected values based on field definitions
3. Handles read-only, read-write, and write-only fields
4. Generates transactions for multi-word registers and arrays

### Test Pattern Generation

The `RegisterMap` can generate test patterns for verification:

```python
def generate_write_even_transactions(self) -> List[APBPacket]:
    return self._generate_write_transactions(even=True)

def generate_write_odd_transactions(self) -> List[APBPacket]:
    return self._generate_write_transactions(even=False)

def _generate_write_transactions(self, even: bool) -> List[APBPacket]:
    write_transactions = []
    for register, info in self.registers.items():
        # Skip read-only registers
        if 'rw' not in info.get('sw', '').lower():
            continue

        # Generate transactions to write alternating bit patterns
        # ...

        return write_transactions
```

These methods generate test patterns for thorough register verification:
1. Even pattern: Set even-numbered bits to 1, odd to 0
2. Odd pattern: Set odd-numbered bits to 1, even to 0

## Implementation Insights

1. **Field-Oriented Design**: The register map works at the field level, not just register level
2. **Smart State Tracking**: Keeps track of both current state and pending writes
3. **Masked Writes**: Handles partial register updates through field masks
4. **Multi-Word Support**: Handles registers wider than the APB data width
5. **Register Arrays**: Supports arrays of registers with the same definition
6. **Flexible Addressing**: Calculates correct addresses based on register definitions
7. **Verification Support**: Provides methods for comparing expected and actual transactions
8. **Test Pattern Generation**: Generates patterns for thorough register verification

## Navigation

[↑ APB Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
