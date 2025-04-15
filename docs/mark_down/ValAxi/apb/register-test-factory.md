# Register Test Factory Functions

This document provides factory functions that create test sequences for comprehensive register testing using the `RegisterMap` class.

## Core Factory Function

```python
def create_register_test_sequence(reg_map, test_type="walk", options=None):
    """
    Create a test sequence for register testing based on register map information.
    
    Args:
        reg_map: RegisterMap instance containing register definitions
        test_type: Type of test to generate ("walk", "field", "access", "reset", "stress", "random")
        options: Dictionary of test-specific options
        
    Returns:
        APBSequence: Configured test sequence
    """
    # Default options
    if options is None:
        options = {}
    
    # Select test generator based on test type
    if test_type == "walk":
        return _create_walk_test(reg_map, options)
    elif test_type == "field":
        return _create_field_test(reg_map, options)
    elif test_type == "access":
        return _create_access_test(reg_map, options)
    elif test_type == "reset":
        return _create_reset_test(reg_map, options)
    elif test_type == "stress":
        return _create_stress_test(reg_map, options)
    elif test_type == "random":
        return _create_random_test(reg_map, options)
    else:
        raise ValueError(f"Unknown test type: {test_type}")
```

## Type-Specific Test Generators

### 1. Walking Ones/Zeros Test

```python
def _create_walk_test(reg_map, options):
    """
    Create a walking ones/zeros test that writes patterns to each register
    and reads back to verify.
    
    Options:
        pattern: "walking_ones" or "walking_zeros" or "alternating" (default: "walking_ones")
        delay: Clock cycles between transactions (default: 2)
    """
    pattern = options.get("pattern", "walking_ones")
    delay = options.get("delay", 2)
    
    # Create sequence container
    sequence = APBSequence(
        name=f"register_walk_{pattern}_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )
    
    # For each register
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers that are not writable
        if "w" not in reg_info.get("sw", "").lower():
            continue
            
        # Get register address and size
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        reg_width = reg_size * 8
        
        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        
        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)
            
            # Generate test patterns
            if pattern == "walking_ones":
                # Walking ones: 0x00000001, 0x00000002, 0x00000004, etc.
                patterns = [1 << i for i in range(min(reg_width, 32))]
            elif pattern == "walking_zeros":
                # Walking zeros: 0xFFFFFFFE, 0xFFFFFFFD, 0xFFFFFFFB, etc.
                patterns = [0xFFFFFFFF ^ (1 << i) for i in range(min(reg_width, 32))]
            elif pattern == "alternating":
                # Alternating patterns: 0x55555555, 0xAAAAAAAA
                patterns = [0x55555555, 0xAAAAAAAA]
            else:
                raise ValueError(f"Unknown pattern: {pattern}")
                
            # Add test transactions for each pattern
            for pattern_value in patterns:
                # Write pattern
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(pattern_value)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)
                
                # Read back to verify
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)
    
    return sequence
```

### 2. Field-Specific Test

```python
def _create_field_test(reg_map, options):
    """
    Create a test that targets specific fields within registers.
    
    Options:
        fields: List of field names to test (default: all fields)
        values: List of test values (default: [0x0, 0x1, 0xF, 0xFF, 0xFFFF, 0xFFFFFFFF])
        delay: Clock cycles between transactions (default: 2)
    """
    fields = options.get("fields", None)  # None means all fields
    test_values = options.get("values", [0x0, 0x1, 0xF, 0xFF, 0xFFFF, 0xFFFFFFFF])
    delay = options.get("delay", 2)
    
    # Create sequence container
    sequence = APBSequence(
        name="register_field_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )
    
    # For each register
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers that are not writable
        if "w" not in reg_info.get("sw", "").lower():
            continue
            
        # Get register address and size
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        
        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        
        # Process each field in the register
        for field_name, field_info in reg_info.items():
            # Skip non-field entries
            if not isinstance(field_info, dict) or field_info.get("type") != "field":
                continue
                
            # Skip fields not in the test list (if a list is specified)
            if fields is not None and field_name not in fields:
                continue
                
            # Skip fields that are not writable
            if "w" not in field_info.get("sw", "").lower():
                continue
                
            # Get field offset (position)
            offset = field_info.get("offset", "0")
            if ":" in offset:
                high, low = map(int, offset.split(":"))
                field_width = high - low + 1
                shift = low
            else:
                field_width = 1
                shift = int(offset)
                
            # Create field mask
            field_mask = ((1 << field_width) - 1) << shift
            
            # Test each register instance
            for idx in range(reg_count):
                # Calculate address for this register instance
                addr = reg_addr + (idx * reg_size)
                
                # Test each value on this field
                for test_value in test_values:
                    # Truncate test value to field width
                    masked_value = (test_value & ((1 << field_width) - 1)) << shift
                    
                    # Read initial value
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)
                    
                    # Write field with test value (preserving other fields)
                    sequence.pwrite_seq.append(True)
                    sequence.addr_seq.append(addr)
                    # Note: The data value is a placeholder that will be
                    # updated by the test harness using read-modify-write
                    sequence.data_seq.append((~field_mask & 0xFFFFFFFF, masked_value))
                    sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                    sequence.inter_cycle_delays.append(delay)
                    
                    # Read back to verify
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)
    
    return sequence
```

### 3. Access Rights Test

```python
def _create_access_test(reg_map, options):
    """
    Create a test that verifies register access rights (R/W, RO, WO, etc.).
    
    Options:
        delay: Clock cycles between transactions (default: 2)
    """
    delay = options.get("delay", 2)
    
    # Create sequence container
    sequence = APBSequence(
        name="register_access_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )
    
    # For each register
    for reg_name, reg_info in reg_map.registers.items():
        # Get register address and size
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        
        # Get access rights
        sw_access = reg_info.get("sw", "rw").lower()
        
        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        
        # Test each register instance
        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)
            
            # Test read access
            if "r" in sw_access:
                # Read should succeed
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)
            
            # Test write access
            if "w" in sw_access:
                # Write should succeed - use 0x55555555 pattern
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(0x55555555)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)
                
                # Read back to verify (if readable)
                if "r" in sw_access:
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)
                    
                # Write inverse pattern - 0xAAAAAAAA
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(0xAAAAAAAA)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)
                
                # Read back to verify (if readable)
                if "r" in sw_access:
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)
            
            # Special handling for W1C (write-1-to-clear) registers
            if "w1c" in sw_access:
                # First read to get current value
                if "r" in sw_access:
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)
                
                # Write all 1s to clear all bits
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(0xFFFFFFFF)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)
                
                # Read back to verify bits are cleared
                if "r" in sw_access:
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)
    
    return sequence
```

### 4. Reset Test

```python
def _create_reset_test(reg_map, options):
    """
    Create a test that verifies registers return to default values after reset.
    
    Options:
        delay: Clock cycles between transactions (default: 2)
        reset_type: Type of reset to perform ("hard", "soft") (default: "hard")
    """
    delay = options.get("delay", 2)
    reset_type = options.get("reset_type", "hard")
    
    # Create sequence container
    sequence = APBSequence(
        name=f"register_reset_{reset_type}_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )
    
    # Special flag to indicate a reset should be performed
    sequence.reset_points = []
    
    # For each register
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers with no default value
        if "default" not in reg_info:
            continue
            
        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        default_value = int(reg_info.get("default", "0"), 16)
        
        # Get access rights
        sw_access = reg_info.get("sw", "rw").lower()
        
        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        
        # Test each register instance
        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)
            
            # Only test registers that are readable and writable
            if "r" in sw_access and "w" in sw_access:
                # First, read default value
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)
                
                # Write non-default value (inverse of default)
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(~default_value & 0xFFFFFFFF)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)
                
                # Read back to verify change
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)
    
    # Add reset point after writing all registers
    sequence.reset_points.append(len(sequence.pwrite_seq))
    
    # After reset, read all registers to verify default values
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers with no default value
        if "default" not in reg_info:
            continue
            
        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        
        # Get access rights
        sw_access = reg_info.get("sw", "rw").lower()
        
        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        
        # Test each register instance
        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)
            
            # Check default value after reset
            if "r" in sw_access:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)
    
    return sequence
```

### 5. Stress Test

```python
def _create_stress_test(reg_map, options):
    """
    Create a stress test with rapid back-to-back register accesses.
    
    Options:
        iterations: Number of test iterations (default: 100)
        delay: Clock cycles between transactions (default: 0)
    """
    iterations = options.get("iterations", 100)
    delay = options.get("delay", 0)  # Minimum delay for stress testing
    
    # Create sequence container
    sequence = APBSequence(
        name="register_stress_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )
    
    # Collect all writable registers
    writable_regs = []
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers that are not writable
        if "w" not in reg_info.get("sw", "").lower():
            continue
            
        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        
        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        
        # Add each register instance
        for idx in range(reg_count):
            addr = reg_addr + (idx * reg_size)
            writable_regs.append((addr, reg_size))
    
    # Collect all readable registers
    readable_regs = []
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers that are not readable
        if "r" not in reg_info.get("sw", "").lower():
            continue
            
        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        
        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        
        # Add each register instance
        for idx in range(reg_count):
            addr = reg_addr + (idx * reg_size)
            readable_regs.append(addr)
    
    # Generate stress test patterns
    import random
    patterns = [0xAAAAAAAA, 0x55555555, 0xFFFFFFFF, 0x00000000]
    
    # Generate the test sequence
    for _ in range(iterations):
        # Pick random action: 0=write, 1=read
        action = random.randint(0, 1)
        
        if action == 0 and writable_regs:  # Write
            # Pick random register
            addr, size = random.choice(writable_regs)
            
            # Pick random data pattern
            data = random.choice(patterns)
            
            # Add write transaction
            sequence.pwrite_seq.append(True)
            sequence.addr_seq.append(addr)
            sequence.data_seq.append(data)
            sequence.strb_seq.append((1 << size) - 1)  # All bytes
            sequence.inter_cycle_delays.append(delay)
            
        elif readable_regs:  # Read
            # Pick random register
            addr = random.choice(readable_regs)
            
            # Add read transaction
            sequence.pwrite_seq.append(False)
            sequence.addr_seq.append(addr)
            sequence.inter_cycle_delays.append(delay)
    
    return sequence
```

### 6. Random Test

```python
def _create_random_test(reg_map, options):
    """
    Create a randomized test with various register operations.
    
    Options:
        iterations: Number of test iterations (default: 100)
        seed: Random seed for reproducibility (default: None)
        delay_min: Minimum delay between transactions (default: 1)
        delay_max: Maximum delay between transactions (default: 5)
    """
    iterations = options.get("iterations", 100)
    seed = options.get("seed", None)
    delay_min = options.get("delay_min", 1)
    delay_max = options.get("delay_max", 5)
    
    # Set random seed if provided
    import random
    if seed is not None:
        random.seed(seed)
    
    # Create sequence container
    sequence = APBSequence(
        name="register_random_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )
    
    # Build register information dictionary
    reg_info_dict = {}
    for reg_name, reg_info in reg_map.registers.items():
        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        sw_access = reg_info.get("sw", "rw").lower()
        
        # Get default value if available
        default_value = 0
        if "default" in reg_info:
            default_value = int(reg_info.get("default", "0"), 16)
        
        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        
        # Process each register instance
        for idx in range(reg_count):
            addr = reg_addr + (idx * reg_size)
            reg_info_dict[addr] = {
                "size": reg_size,
                "sw_access": sw_access,
                "default": default_value,
                "fields": {}
            }
            
            # Add field information
            for field_name, field_info in reg_info.items():
                if isinstance(field_info, dict) and field_info.get("type") == "field":
                    offset = field_info.get("offset", "0")
                    field_sw = field_info.get("sw", sw_access).lower()
                    
                    # Process field offset
                    if ":" in offset:
                        high, low = map(int, offset.split(":"))
                        field_width = high - low + 1
                        shift = low
                    else:
                        field_width = 1
                        shift = int(offset)
                    
                    # Add field info
                    reg_info_dict[addr]["fields"][field_name] = {
                        "width": field_width,
                        "shift": shift,
                        "sw_access": field_sw,
                        "mask": ((1 << field_width) - 1) << shift
                    }
    
    # Generate random test sequence
    for _ in range(iterations):
        # Pick random register
        if not reg_info_dict:
            break
        addr = random.choice(list(reg_info_dict.keys()))
        info = reg_info_dict[addr]
        
        # Pick random operation
        ops = []
        if "r" in info["sw_access"]:
            ops.append("read")
        if "w" in info["sw_access"]:
            ops.append("write")
            if info["fields"]:
                ops.append("field_write")
        
        if not ops:
            continue
        
        op = random.choice(ops)
        
        # Random delay
        delay = random.randint(delay_min, delay_max)
        
        if op == "read":
            # Simple register read
            sequence.pwrite_seq.append(False)
            sequence.addr_seq.append(addr)
            sequence.inter_cycle_delays.append(delay)
            
        elif op == "write":
            # Full register write
            data = random.randint(0, (1 << (info["size"] * 8)) - 1)
            
            sequence.pwrite_seq.append(True)
            sequence.addr_seq.append(addr)
            sequence.data_seq.append(data)
            sequence.strb_seq.append((1 << info["size"]) - 1)  # All bytes
            sequence.inter_cycle_delays.append(delay)
            
            # Add read-back verification
            if "r" in info["sw_access"]:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)
                
        elif op == "field_write" and info["fields"]:
            # Pick random field
            field_name = random.choice(list(info["fields"].keys()))
            field = info["fields"][field_name]
            
            # Skip if not writable
            if "w" not in field["sw_access"]:
                continue
                
            # Generate random field value
            field_value = random.randint(0, (1 << field["width"]) - 1)
            masked_value = (field_value << field["shift"]) & field["mask"]
            
            # Read current value
            if "r" in info["sw_access"]:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)
            
            # Write field with read-modify-write
            sequence.pwrite_seq.append(True)
            sequence.addr_seq.append(addr)
            # Note: The data value is a placeholder that will be
            # updated by the test harness using read-modify-write
            sequence.data_seq.append((~field["mask"] & 0xFFFFFFFF, masked_value))
            sequence.strb_seq.append((1 << info["size"]) - 1)  # All bytes
            sequence.inter_cycle_delays.append(delay)
            
            # Read back to verify
            if "r" in info["sw_access"]:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)
    
    return sequence
```

## Usage Examples

### Basic Walking Ones Test

```python
# Create register map from UVM file
reg_map = RegisterMap(
    filename="registers.py",
    apb_data_width=32,
    apb_addr_width=24,
    start_address=0x7F0000,
    log=log
)

# Create walking ones test
sequence = create_register_test_sequence(
    reg_map,
    test_type="walk",
    options={
        "pattern": "walking_ones",
        "delay": 2
    }
)

# Use the sequence for testing
await run_test_sequence(apb_master, sequence)
```

### Field-Level Test

```python
# Create field-specific test for control registers
sequence = create_register_test_sequence(
    reg_map,
    test_type="field",
    options={
        "fields": ["enable", "interrupt_mask", "mode"],
        "values": [0x0, 0x1, 0xF],
        "delay": 1
    }
)

# Use the sequence for testing
await run_test_sequence(apb_master, sequence)
```

### Reset Test

```python
# Create reset test
sequence = create_register_test_sequence(
    reg_map,
    test_type="reset",
    options={
        "reset_type": "hard",
        "delay": 2
    }
)

# Run the reset test with special handling
await run_reset_test(dut, apb_master, sequence)
```

### Stress Test

```python
# Create stress test
sequence = create_register_test_sequence(
    reg_map,
    test_type="stress",
    options={
        "iterations": 1000,
        "delay": 0  # Minimum delay for rapid back-to-back testing
    }
)

# Run the stress test
await run_test_sequence(apb_master, sequence)
```

## Test Runner Function

```python
async def run_test_sequence(apb_master, sequence, verify_func=None):
    """
    Run a register test sequence through an APB master.
    
    Args:
        apb_master: APB master driver
        sequence: Test sequence to run
        verify_func: Optional function to verify each transaction
        
    Returns:
        List of transaction results
    """
    results = []
    read_data = {}  # For read-modify-write operations
    
    # Execute each transaction in the sequence
    for i in range(len(sequence.pwrite_seq)):
        is_write = sequence.pwrite_seq[i]
        addr = sequence.addr_seq[i]
        
        if is_write:
            data = sequence.data_seq[i] if i < len(sequence.data_seq) else 0
            strobe = sequence.strb_seq[i] if i < len(sequence.strb_seq) else 0xF
            
            # Handle read-modify-write tuple
            if isinstance(data, tuple) and len(data) == 2:
                mask, value = data
                if addr in read_data:
                    # Apply mask and value to previous read data
                    data = (read_data[addr] & mask) | value
                else:
                    # No previous read data, use value directly
                    data = value
            
            # Create and send write transaction
            packet = APBPacket(
                count=i,
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=strobe,
                pprot=0
            )
        else:
            # Create and send read transaction
            packet = APBPacket(
                count=i,
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0,
                pprot=0
            )
        
        # Send the transaction
        await apb_master.send(packet)
        await apb_master.wait_for_queue_empty()
        
        # Store read data for potential read-modify-write
        if not is_write and hasattr(packet, 'prdata'):
            read_data[addr] = packet.prdata
        
        # Add result to list
        results.append(packet)
        
        # Call verification function if provided
        if verify_func:
            await verify_func(packet, i)
        
        # Add delay if specified
        if i < len(sequence.inter_cycle_delays):
            delay = sequence.inter_cycle_delays[i]
            if delay > 0:
                await cocotb.triggers.Timer(delay, units="ns")
    
    return results

async def run_reset_test(dut, apb_master, sequence):
    """
    Run a reset test sequence with reset between transactions.
    
    Args:
        dut: Device under test
        apb_master: APB master driver
        sequence: Reset test sequence
        
    Returns:
        List of transaction results
    """
    results = []
    
    # Get reset points
    reset_points = getattr(sequence, 'reset_points', [])
    
    # Execute each transaction in the sequence
    for i in range(len(sequence.pwrite_seq)):
        # Check if we need to reset
        if i in reset_points:
            # Perform reset
            dut.reset_n.value = 0
            await cocotb.triggers.Timer(100, units="ns")
            dut.reset_n.value = 1
            await cocotb.triggers.Timer(100, units="ns")
            
            # Reset APB master
            await apb_master.reset_bus()
        
        # Create and send transaction
        is_write = sequence.pwrite_seq[i]
        addr = sequence.addr_seq[i]
        
        if is_write:
            data = sequence.data_seq[i] if i < len(sequence.data_seq) else 0
            strobe = sequence.strb_seq[i] if i < len(sequence.strb_seq) else 0xF
            
            packet = APBPacket(
                count=i,
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=strobe,
                pprot=0
            )
        else:
            packet = APBPacket(
                count=i,
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0,
                pprot=0
            )
        
        # Send the transaction
        await apb_master.send(packet)
        await apb_master.wait_for_queue_empty()
        
        # Add result to list
        results.append(packet)
        
        # Add delay if specified
        if i < len(sequence.inter_cycle_delays):
            delay = sequence.inter_cycle_delays[i]
            if delay > 0:
                await cocotb.triggers.Timer(delay, units="ns")
    
    return results
```
