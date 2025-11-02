# axi_split_calculator.py

A specialized tool for calculating AXI transaction splitting logic when transactions cross alignment boundaries, essential for AXI4 protocol compliance and high-performance system design.

## Overview

The `axi_split_calculator.py` script provides precise calculations for AXI transaction splitting when transactions cross configurable address boundaries (e.g., 4KB page boundaries for memory controllers). This tool is crucial for AXI4 master designs that need to handle boundary-crossing transactions correctly.

## Purpose

AXI4 transactions that cross certain address boundaries (typically 4KB for DDR memory controllers) must be split into multiple smaller transactions. This script calculates:

- Whether a transaction requires splitting
- Where to split the transaction
- The lengths of resulting split transactions
- Next boundary address calculations

## Usage

### Command Line Interface

```bash
python3 bin/axi_split_calculator.py [options]
```

### Interactive Mode

The script can be run interactively or imported as a module for use in other tools.

### Function Interface

```python
calculate_axi_split(aw, dw, alignment_mask, addr, length)
```

**Parameters:**
- `aw` (int): Address width in bits (typically 32 or 64)
- `dw` (int): Data width in bits (32, 64, 128, 256, 512, 1024)
- `alignment_mask` (int): Boundary alignment mask (e.g., 0xFFF for 4KB boundaries)
- `addr` (int): Starting address of the transaction
- `length` (int): Transaction length in AXI encoding (beats - 1, so 0 = 1 beat)

## Examples

### Example 1: 4KB Boundary Crossing

```python
# 64-bit data, 4KB boundaries, address just before boundary
result = calculate_axi_split(
    aw=32,                    # 32-bit address space
    dw=64,                    # 64-bit data width (8 bytes per beat)
    alignment_mask=0xFFF,     # 4KB boundaries (4096 bytes)
    addr=0x00000FF8,          # Address 8 bytes before 4KB boundary
    length=15                 # 16 beats total (128 bytes)
)

# Result shows:
# - split_required: True
# - split_len: 0 (1 beat before boundary)
# - remaining_len: 14 (15 beats after boundary)
```

### Example 2: No Split Required

```python
# Transaction that doesn't cross boundary
result = calculate_axi_split(
    aw=32,
    dw=32,                    # 32-bit data width (4 bytes per beat)
    alignment_mask=0xFFF,     # 4KB boundaries
    addr=0x00001000,          # Aligned to 4KB boundary
    length=3                  # 4 beats total (16 bytes)
)

# Result shows:
# - split_required: False
# - split_len: 3 (original length)
# - remaining_len: 0 (no remaining transaction)
```

### Example 3: Complex Boundary Calculation

```python
# Large transaction crossing multiple potential splits
result = calculate_axi_split(
    aw=32,
    dw=256,                   # 256-bit data width (32 bytes per beat)
    alignment_mask=0xFFF,     # 4KB boundaries
    addr=0x00000F00,          # 256 bytes before boundary
    length=31                 # 32 beats total (1024 bytes)
)

# Result shows split calculations for first boundary crossing
```

## Return Value Structure

The function returns a comprehensive dictionary with calculation details:

```python
{
    'inputs': {
        'aw': 32,
        'dw': 64,
        'alignment_mask': '0xFFF',
        'boundary_size': 4096,
        'addr': '0x00000FF8',
        'aligned_addr': '0x00000FF8',
        'length': 15,
        'total_beats': 16,
        'total_bytes': 128,
        'bytes_per_beat': 8
    },
    'calculation': {
        'transaction_end_addr': '0x00001077',
        'next_boundary_addr': '0x00001000',
        'bytes_to_boundary': 8,
        'beats_to_boundary': 1,
        'crosses_boundary': True,
        'has_beats_before_boundary': True
    },
    'results': {
        'split_required': True,
        'split_len': 0,           # First transaction: 1 beat
        'remaining_len': 14       # Second transaction: 15 beats
    }
}
```

## Key Features

### Address Alignment

- Automatically aligns addresses to data width boundaries
- Handles unaligned starting addresses correctly
- Supports arbitrary address widths (32-bit, 64-bit systems)

### Data Width Support

- Supports all standard AXI data widths (32, 64, 128, 256, 512, 1024 bits)
- Calculates bytes per beat automatically
- Handles byte-to-beat conversions

### Boundary Handling

- Configurable boundary alignment (4KB, 64KB, etc.)
- Supports arbitrary boundary sizes via mask parameter
- Handles address space wraparound correctly

### AXI Protocol Compliance

- Uses proper AXI length encoding (length = beats - 1)
- Handles maximum burst length constraints
- Provides results suitable for AXI4 master implementation

## Common Use Cases

### Memory Controller Interface Design

```python
# DDR4 memory with 4KB page boundaries
def check_ddr_split(addr, length):
    return calculate_axi_split(
        aw=32,
        dw=128,               # 128-bit DDR interface
        alignment_mask=0xFFF, # 4KB DDR pages
        addr=addr,
        length=length
    )
```

### PCIe Transaction Splitting

```python
# PCIe with 4KB Memory Request Boundary (MRB)
def check_pcie_split(addr, length):
    return calculate_axi_split(
        aw=64,                # 64-bit PCIe addressing
        dw=256,               # 256-bit PCIe interface
        alignment_mask=0xFFF, # 4KB MRB
        addr=addr,
        length=length
    )
```

### Cache Line Boundary Analysis

```python
# 64-byte cache line boundaries
def check_cache_split(addr, length):
    return calculate_axi_split(
        aw=32,
        dw=64,
        alignment_mask=0x3F,  # 64-byte cache lines
        addr=addr,
        length=length
    )
```

## Integration with RTL Design

### SystemVerilog Module Generation

The calculator can be used to verify RTL splitting logic or generate test cases:

```python
# Generate test vectors for RTL verification
def generate_split_test_vectors():
    test_cases = []

    for addr in range(0x0FF0, 0x1010, 8):
        for length in [0, 1, 3, 7, 15, 31]:  # Various burst lengths
            result = calculate_axi_split(32, 64, 0xFFF, addr, length)
            test_cases.append({
                'addr': addr,
                'length': length,
                'expected_split': result['results']['split_required'],
                'expected_split_len': result['results']['split_len'],
                'expected_remaining_len': result['results']['remaining_len']
            })

    return test_cases
```

### CocoTB Test Integration

```python
# Use in CocoTB testbenches
@cocotb.test()
async def test_axi_splitter(dut):
    for test_case in generate_split_test_vectors():
        # Apply inputs
        dut.i_addr <= test_case['addr']
        dut.i_length <= test_case['length']

        await Timer(1, units='ns')

        # Check outputs
        assert dut.o_split_required == test_case['expected_split']
        assert dut.o_split_len == test_case['expected_split_len']
        assert dut.o_remaining_len == test_case['expected_remaining_len']
```

## Algorithm Details

### Boundary Crossing Detection

1. **Address Alignment**: Align starting address to data width boundary
2. **End Address Calculation**: Calculate transaction end address
3. **Next Boundary**: Find next alignment boundary address
4. **Crossing Check**: Determine if transaction crosses boundary
5. **Split Calculation**: Calculate optimal split point and lengths

### Edge Case Handling

- **Address Wraparound**: Handles address space overflow correctly
- **Zero-Length Transactions**: Properly handles single-beat transactions
- **Boundary-Aligned Addresses**: Optimizes for aligned starting addresses
- **Maximum Burst Lengths**: Respects AXI4 burst length limits

## Performance Considerations

### Calculation Complexity

- **Time Complexity**: O(1) - All calculations are constant time
- **Space Complexity**: O(1) - Minimal memory usage
- **Precision**: Uses exact integer arithmetic, no floating-point errors

### Optimization Features

- Pre-calculates common values (bytes per beat, masks)
- Uses bitwise operations for alignment calculations
- Minimizes conditional branches in hot paths

## Verification and Validation

### Test Coverage

The calculator includes comprehensive test coverage for:
- All standard AXI data widths
- Various boundary sizes (64B, 4KB, 64KB)
- Edge cases (wraparound, alignment, zero-length)
- Real-world transaction patterns

### Correctness Verification

Results have been verified against:
- AXI4 specification requirements
- Hardware implementation behavior
- Industry-standard memory controller specs

## Related Tools

- **[axi4_master_rd.md](../RTLAmba/axi/axi4_master_rd.md)**: AXI4 read master implementation
- **[axi4_master_wr.md](../RTLAmba/axi/axi4_master_wr.md)**: AXI4 write master implementation
- **[struct_test_script.md](struct_test_script.md)**: Structural testing framework
- **[sv_interface_flattener.md](sv_interface_flattener.md)**: SystemVerilog interface utilities

## Future Enhancements

- GUI interface for interactive calculation
- Batch processing of multiple transactions
- Performance profiling and optimization recommendations
- Integration with AXI4 IP generation tools

---

[Back to Scripts Index](index.md)

---