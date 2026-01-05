<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# CRC Testing Module Documentation

## Overview

The `CRCTB` class provides comprehensive testing for Cyclic Redundancy Check (CRC) implementations. It supports multiple CRC standards, configurable parameters, and validates CRC calculations against reference implementations with extensive test data patterns.

## Purpose and Use Cases

### When to Use CRCTB
- Testing CRC calculation engines for data integrity
- Verifying compliance with standard CRC polynomials (CRC-8, CRC-16, CRC-32, etc.)
- Validating configurable CRC parameters (polynomial, initial value, reflection)
- Testing cascade CRC operations for large data blocks
- Ensuring proper CRC initialization and finalization

### CRC Fundamentals
CRC provides error detection through polynomial division:
- **Polynomial**: Generator polynomial defining CRC algorithm
- **Initial Value**: Starting value for CRC register
- **Input/Output Reflection**: Bit order reversal options
- **XOR Output**: Final value XORed with result

## Configuration

### Environment Variables
- `PARAM_DATA_WIDTH`: Input data width in bits
- `PARAM_CRC_WIDTH`: CRC output width (8, 16, 32, 40, 64 bits)
- `PARAM_POLY`: CRC polynomial (hex format)
- `PARAM_POLY_INIT`: Initial CRC value (hex format)
- `PARAM_REFIN`: Input reflection (0/1)
- `PARAM_REFOUT`: Output reflection (0/1) 
- `PARAM_XOROUT`: Final XOR value (hex format)

### Expected DUT Interface

```verilog
module crc_engine #(
    parameter DATA_WIDTH = 32,
    parameter CRC_WIDTH = 32
) (
    input                    i_clk,              // Clock
    input                    i_rst_n,            // Reset
    
    // Configuration
    input  [CRC_WIDTH-1:0]   POLY,               // CRC polynomial
    input  [CRC_WIDTH-1:0]   POLY_INIT,          // Initial value
    input  [CRC_WIDTH-1:0]   XOROUT,             // Final XOR value
    
    // Data interface
    input  [DATA_WIDTH-1:0]  i_data,             // Input data
    input                    i_load_crc_start,   // Load initial CRC
    input                    i_load_from_cascade, // Process data
    input  [DATA_WIDTH/8-1:0] i_cascade_sel,     // Byte enable
    
    // CRC output
    output [CRC_WIDTH-1:0]   o_crc               // CRC result
);
```

## Test Methodologies

### 1. Test Data Generation (`generate_test_data`)
**Purpose**: Create comprehensive test patterns for CRC validation

**Test Patterns**:
```python
# Walking patterns
walk_1_through_0s = [1 << i for i in range(DATA_WIDTH)]  # 0001, 0010, 0100...
walk_0_through_1s = [~(1 << i) for i in range(DATA_WIDTH)]  # 1110, 1101, 1011...

# Boundary values
boundary_values = [0, 2**DATA_WIDTH - 1]  # All zeros, all ones

# Random values
random_values = [random.randint(0, 2**DATA_WIDTH - 1) for _ in range(rnd_count)]
```

**Reference Calculation**:
```python
# Using Python CRC library for golden reference
from crc import Calculator, Configuration

cfg = Configuration(
    width=CRC_WIDTH,
    polynomial=POLY,
    init_value=POLY_INIT,
    final_xor_value=XOROUT,
    reverse_input=REFIN,
    reverse_output=REFOUT
)
calculator = Calculator(cfg)

for data in test_values:
    data_bytes = data.to_bytes(CHUNKS, 'little')
    expected_crc = calculator.checksum(data_bytes)
    test_data.append((data, expected_crc))
```

### 2. Main Loop Testing (`main_loop`)
**Purpose**: Validate CRC calculations against reference implementation

**Test Sequence**:
```python
for data, expected_crc in test_data:
    # 1. Initialize CRC register
    self.dut.i_load_crc_start.value = 1
    await self.wait_clocks('i_clk', 1)
    self.dut.i_load_crc_start.value = 0
    
    # Verify initial value
    assert self.dut.o_crc.value == POLY_INIT
    
    # 2. Process data
    self.dut.i_data.value = data
    self.dut.i_load_from_cascade.value = 1
    self.dut.i_cascade_sel.value = highest_byte_enable
    await self.wait_clocks('i_clk', 1)
    
    # 3. Verify result
    actual_crc = self.dut.o_crc.value
    assert actual_crc == expected_crc
```

### 3. CRC Standard Compliance
**Purpose**: Test against industry-standard CRC configurations

The module includes pre-defined configurations for common CRC standards:

#### CRC-8 Standards
- CRC-08, CRC-08_CDMA2000, CRC-08_DARC, CRC-08_DVB-S2
- CRC-08_EBU, CRC-08_I-CODE, CRC-08_ITU, CRC-08_MAXIM
- CRC-08_ROHC, CRC-08_WCDMA

#### CRC-16 Standards  
- CRC-16_ARC, CRC-16_CCITT-FALSE, CRC-16_MODBUS
- CRC-16_XMODEM, CRC-16_X-25, CRC-16_USB

#### CRC-32 Standards
- CRC-32 (Ethernet), CRC-32_BZIP2, CRC-32C (Castagnoli)
- CRC-32_POSIX, CRC-32_SATA, CRC-32Q

#### CRC-64 Standards
- CRC-64_ECMA-182, CRC-64_GO-ISO, CRC-64_XZ

### 4. Parameter Validation
**Purpose**: Ensure configuration parameters are correctly applied

**Configuration Tests**:
```python
def verify_configuration(self):
    # Verify polynomial is applied
    assert self.dut.POLY.value == self.crc_poly
    
    # Verify initial value is applied  
    assert self.dut.POLY_INIT.value == self.crc_poly_initial
    
    # Verify XOR output is applied
    assert self.dut.XOROUT.value == self.xor_output
```

## Implementation Examples

### Basic CRC Test
```python
import cocotb
from CocoTBFramework.tbclasses.common.crc_testing import CRCTB

@cocotb.test()
async def test_crc_basic(dut):
    """Basic CRC functionality test"""
    tb = CRCTB(dut, rnd_count=100)
    
    # Initialize
    tb.assert_reset()
    await tb.start_clock('i_clk', 10, 'ns')
    await tb.wait_clocks('i_clk', 5)
    tb.deassert_reset()
    
    # Generate test data and run tests
    tb.generate_test_data()
    await tb.main_loop()
```

### CRC Standard Compliance Test
```python
@cocotb.test()
async def test_crc32_ethernet(dut):
    """Test CRC-32 Ethernet standard"""
    
    # Set environment for CRC-32
    os.environ['PARAM_CRC_WIDTH'] = '32'
    os.environ['PARAM_POLY'] = '0x04C11DB7'
    os.environ['PARAM_POLY_INIT'] = '0xFFFFFFFF'
    os.environ['PARAM_REFIN'] = '1'
    os.environ['PARAM_REFOUT'] = '1'
    os.environ['PARAM_XOROUT'] = '0xFFFFFFFF'
    
    tb = CRCTB(dut, rnd_count=500)
    tb.print_settings()
    
    # Initialize and test
    await tb.reset_sequence()
    tb.generate_test_data()
    await tb.main_loop()
```

### Custom CRC Configuration
```python
@cocotb.test()
async def test_custom_crc(dut):
    """Test custom CRC configuration"""
    tb = CRCTB(dut, rnd_count=200)
    
    # Override default configuration
    tb.crc_width = 16
    tb.crc_poly = 0x1021  # CRC-16-CCITT
    tb.crc_poly_initial = 0x0000
    tb.reflected_input = 0
    tb.reflected_output = 0
    tb.xor_output = 0x0000
    
    # Rebuild configuration
    tb.cfg = Configuration(
        width=tb.crc_width,
        polynomial=tb.crc_poly,
        init_value=tb.crc_poly_initial,
        final_xor_value=tb.xor_output,
        reverse_input=tb.reflected_input,
        reverse_output=tb.reflected_output
    )
    tb.calculator = Calculator(tb.cfg)
    
    tb.generate_test_data()
    await tb.main_loop()
```

### Cascade Operation Test
```python
@cocotb.test()
async def test_crc_cascade(dut):
    """Test CRC cascade operations for large data"""
    tb = CRCTB(dut, rnd_count=50)
    
    await tb.reset_sequence()
    
    # Test processing data in chunks
    large_data = 0x123456789ABCDEF0
    chunks = [(large_data >> i) & 0xFFFFFFFF for i in range(0, 64, 32)]
    
    # Initialize CRC
    tb.dut.i_load_crc_start.value = 1
    await tb.wait_clocks('i_clk', 1)
    tb.dut.i_load_crc_start.value = 0
    
    # Process each chunk
    for chunk in chunks:
        tb.dut.i_data.value = chunk
        tb.dut.i_load_from_cascade.value = 1
        tb.dut.i_cascade_sel.value = 0xF  # All bytes valid
        await tb.wait_clocks('i_clk', 1)
        tb.dut.i_load_from_cascade.value = 0
    
    # Verify final result
    final_crc = tb.dut.o_crc.value
    # Compare against reference calculation
```

## CRC Algorithm Details

### Polynomial Mathematics
CRC uses polynomial arithmetic in GF(2):
```
Division: message(x) / generator(x) = quotient(x) + remainder(x)
CRC = remainder(x)
```

### Bit Processing Order
- **Normal**: Process MSB first
- **Reflected**: Process LSB first (reverse bit order)

### Common Polynomials
| Standard | Width | Polynomial | Usage |
|----------|-------|------------|-------|
| CRC-8 | 8 | 0x07 | Simple checksums |
| CRC-16-CCITT | 16 | 0x1021 | Serial communications |
| CRC-32 | 32 | 0x04C11DB7 | Ethernet, ZIP files |
| CRC-32C | 32 | 0x1EDC6F41 | iSCSI, SCTP |

## Error Analysis

### Common Failure Patterns
1. **Polynomial Mismatch**: Wrong generator polynomial configured
2. **Bit Order Issues**: Incorrect input/output reflection settings
3. **Initialization Errors**: Wrong initial CRC value
4. **XOR Output**: Incorrect final XOR operation

### Debug Information
```
CRC test failed:
  test_data=0x12345678   expected_crc=0xABCDEF12  actual_crc=0x87654321
  Configuration:
    POLY=0x04C11DB7  INIT=0xFFFFFFFF  REFIN=1  REFOUT=1  XOROUT=0xFFFFFFFF
  Debug: Check polynomial and reflection settings
```

### Troubleshooting
1. **Verify Standard**: Ensure configuration matches target CRC standard
2. **Check Bit Order**: Verify input data bit ordering
3. **Validate Reference**: Confirm reference implementation settings
4. **Test Incremental**: Start with simple data patterns

## Performance Considerations

### Test Data Scaling
- **Small widths**: Generate all possible patterns
- **Large widths**: Use statistical sampling with representative patterns
- **Stress testing**: Include boundary conditions and random data

### Byte Enable Testing
```python
def find_highest_byte_enable(data_width):
    """Calculate byte enable for highest byte position"""
    highest_byte_position = (data_width // 8) - 1
    return 1 << highest_byte_position
```

This module provides comprehensive CRC validation ensuring compliance with industry standards and proper implementation of configurable CRC parameters across various data widths and polynomial configurations.