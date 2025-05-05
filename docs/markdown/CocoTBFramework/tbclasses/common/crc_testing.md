# CRC Testing

## Overview

The `crc_testing` module provides a comprehensive testbench for verifying Cyclic Redundancy Check (CRC) implementations. It supports testing various CRC standards with different polynomial configurations, input/output reflections, and XOR patterns. The module includes a comprehensive database of standard CRC configurations for validation against known-good implementations.

## Class Definition

```python
class CRCTB(TBBase):
    """A class for testing CRC functionality.

    This class is used to test CRC functionality by generating test data 
    based on the provided settings and calculating checksums.
    """
    def __init__(self, dut, rnd_count):
        """Initialize the CRCTesting class.

        Args:
            dut: The design under test.
            rnd_count: The number of random values to generate for testing.
        """
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.data_width = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.chunks = self.convert_to_int(dut.CHUNKS.value)
        self.d_nybbles = self.chunks // 2
        self.crc_width = self.convert_to_int(os.environ.get('PARAM_CRC_WIDTH', '0'))
        self.nybbles = self.crc_width // 4
        mask = "F" * self.nybbles
        self.crc_poly = self.convert_to_int(os.environ.get('PARAM_POLY', '0')) & int(mask, 16)
        self.crc_poly_initial = self.convert_to_int(os.environ.get('PARAM_POLY_INIT', '0')) & int(mask, 16)
        self.reflected_input = self.convert_to_int(os.environ.get('PARAM_REFIN', '0'))
        self.reflected_output = self.convert_to_int(os.environ.get('PARAM_REFOUT', '0'))
        self.xor_output = self.convert_to_int(os.environ.get('PARAM_XOROUT', '0')) & int(mask, 16)
        self.rnd_count = rnd_count
        self.test_values = []
        self.test_data = []
        self.cfg = Configuration(
            width=self.crc_width,
            polynomial=self.crc_poly,
            init_value=self.crc_poly_initial,
            final_xor_value=self.xor_output,
            reverse_input=self.reflected_input,
            reverse_output=self.reflected_output
        )
        self.calculator = Calculator(self.cfg)
```

## Key Features

- Support for all standard CRC configurations (CRC-8, CRC-16, CRC-32, CRC-64)
- Parameter-driven configuration via environment variables
- Reference Python CRC implementation for result verification
- Test vector generation including directed and random patterns
- Comprehensive database of CRC parameters for standard algorithms
- Verification against known-good CRC implementations

## Primary Methods

### clear_interface

Clears the DUT interface by setting all inputs to 0.

```python
def clear_interface(self):
    """Clear all interface signals to default values."""
    # Implementation...
```

### assert_reset / deassert_reset

Control the reset signal.

```python
def assert_reset(self):
    """Assert reset signal."""
    # Implementation...

def deassert_reset(self):
    """Deassert reset signal."""
    # Implementation...
```

### generate_test_data

Generates test data for CRC testing.

```python
def generate_test_data(self):
    """Generate test data for CRC testing.

    This method generates test data for CRC testing based on the configured 
    settings and calculates checksums for the generated data.
    """
    # Generate directed test patterns (walking bits, etc.)
    walk_1_through_0s = [1 << i for i in range(self.data_width)]
    all_ones = 2**self.data_width - 1
    walk_0_through_1s = [all_ones ^ (1 << i) for i in range(self.data_width)]
    self.test_values = [0, all_ones] + walk_1_through_0s + walk_0_through_1s

    # Calculate expected CRC for each test value
    for data in self.test_values:
        data_bytes = data.to_bytes(self.chunks, 'little')
        ecc = self.calculator.checksum(data_bytes)
        self.test_data.append((data, ecc))

    # Add random test values
    # Implementation continues...
```

### main_loop

Main test method that verifies CRC calculation for all test vectors.

```python
async def main_loop(self):
    """Main test method that runs all CRC tests.
    
    This method uses the generated test vectors to verify the DUT's CRC 
    calculation matches the expected results from the reference implementation.
    """
    for data, expected_crc in self.test_data:
        # Test 1: Load initial CRC value and check
        self.dut.i_load_crc_start.value = 1
        await self.wait_clocks('i_clk',1)
        self.dut.i_load_crc_start.value = 0
        assert self.dut.o_crc.value == self.crc_poly_initial, "CRC initial value incorrect"

        # Test 2: Load data and validate CRC calculation
        # Implementation continues...
```

### print_settings

Prints the current CRC settings.

```python
def print_settings(self):
    """Print the settings of the CRCTesting class.

    This method prints out the settings related to data width, chunks, 
    CRC width, polynomial, initial polynomial value, input reflection, 
    output reflection, and XOR output for CRC testing.
    """
    # Implementation...
```

## CRC Parameter Database

The module includes a comprehensive database of standard CRC configurations:

```python
crc_parameters = [
    ('CRC-08', 8, '8', "8'h07", "8'h00", '0', '0', "8'h00"),
    ('CRC-08_CDMA2000', 8, '8', "8'h9B", "8'hFF", '0', '0', "8'h00"),
    ('CRC-08_DARC', 8, '8', "8'h39", "8'h00", '1', '1', "8'h00"),
    # Many more entries...
]
```

Each entry contains:
1. CRC Algorithm Name
2. Data Width
3. CRC Width
4. Polynomial (Verilog format)
5. Initial Value
6. Input Reflection Flag
7. Output Reflection Flag
8. Final XOR Value

## Test Methodology

The CRC testing methodology includes:

1. **Parameter Validation**: Verify the DUT's CRC parameters match the configuration
2. **Initial Value Test**: Verify the CRC module initializes to the correct value
3. **Directed Testing**: Test with specific patterns (walking ones, etc.)
4. **Random Testing**: Test with random data values
5. **Reference Comparison**: Compare DUT results with software CRC implementation
6. **Standard Algorithm Check**: Verify against known CRC standards

## Implementation Approach

The implementation provides detailed verification against a reference software implementation:

```python
# Test CRC calculation
self.dut.i_data.value = data
self.dut.i_load_from_cascade.value = 1
self.dut.i_cascade_sel.value = self.find_highest_byte_enable(self.data_width)
await self.wait_clocks('i_clk',1)
self.dut.i_data.value = 0
self.dut.i_load_from_cascade.value = 0
self.dut.i_cascade_sel.value = 0
await self.wait_clocks('i_clk',1)

# Verify the CRC output matches the expected value
found_crc = self.dut.o_crc.value
msg = f'test_data=0x{hex(data)[2:].zfill(self.d_nybbles)}   expected_crc=0x{hex(expected_crc)[2:].zfill(self.nybbles)}  actual_crc=0x{hex(found_crc)[2:].zfill(self.nybbles)}'
self.log.info(msg)
assert hex(found_crc) == hex(expected_crc), f"Unexpected CRC result: data=0x{hex(data)[2:].zfill(self.d_nybbles)}  expected {hex(expected_crc)} --> found {hex(found_crc)}"
```

## Example Usage

Basic usage of the CRC testbench:

```python
from CocoTBFramework.tbclasses.common.crc_testing import CRCTB

@cocotb.test()
async def test_crc(dut):
    # Create testbench
    tb = CRCTB(dut, rnd_count=20)
    
    # Print settings
    tb.print_settings()
    
    # Generate test data
    tb.generate_test_data()
    
    # Run tests
    await tb.main_loop()
```

Testing a specific CRC standard:

```python
@cocotb.test()
async def test_crc32(dut):
    # Set parameters for CRC-32
    os.environ['PARAM_DATA_WIDTH'] = '32'
    os.environ['PARAM_CRC_WIDTH'] = '32'
    os.environ['PARAM_POLY'] = '0x04C11DB7'
    os.environ['PARAM_POLY_INIT'] = '0xFFFFFFFF'
    os.environ['PARAM_REFIN'] = '1'
    os.environ['PARAM_REFOUT'] = '1'
    os.environ['PARAM_XOROUT'] = '0xFFFFFFFF'
    
    # Create testbench
    tb = CRCTB(dut, rnd_count=50)
    
    # Generate test data
    tb.generate_test_data()
    
    # Run tests
    await tb.main_loop()
```

## Implementation Notes

- DUT signals use standard names: i_load_crc_start, i_data, o_crc, etc.
- PARAM_* environment variables control CRC configuration
- Data is applied using the cascade mechanism to model real usage
- Highest byte enable is used for standard cascade operation
- All test results are compared against a reference Python CRC implementation
- The module includes a comprehensive database of standard CRC algorithms
- Input/output reflection and final XOR operations are properly accounted for

## See Also

- [CRC Standards](https://reveng.sourceforge.io/crc-catalogue/) - Reference for CRC parameters
- [CRC Python Library](https://pypi.org/project/crc/) - Reference implementation used by testbench

## Navigation

[↑ Common Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
