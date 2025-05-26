# Getting Started with CocoTBFramework

This guide will help you get started with using the CocoTBFramework for hardware verification. The framework provides a collection of Python components that make it easier to build verification environments using [Cocotb](https://www.cocotb.org/).

## Prerequisites

Before using the CocoTBFramework, ensure you have the following prerequisites installed:

- Python 3.6 or later
- Cocotb 1.6.0 or later
- A supported simulator (e.g., Verilator, ModelSim, VCS, Xcelium)
- NumPy (for memory model component)
- Rich (for enhanced console output with FieldConfig)

## Installation

1. Clone the CocoTBFramework repository:

```bash
git clone https://github.com/your-org/cocotbframework.git
```

2. Install the framework and its dependencies:

```bash
cd cocotbframework
pip install -e .
```

3. Verify the installation:

```bash
python -c "import CocoTBFramework; print(CocoTBFramework.__version__)"
```

## Basic Workflow

The typical workflow for using CocoTBFramework is:

1. **Design the Verification Plan**:
   - Identify the interfaces and protocols to verify
   - Determine coverage goals
   - Plan test scenarios

2. **Set Up Project Structure**:
   - Create a Cocotb test directory
   - Set up simulator configuration (Makefile)

3. **Create Verification Components**:
   - Define packet structures with FieldConfig
   - Set up monitors for key interfaces
   - Configure randomization strategies

4. **Write Tests**:
   - Implement test scenarios
   - Create sequences of transactions
   - Add coverage collection

5. **Run and Analyze**:
   - Execute tests
   - Analyze coverage
   - Debug failures

## Quick Start Example

Let's create a simple verification environment for an APB protocol interface:

### 1. Define the Field Configuration

```python
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition

# Create a field configuration for APB packets
apb_config = FieldConfig()

# Add standard APB fields
apb_config.add_field(
    FieldDefinition(
        name="paddr",
        bits=32,
        format="hex",
        description="APB Address"
    )
)

apb_config.add_field(
    FieldDefinition(
        name="pwrite",
        bits=1,
        format="bin",
        description="APB Write Enable"
    )
)

apb_config.add_field(
    FieldDefinition(
        name="psel",
        bits=1,
        format="bin",
        description="APB Select"
    )
)

apb_config.add_field(
    FieldDefinition(
        name="penable",
        bits=1,
        format="bin",
        description="APB Enable"
    )
)

apb_config.add_field(
    FieldDefinition(
        name="pwdata",
        bits=32,
        format="hex",
        description="APB Write Data"
    )
)

apb_config.add_field(
    FieldDefinition(
        name="prdata",
        bits=32,
        format="hex",
        description="APB Read Data"
    )
)
```

### 2. Set Up Randomization

```python
from CocoTBFramework.components.randomization_config import (
    RandomizationConfig, RandomizationMode, FieldRandomizationConfig
)

# Create randomization configuration
rand_config = RandomizationConfig(protocol_name="APB", seed=12345)

# Configure randomization for address
rand_config.create_constrained_config(
    "paddr",
    bins=[(0x0000, 0x0FFF), (0x1000, 0x1FFF)],
    weights=[0.3, 0.7]
)

# Configure randomization for write enable
rand_config.create_sequence_config(
    "pwrite",
    sequence=[0, 1, 1, 0, 1]  # Pattern of read/write operations
)

# Configure randomization for write data
rand_config.create_constrained_config(
    "pwdata",
    bins=[(0x00000000, 0xFFFFFFFF)],
    weights=[1.0]
)
```

### 3. Create a Test

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
from CocoTBFramework.components.packet import Packet
from CocoTBFramework.components.memory_model import MemoryModel

# Create a reference memory model
log = cocotb.logging.getLogger("cocotb.test")
memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)

@cocotb.test()
async def apb_basic_test(dut):
    """Test basic APB transactions."""
    # Create a clock
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    
    # Reset procedure
    dut.rst_n.value = 0
    await Timer(20, units="ns")
    dut.rst_n.value = 1
    await Timer(20, units="ns")
    
    # Run 10 random transactions
    for i in range(10):
        # Generate random values
        values = rand_config.generate_values(["paddr", "pwrite", "pwdata"])
        
        # Create packet with random values
        packet = Packet(apb_config, **values)
        packet.psel = 1
        packet.penable = 0
        
        # Display the packet
        log.info(f"Transaction {i+1}:")
        log.info(f"{packet}")
        
        # SETUP phase
        dut.paddr.value = packet.paddr
        dut.pwrite.value = packet.pwrite
        dut.psel.value = packet.psel
        dut.penable.value = packet.penable
        
        if packet.pwrite:
            dut.pwdata.value = packet.pwdata
        
        await RisingEdge(dut.clk)
        
        # ACCESS phase
        dut.penable.value = 1
        await RisingEdge(dut.clk)
        
        # Capture read data if this is a read
        if not packet.pwrite:
            packet.prdata = dut.prdata.value.integer
            log.info(f"Read data: 0x{packet.prdata:08X}")
        else:
            # Update memory model for write
            addr = packet.paddr
            data = memory.integer_to_bytearray(packet.pwdata, byte_length=4)
            memory.write(addr, data, 0b1111)
        
        # Idle phase
        dut.psel.value = 0
        dut.penable.value = 0
        await RisingEdge(dut.clk)
```

### 4. Run the Test

Create a simple Makefile:

```makefile
# Makefile for Cocotb tests
TOPLEVEL_LANG = verilog
VERILOG_SOURCES = $(shell pwd)/apb_interface.v
TOPLEVEL = apb_interface
MODULE = test_apb

include $(shell cocotb-config --makefiles)/Makefile.sim
```

Run the test:

```bash
make
```

## Next Steps

After getting familiar with the basic components, you can:

1. **Explore Protocol-Specific Components**:
   - Look at the components in the [APB](apb/index.md), [AXI4](axi4/index.md), [FIFO](fifo/index.md), or [GAXI](gaxi/index.md) directories

2. **Build a Complete Verification Environment**:
   - Create drivers, monitors, and scoreboards
   - Set up coverage collection
   - Create more advanced test scenarios

3. **Extend the Framework**:
   - Create custom components for your specific needs
   - Contribute improvements back to the framework

## Documentation

For more detailed information, refer to the component documentation:

- [Components Index](index.md) - Overview of all components
- [API Reference](api-reference.md) - Detailed API reference
- [Overview](overview.md) - Architecture and design overview

## Common Issues and Solutions

### Issue: Import Errors

If you encounter import errors, ensure:
- The package is installed correctly
- Your Python path includes the framework
- You're using the correct import paths

### Issue: Type Errors

If you encounter type errors:
- Check the parameter types against the documentation
- Ensure you're using appropriate data structures (e.g., bytearray vs. integer)

### Issue: Performance Problems

If your tests run slowly:
- Check if you're clearing the field cache appropriately
- Consider using the NumPy-based memory model
- Profile your Python code to identify bottlenecks

## Getting Help

If you need assistance:
- Check the documentation
- Look at the example code
- File an issue on the project repository

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
