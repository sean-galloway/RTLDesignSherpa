# AXI4 Scoreboard Documentation

## Overview

The AXI4 Scoreboard module provides specialized components for verifying AXI4 protocol transactions. It includes two main classes:

1. `AXI4Scoreboard`: Core verification component for standard AXI4 transactions
2. `AXI4MemoryScoreboard`: Extended scoreboard that uses a memory model as reference

These components allow comprehensive verification of AXI4 interfaces by tracking and comparing transactions between master and slave sides, validating protocol rules, and verifying memory operations.

## AXI4Scoreboard Class

### Purpose

The `AXI4Scoreboard` provides core functionality for monitoring and verifying AXI4 protocol transactions, ensuring that master-side transactions are correctly reflected on the slave side.

### Class Definition

```python
class AXI4Scoreboard(BaseScoreboard):
    """
    Scoreboard for AXI4 protocol transactions.

    This class provides:
    - Tracking and matching of master and slave-side transactions
    - Protocol compliance checking
    - Transaction statistics
    """

    def __init__(self, name, id_width=8, addr_width=32, data_width=32, user_width=1, log=None):
        """
        Initialize AXI4 Scoreboard.

        Args:
            name: Scoreboard name
            id_width: Width of ID fields (default: 8)
            addr_width: Width of address fields (default: 32)
            data_width: Width of data fields (default: 32)
            user_width: Width of user fields (default: 1)
            log: Logger instance
        """
```

### Key Features

#### Transaction Tracking

- Separate tracking for write and read transactions
- Support for multiple outstanding transactions via IDs
- Tracking of AW, W, B, AR, and R channels

#### Monitor Integration

```python
def add_master_monitor(self, monitor):
    """Connect a master-side AXI4 monitor to the scoreboard"""
```
Registers callbacks for master-side write and read transactions.

```python
def add_slave_monitor(self, monitor):
    """Connect a slave-side AXI4 monitor to the scoreboard"""
```
Registers callbacks for slave-side write and read transactions.

#### Transaction Handling

```python
def _handle_master_write(self, id_value, transaction):
    """Process a completed write transaction from the master side"""
```
Processes write transactions from the master side and attempts to match them with slave-side transactions.

```python
def _handle_slave_write(self, id_value, transaction):
    """Process a completed write transaction from the slave side"""
```
Processes write transactions from the slave side and attempts to match them with master-side transactions.

Similar methods exist for handling read transactions.

#### Transaction Comparison

```python
def _check_write_match(self, id_value, master_tx, slave_tx):
    """Check if master and slave-side write transactions match"""
```
Compares master and slave write transactions for protocol correctness:
- Validates address channel signals (AWADDR, AWLEN, AWSIZE, AWBURST)
- Ensures data beats match in count and content
- Validates response channel signals (BRESP)

```python
def _check_read_match(self, id_value, master_tx, slave_tx):
    """Check if master and slave-side read transactions match"""
```
Compares master and slave read transactions for protocol correctness:
- Validates address channel signals (ARADDR, ARLEN, ARSIZE, ARBURST)
- Ensures data beats match in count and content
- Validates response channel signals (RRESP, RLAST)

#### Reporting and Checks

```python
def report(self):
    """Generate comprehensive report of AXI4 transaction verification"""
```
Generates a detailed report of verification activity including:
- Matched and mismatched transactions
- Protocol errors
- Unmatched transactions

```python
def check_all_transactions_matched(self):
    """Check if all transactions have been matched"""
```
Checks if all transactions have been matched correctly.

## AXI4MemoryScoreboard Class

### Purpose

The `AXI4MemoryScoreboard` extends the basic AXI4 scoreboard by adding a memory model as a "golden" reference. This allows verification that memory operations behave correctly.

### Class Definition

```python
class AXI4MemoryScoreboard(AXI4Scoreboard):
    """
    AXI4 scoreboard that uses a memory model for verification.

    This class extends the standard AXI4Scoreboard by:
    - Using a shared memory model as the "golden" reference
    - Verifying all memory operations against the model
    - Tracking out-of-order operations
    """

    def __init__(self, name, memory_model, id_width=8, addr_width=32, data_width=32, user_width=1, log=None):
        """
        Initialize AXI4 Memory Scoreboard.

        Args:
            name: Scoreboard name
            memory_model: Memory model to use as reference
            id_width: Width of ID fields (default: 8)
            addr_width: Width of address fields (default: 32)
            data_width: Width of data fields (default: 32)
            user_width: Width of user fields (default: 1)
            log: Logger instance
        """
```

### Key Features

#### Memory Operation Tracking

```python
def add_write(self, addr, data, strb=None):
    """
    Add a memory write operation.

    Args:
        addr: Address to write to
        data: Data written
        strb: Write strobe mask (default: all enabled)
    """
```
Adds a write operation to the memory model and tracks it in the scoreboard.

```python
def verify_read(self, addr, data):
    """
    Verify a memory read operation.

    Args:
        addr: Address read from
        data: Data returned

    Returns:
        bool: True if read data matches expected data
    """
```
Verifies that read data matches the expected data in the memory model.

#### Enhanced Reporting

```python
def report(self):
    """Generate comprehensive report including memory operations"""
```
Extends the basic report with information about memory operations.

## Usage Examples

### Basic AXI4 Scoreboard

```python
# Create AXI4 Scoreboard
axi4_sb = AXI4Scoreboard("AXI4_SB", 
                          id_width=4,
                          addr_width=32,
                          data_width=64,
                          log=logger)

# Connect monitors
axi4_sb.add_master_monitor(master_monitor)
axi4_sb.add_slave_monitor(slave_monitor)

# Run tests...

# Check and report
if not axi4_sb.check_all_transactions_matched():
    print("ERROR: Not all transactions matched")
    
print(axi4_sb.report())
```

### Memory-Based Verification

```python
# Create memory model
mem_model = MemoryModel(num_lines=1024, bytes_per_line=8, log=logger)

# Create Memory Scoreboard
axi4_mem_sb = AXI4MemoryScoreboard("AXI4_MEM_SB", 
                                   memory_model=mem_model,
                                   id_width=4,
                                   addr_width=32,
                                   data_width=64,
                                   log=logger)

# Connect monitors
axi4_mem_sb.add_master_monitor(master_monitor)
axi4_mem_sb.add_slave_monitor(slave_monitor)

# Run tests...

# Verify a specific read operation
read_addr = 0x1000
read_data = 0xABCD1234
if not axi4_mem_sb.verify_read(read_addr, read_data):
    print(f"ERROR: Read data mismatch at 0x{read_addr:X}")

# Check and report
print(axi4_mem_sb.report())
```

## Transaction Structure

The scoreboard expects AXI4 transactions in the following format:

### Write Transaction

```python
{
    'aw_transaction': {  # Address Write channel
        'awaddr': 0x1000,
        'awlen': 3,      # 4 beats
        'awsize': 2,     # 4 bytes per beat
        'awburst': 1,    # INCR burst type
        # Other AW signals...
    },
    'w_transactions': [  # Write Data channel
        {
            'wdata': 0x12345678,
            'wstrb': 0xF,
            'wlast': False
        },
        # More data beats...
        {
            'wdata': 0xABCDEF00,
            'wstrb': 0xF,
            'wlast': True  # Last beat
        }
    ],
    'b_transaction': {  # Write Response channel
        'bresp': 0,     # OKAY response
        # Other B signals...
    }
}
```

### Read Transaction

```python
{
    'ar_transaction': {  # Address Read channel
        'araddr': 0x2000,
        'arlen': 1,      # 2 beats
        'arsize': 2,     # 4 bytes per beat
        'arburst': 1,    # INCR burst type
        # Other AR signals...
    },
    'r_transactions': [  # Read Data channel
        {
            'rdata': 0x12345678,
            'rresp': 0,
            'rlast': False
        },
        {
            'rdata': 0xABCDEF00,
            'rresp': 0,
            'rlast': True  # Last beat
        }
    ]
}
```

## Best Practices

1. Always connect both master and slave monitors to the scoreboard
2. Use the memory scoreboard when verifying memory interfaces
3. Check the report for details on any mismatches or protocol errors
4. Clear the scoreboard between test phases with `clear()`
5. Verify both read and write transactions
6. Pay attention to burst transfers and ensure all beats are correctly processed

## Navigation

[↑ Scoreboards Index](index.md) | [↑ CocoTBFramework Index](../index.md)
