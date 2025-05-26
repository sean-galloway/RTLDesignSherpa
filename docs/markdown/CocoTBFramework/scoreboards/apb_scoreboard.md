# APB Scoreboard Documentation

## Overview

The APB Scoreboard module provides specialized components for verifying APB (Advanced Peripheral Bus) protocol transactions. It includes:

1. `APBScoreboard`: Verifies standard APB transactions
2. `APBCrossbarScoreboard`: Verifies APB crossbar routing between multiple masters and slaves
3. `APBtoGAXITransformer`: Transforms APB transactions to GAXI format for cross-protocol verification

## APBScoreboard

This class extends the `BaseScoreboard` to provide APB-specific transaction verification.

### Class Definition

```python
class APBScoreboard(BaseScoreboard):
    """Scoreboard for APB transactions"""

    def __init__(self, name, addr_width=32, data_width=32, log=None):
        super().__init__(name, log)
        self.addr_width = addr_width
        self.data_width = data_width
        self.strb_width = data_width // 8
        
        # Track which master initiated each transaction
        self.master_transactions = defaultdict(list)
```

### Key Methods

#### Transaction Comparison

```python
def _compare_transactions(self, expected, actual):
    """Compare APB cycles based on direction, address, and data"""
```
Compares APB packets for equality, validating their types and fields.

#### Mismatch Logging

```python
def _log_mismatch(self, expected, actual):
    """Enhanced mismatch logging for APB cycles"""
```
Provides detailed APB-specific logging of transaction mismatches, including detailed field-by-field comparison.

#### Source Tracking

```python
def add_expected_with_source(self, transaction, master_id):
    """Add an expected transaction with source information"""
```
Adds an expected transaction while tracking which master initiated it.

## APBCrossbarScoreboard

This specialized scoreboard verifies APB crossbar functionality, checking that transactions from masters are correctly routed to the appropriate slaves.

### Class Definition


```python
class APBCrossbarScoreboard:
    """Router scoreboard for APB crossbar testing"""
    
    def __init__(self, name, num_slaves, addr_width=32, data_width=32, log=None):
        """
        Initialize APB crossbar scoreboard with multiple slave scoreboards
        """
```

### Key Features

- Manages multiple slave scoreboards
- Supports custom address mapping for routing decisions
- Tracks transaction sources (master IDs)
- Provides overall results across all slaves

### Key Methods

#### Address Mapping

```python
def set_address_map(self, addr_map):
    """
    Set custom address map for routing transactions
    """
```
Configures the address ranges for each slave in the crossbar.

```python
def get_slave_idx(self, addr):
    """
    Determine which slave an address should go to
    """
```
Determines which slave a transaction should be routed to based on its address.

#### Transaction Routing

```python
def add_master_transaction(self, transaction, master_id):
    """
    Add a transaction from a master, routing to correct slave scoreboard
    """
```
Adds a transaction from a master and routes it to the appropriate slave scoreboard.

```python
def add_slave_transaction(self, transaction, slave_idx):
    """
    Add a transaction from a slave to its scoreboard
    """
```
Adds a transaction from a slave to its corresponding scoreboard.

#### Results and Reporting

```python
def result(self):
    """
    Get overall result as minimum of all slave results
    """
```
Calculates the overall pass rate as the minimum of all slave pass rates.

```python
def report(self):
    """
    Generate detailed report of all scoreboards
    """
```
Generates a comprehensive report of all slave scoreboards.

## APBtoGAXITransformer

This transformer converts APB transactions to GAXI format for cross-protocol verification.

### Class Definition

```python
class APBtoGAXITransformer(ProtocolTransformer):
    """Transformer from APB to GAXI transactions"""

    def __init__(self, gaxi_field_config, packet_class, log=None):
        super().__init__("APB", "GAXI", log)
        self.gaxi_field_config = gaxi_field_config
        self.packet_class = packet_class
```

### Key Methods

```python
def transform(self, apb_cycle):
    """Transform APB cycle to one or more GAXI transactions"""
```
Converts an APB transaction to GAXI format by mapping the relevant fields.

## Usage Examples

### Basic APB Verification

```python
# Create APB scoreboard
apb_sb = APBScoreboard("APB_SB", addr_width=32, data_width=32, log=logger)

# Add expected transaction
expected_tx = APBPacket(paddr=0x1000, pwdata=0xABCD, direction="WRITE")
apb_sb.add_expected(expected_tx)

# Add actual transaction (triggers comparison)
actual_tx = APBPacket(paddr=0x1000, pwdata=0xABCD, direction="WRITE")
apb_sb.add_actual(actual_tx)

# Get results
result = apb_sb.result()  # 1.0 for perfect match
print(apb_sb.report())    # Detailed report
```

### APB Crossbar Verification

```python
# Create crossbar scoreboard with 4 slaves
crossbar_sb = APBCrossbarScoreboard("Crossbar_SB", num_slaves=4, log=logger)

# Set custom address map
addr_map = [
    (0x0000, 0x0FFF),  # Slave 0: 0x0000-0x0FFF
    (0x1000, 0x1FFF),  # Slave 1: 0x1000-0x1FFF
    (0x2000, 0x2FFF),  # Slave 2: 0x2000-0x2FFF
    (0x3000, 0x3FFF)   # Slave 3: 0x3000-0x3FFF
]
crossbar_sb.set_address_map(addr_map)

# Add master transaction (automatically routed to slave 1)
master_tx = APBPacket(paddr=0x1234, pwdata=0xABCD, direction="WRITE")
crossbar_sb.add_master_transaction(master_tx, master_id=0)

# Add slave transaction
slave_tx = APBPacket(paddr=0x1234, pwdata=0xABCD, direction="WRITE")
crossbar_sb.add_slave_transaction(slave_tx, slave_idx=1)

# Get results
result = crossbar_sb.result()
print(crossbar_sb.report())
```

### Cross-Protocol Verification (APB to GAXI)

```python
# Create GAXI field configuration and packet class
gaxi_config = FieldConfig.create_standard(addr_width=32, data_width=32)
gaxi_packet_cls = GAXIPacket

# Create transformer
transformer = APBtoGAXITransformer(gaxi_config, gaxi_packet_cls, log=logger)

# Create scoreboard and set transformer
apb_sb = APBScoreboard("APB_SB", log=logger)
apb_sb.set_transformer(transformer)

# Add expected APB transaction (will be transformed to GAXI)
apb_tx = APBPacket(paddr=0x1000, pwdata=0xABCD, direction="WRITE")
apb_sb.add_expected(apb_tx)

# Add actual GAXI transaction (for comparison)
gaxi_tx = GAXIPacket(gaxi_config, addr=0x1000, data=0xABCD)
apb_sb.add_actual(gaxi_tx)

# Get results
result = apb_sb.result()
```

## Best Practices
1. Use `add_expected_with_source()` when tracking transactions from multiple masters
2. Set appropriate address mapping in `APBCrossbarScoreboard` for accurate routing
3. Use the transformer when integrating APB with GAXI components
4. Always check both the result (pass rate) and detailed report for verification

## Navigation

[↑ Scoreboards Index](index.md) | [↑ CocoTBFramework Index](../index.md)
