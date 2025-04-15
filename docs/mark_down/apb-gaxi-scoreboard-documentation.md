# APB-GAXI Scoreboard Documentation

## Overview
The `APBGAXIScoreboard` class provides a specialized scoreboard for cross-protocol verification between APB (Advanced Peripheral Bus) and GAXI (Generic AXI) protocols. This component allows verification engineers to track and compare transactions between these two different protocols, ensuring that data transfers correctly between APB and GAXI interfaces.

## Purpose
In complex SoC designs, it's common to have bridges between different protocols. The APB-GAXI scoreboard verifies that:
- APB write transactions are properly translated to GAXI write transactions
- APB read transactions result in correct GAXI read transactions
- Address mapping is preserved between protocols
- Data values match between corresponding transactions

## Class Definition

```python
class APBGAXIScoreboard:
    """
    Scoreboard for verifying APB and GAXI transactions match.

    This scoreboard can:
    1. Verify APB transactions against GAXI transactions
    2. Track transactions by address
    3. Report mismatches in data or control signals
    4. Provide coverage statistics
    """

    def __init__(self, name, log=None):
        """
        Initialize the APB-GAXI scoreboard.

        Args:
            name: Scoreboard name
            log: Logger instance
        """
```

## Key Features

### Transaction Queues
The scoreboard maintains separate queues for different transaction types:
- `apb_writes`: Stores APB write transactions indexed by address
- `apb_reads`: Stores APB read transactions indexed by address
- `gaxi_writes`: Stores GAXI write transactions indexed by address
- `gaxi_reads`: Stores GAXI read transactions indexed by address

### Statistics Tracking
- `total_matches`: Counts matching transactions
- `total_mismatches`: Counts mismatched transactions
- `total_dropped`: Counts unmatched transactions
- `total_verified`: Total number of verified transactions
- `address_coverage`: Tracks unique addresses seen
- `type_coverage`: Counts transactions by type (apb_write, apb_read, gaxi_write, gaxi_read)

## Core Methods

### Transaction Management

```python
def add_apb_transaction(self, transaction):
    """
    Add an APB transaction to the scoreboard.
    """
```
Adds an APB transaction and attempts to match it with existing GAXI transactions.

```python
def add_gaxi_transaction(self, transaction):
    """
    Add a GAXI transaction to the scoreboard.

    Args:
        transaction: GAXI transaction to add
    """
```
Adds a GAXI transaction and attempts to match it with existing APB transactions.

### Transaction Matching

```python
def _check_write_matches(self, addr, transaction, is_apb=True):
    """
    Check for write transaction matches.
    """
```
Compares APB and GAXI write transactions with the same address for matching data.

```python
def _check_read_matches(self, addr, transaction, is_apb=True):
    """
    Check for read transaction matches.

    Args:
        addr: Transaction address
        transaction: New transaction
        is_apb: True if transaction is APB, False if GAXI
            
    Returns:
        True if a match was found, False otherwise
    """
```
Compares APB and GAXI read transactions with the same address for matching data.

### Checking and Reporting

```python
async def check_scoreboard(self, timeout=None):
    """
    Check scoreboard for unmatched transactions.

    Args:
        timeout: Optional timeout in ns before checking

    Returns:
        True if all transactions matched, False otherwise
    """
```
Verifies that all transactions have been matched and reports any unmatched transactions.

```python
def report(self):
    """
    Generate a report of scoreboard statistics.

    Returns:
        String with scoreboard report
    """
```
Produces a comprehensive report of transaction statistics.

```python
def clear(self):
    """Clear all transactions and reset statistics."""
```
Resets the scoreboard for a new test phase.

## Usage Example

```python
# Create the scoreboard
scoreboard = APBGAXIScoreboard("APB_GAXI_SB", log=logger)

# Add APB write transaction
apb_write = APBTransaction()
apb_write.paddr = 0x1000
apb_write.pwdata = 0xABCD
apb_write.direction = "WRITE"
apb_write.start_time = cocotb.utils.get_sim_time('ns')
scoreboard.add_apb_transaction(apb_write)

# Add corresponding GAXI write transaction
gaxi_write = GAXITransaction()
gaxi_write.addr = 0x1000
gaxi_write.data = 0xABCD
gaxi_write.cmd = 1  # Write
gaxi_write.start_time = cocotb.utils.get_sim_time('ns')
scoreboard.add_gaxi_transaction(gaxi_write)

# After test completion, check for unmatched transactions
await scoreboard.check_scoreboard(timeout=100)  # Wait 100ns before checking

# Print detailed report
print(scoreboard.report())
```

## Transaction Flow

1. APB or GAXI transactions are added to the scoreboard with `add_apb_transaction()` or `add_gaxi_transaction()`.
2. When a transaction is added, the scoreboard attempts to find a matching transaction in the opposite protocol.
3. If a match is found, both transactions are marked as matched and statistics are updated.
4. If no match is found, the transaction is queued for later matching.
5. At the end of the test, `check_scoreboard()` checks for any unmatched transactions.
6. The `report()` method generates comprehensive statistics on transaction matching.

## Address-Based Matching

Transactions are matched based on their 12-bit address (lowest 12 bits). For each address:
1. The scoreboard maintains separate queues for APB and GAXI transactions.
2. When a transaction is added, it checks for a matching transaction in the opposite protocol with the same address.
3. Data values are compared to ensure they match.
4. Transactions are processed in FIFO order for each address.

## Verification Metrics

The scoreboard calculates several key metrics:
- **Verification Rate**: Percentage of transactions successfully verified
- **Match Rate**: Percentage of verified transactions that matched
- **Address Coverage**: Number of unique addresses seen
- **Transaction Type Coverage**: Distribution of transaction types

These metrics help assess the completeness and correctness of protocol translation between APB and GAXI.

## Best Practices

1. Add both APB and GAXI transactions to the scoreboard as they occur.
2. Call `check_scoreboard()` at the end of the test to verify all transactions matched.
3. Examine the report for detailed statistics on transaction matching.
4. Check the verification rate to ensure complete coverage.
5. Look for specific addresses with unmatched transactions to identify problem areas.
6. Clear the scoreboard between test phases with `clear()`.
