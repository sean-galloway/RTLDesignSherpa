# Scoreboards Overview

## Introduction

The scoreboard components are central to the verification process, providing essential mechanisms for checking that the behavior of a device under test (DUT) matches expected functionality. In the CocoTBFramework, scoreboards handle comparison between expected and actual transactions across different protocols, track verification statistics, and provide detailed reports of test results.

## Architecture

The scoreboard architecture follows a hierarchical pattern:

```
BaseScoreboard (Abstract)
    |
    +---APBScoreboard
    |   |
    |   +---APBCrossbarScoreboard
    |
    +---AXI4Scoreboard
    |   |
    |   +---AXI4MemoryScoreboard
    |
    +---FIFOScoreboard
    |
    +---GAXIScoreboard
```

This hierarchical design enables code reuse while allowing protocol-specific verification. The `BaseScoreboard` provides common functionality, and protocol-specific scoreboards implement custom comparison logic.

## Core Functionality

All scoreboards provide the following core functionality:

1. **Transaction Queue Management**: Maintain separate queues for expected and actual transactions
2. **Comparison Logic**: Compare transactions according to protocol-specific rules
3. **Error Tracking**: Count and track mismatched transactions
4. **Statistics Gathering**: Maintain metrics on transaction verification
5. **Reporting**: Generate comprehensive reports of verification results
6. **Protocol Transformation**: Support cross-protocol verification through transformers

## Expected vs. Actual Model

Scoreboards operate on an expected vs. actual model:

```
Expected Transactions      Actual Transactions
       |                          |
       v                          v
    +------------------------------+
    |         Scoreboard          |
    +------------------------------+
                  |
                  v
      Success Rate and Mismatches
```

1. **Expected Transactions**: These typically come from reference models, test sequences, or known good implementations
2. **Actual Transactions**: These come from monitors observing the DUT behavior
3. **Comparison**: Scoreboards compare expected and actual transactions, either in order or using matching algorithms

## Cross-Protocol Verification

A key feature is cross-protocol verification, enabling comparison between transactions in different protocols:

```
Protocol A              Protocol B
Transactions            Transactions
     |                       |
     v                       v
+------------------+  +-----------------+
|   Transformer    |  |                 |
+------------------+  |   Scoreboard    |
          |           |                 |
          +---------->|                 |
                      +-----------------+
```

The transformer converts transactions from one protocol to another before comparison, allowing verification across protocol boundaries (e.g., APB to GAXI).

## Memory Integration

Scoreboards can integrate with memory models for enhanced validation:

```
Transactions           Memory Model
     |                      |
     v                      v
+----------------------------+
|  Memory-Based Scoreboard   |
+----------------------------+
            |
            v
  Verification Results
```

This is particularly useful for protocol interfaces that interact with memory (like AXI4).

## Available Scoreboards

### Basic Scoreboards

1. **BaseScoreboard**: Abstract base class for all scoreboards
2. **APBScoreboard**: Verifies APB (Advanced Peripheral Bus) transactions
3. **AXI4Scoreboard**: Verifies AXI4 protocol transactions
4. **FIFOScoreboard**: Verifies FIFO interface transactions
5. **GAXIScoreboard**: Verifies GAXI (Generic AXI) transactions

### Specialized Scoreboards

1. **APBCrossbarScoreboard**: Specialized scoreboard for APB crossbar verification
2. **AXI4MemoryScoreboard**: Extends AXI4 scoreboard with memory model integration
3. **APB-GAXI Scoreboard**: Verifies transactions between APB and GAXI interfaces

## Implementation Approach

### Transaction Comparison

All scoreboard implementations must override these key methods:

```python
def _compare_transactions(self, expected, actual):
    """Compare two transactions based on protocol requirements"""
    # Protocol-specific comparison logic

def _log_mismatch(self, expected, actual):
    """Log detailed information about mismatched transactions"""
    # Protocol-specific mismatch reporting
```

### Verification Metrics

Scoreboards track several key metrics:

1. **Transaction Count**: Total number of transactions verified
2. **Error Count**: Number of mismatched transactions
3. **Pass Rate**: Ratio of successful to total transactions
4. **Mismatch Details**: Details of each failed comparison
5. **Coverage**: Optional tracking of coverage metrics

## Practical Applications

### Basic Verification Flow

```python
# Create a scoreboard
sb = APBScoreboard("APB_SB")

# Connect a monitor to the scoreboard
apb_monitor.add_callback(sb.monitor_callback)

# Run the test...

# Check results
result = sb.result()  # Returns pass rate from 0.0 to 1.0
if result < 1.0:
    print(sb.report())  # Print detailed information about mismatches
```

### Cross-Protocol Verification

```python
# Create a transformer
transformer = APBtoGAXITransformer(gaxi_config, GAXIPacket)

# Create a scoreboard with the transformer
apb_sb = APBScoreboard("APB_SB")
apb_sb.set_transformer(transformer)

# Add APB transaction
apb_tx = APBPacket(pwrite=1, paddr=0x1000, pwdata=0xABCD)
apb_sb.add_expected(apb_tx)  # Will be transformed to GAXI

# Add GAXI transaction
gaxi_tx = GAXIPacket(addr=0x1000, data=0xABCD)
apb_sb.add_actual(gaxi_tx)  # Compared with transformed APB transaction
```

## Implementation Details

For a comprehensive breakdown of implementation details for each scoreboard file, see the [Implementation Details](scoreboards-details.md) document.

## Best Practices

1. **Choose the Right Scoreboard**: Select the scoreboard specific to your protocol
2. **Configure Before Use**: Set up all options before adding transactions
3. **Use Transformers**: For cross-protocol verification, use the appropriate transformer
4. **Check Both Statistics and Reports**: Look at the numeric result and the detailed report
5. **Clear Between Tests**: Call `clear()` between different test phases
6. **Handle Out-of-Order Transactions**: For protocols that can complete out of order, use the appropriate matching algorithm
7. **Add Expected Transactions First**: For predictable behavior, add expected transactions before actuals
8. **Monitor Coverage**: Track which features have been verified

## Navigation

[↑ Scoreboards Index](index.md) | [↑ CocoTBFramework Index](../index.md)
