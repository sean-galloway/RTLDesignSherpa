# ArbiterMonitor

## Overview

The `ArbiterMonitor` component provides a flexible monitoring infrastructure for observing and analyzing arbiter behavior in digital designs. It supports various types of arbiters including round-robin and weighted round-robin implementations.

## Features

- Monitoring of request and grant signals with timing information
- Automatic transaction tracking and statistical analysis
- Support for both round-robin and weighted round-robin arbiters
- Customizable callbacks for events
- Fairness analysis using Jain's fairness index

## Classes

### ArbiterTransaction

A named tuple that represents a single arbiter transaction with the following fields:

- `req_vector`: Request vector from clients
- `gnt_vector`: Grant vector indicating which client was selected
- `gnt_id`: ID of the granted client
- `cycle_count`: Number of cycles between request and grant
- `timestamp`: Timestamp when grant was issued
- `weights`: Optional weights for weighted arbiters
- `metadata`: Dictionary for any additional metadata

### ArbiterMonitor

The main monitoring class that observes arbiter transactions.

#### Constructor Parameters

```python
def __init__(self, dut, title, clock, reset_n, req_signal, gnt_valid_signal, gnt_signal,
             gnt_id_signal, gnt_ack_signal=None, block_arb_signal=None,
             max_thresh_signal=None, is_weighted=False, clients=None, log=None,
             clock_period_ns=(10, "ns"))
```

- `dut`: Device under test
- `title`: Component title (for logging)
- `clock`: Clock signal
- `reset_n`: Reset signal (active low)
- `req_signal`: Request input signal (bus)
- `gnt_valid_signal`: Grant valid output signal
- `gnt_signal`: Grant output signal (bus)
- `gnt_id_signal`: Grant ID output signal
- `gnt_ack_signal`: Optional grant acknowledge input signal (bus)
- `block_arb_signal`: Optional signal to block arbitration
- `max_thresh_signal`: Optional maximum threshold signal for weighted arbiters
- `is_weighted`: Boolean indicating if this is a weighted arbiter
- `clients`: Number of clients (derived from signal width if None)
- `log`: Logger instance (creates new if None)
- `clock_period_ns`: Clock period as tuple (value, unit)

#### Key Methods

- `add_transaction_callback(callback)`: Register a callback for completed transactions
- `add_reset_callback(callback)`: Register a callback for reset events
- `get_transaction_count()`: Return the total number of observed transactions
- `get_client_stats(client_id)`: Get statistics for a specific client
- `get_fairness_index()`: Calculate Jain's fairness index for the arbiter

### RoundRobinArbiterMonitor

A specialized monitor for round-robin arbiters with enhanced tracking features.

#### Additional Methods

- `get_priority_changes()`: Get statistics about priority changes in the arbiter

### WeightedRoundRobinArbiterMonitor

A specialized monitor for weighted round-robin arbiters.

#### Additional Methods

- `get_inferred_weights()`: Get the inferred weights for each client
- `get_weight_distribution()`: Get statistics about the weight distribution

## Example Usage

```python
# Create a standard round-robin arbiter monitor
rr_monitor = RoundRobinArbiterMonitor(
    dut=dut,
    title="RR_Arbiter",
    clock=dut.clk,
    reset_n=dut.rst_n,
    req_signal=dut.req,
    gnt_valid_signal=dut.gnt_valid,
    gnt_signal=dut.gnt,
    gnt_id_signal=dut.gnt_id,
    clients=4
)

# Add a callback for completed transactions
def transaction_callback(transaction):
    print(f"Transaction granted to client {transaction.gnt_id}")

rr_monitor.add_transaction_callback(transaction_callback)

# Create a weighted round-robin arbiter monitor
wrr_monitor = WeightedRoundRobinArbiterMonitor(
    dut=dut,
    title="WRR_Arbiter",
    clock=dut.clk,
    reset_n=dut.rst_n,
    req_signal=dut.req,
    gnt_valid_signal=dut.gnt_valid,
    gnt_signal=dut.gnt,
    gnt_id_signal=dut.gnt_id,
    max_thresh_signal=dut.max_thresh,
    clients=4
)

# Check fairness after some transactions
fairness = wrr_monitor.get_fairness_index()
print(f"Arbiter fairness index: {fairness}")

# Get inferred weights
weights = wrr_monitor.get_inferred_weights()
print(f"Inferred client weights: {weights}")
```

## See Also

- [Field Configuration](field_config.md) - For defining packet field configurations
- [Constrained Random](constrained_random.md) - For generating constrained random values

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
