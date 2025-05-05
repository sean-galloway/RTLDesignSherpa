# BaseScoreboard Class Documentation

## Overview

The `BaseScoreboard` class serves as the foundation for all protocol-specific scoreboards in the verification framework. It provides essential functionality for comparing expected versus actual transactions and tracking mismatches.

## Key Features

- Transaction queue management for expected and actual transactions
- Comparison infrastructure with customizable comparison logic
- Error tracking and reporting
- Protocol transformation for cross-protocol verification
- Result calculation and reporting

## Class Definition

```python
class BaseScoreboard:
    """Base class for all protocol scoreboards"""

    def __init__(self, name, log=None):
        self.name = name
        self.log = log
        self.expected_queue = deque()
        self.actual_queue = deque()
        self.error_count = 0
        self.transaction_count = 0
        self.mismatched = []
        self.transformer = None
```

## Core Methods

### Transaction Management

```python
def add_expected(self, transaction):
    """Add transaction to expected queue"""
```
Adds a transaction to the expected transaction queue. If a transformer is set, the transaction is first transformed.

```python
def add_actual(self, transaction):
    """Add transaction to actual queue and trigger comparison"""
```
Adds a transaction to the actual transaction queue and triggers comparison with the next expected transaction.

### Comparison Logic

```python
def _compare_next(self):
    """Compare next transaction in queues if available"""
```
Compares the next available transactions from both queues if available.

```python
def _compare_transactions(self, expected, actual):
    """Compare two transactions - override in derived classes"""
```
Abstract method that must be implemented by derived classes to provide protocol-specific comparison logic.

```python
def _log_mismatch(self, expected, actual):
    """Log detailed information about mismatched transactions"""
```
Logs detailed information about mismatches, can be overridden by derived classes for protocol-specific details.

### Reporting and Results

```python
def report(self):
    """Generate report of scoreboard activity"""
```
Generates a report of scoreboard activity including statistics on transactions and errors.

```python
def result(self):
    """Calculate the result as a ratio of successful transactions."""
```
Calculates the pass rate from 0.0 to 1.0 based on successful vs. failed transactions.

```python
def clear(self):
    """Clear all queues and reset counters"""
```
Clears all transaction queues and resets counters for reuse.

## Protocol Transformer

The `BaseScoreboard` includes support for protocol transformation via the `ProtocolTransformer` class:

```python
class ProtocolTransformer:
    """
    Base class for protocol transformers.
    Protocol transformers convert transactions from one protocol to another,
    allowing for cross-protocol comparison in scoreboards.
    """
```

### Transformer Methods

```python
def transform(self, transaction):
    """Transform a transaction from source to target protocol."""
```
Abstract method to transform a transaction from the source protocol to the target protocol.

```python
def try_transform(self, transaction):
    """Attempt to transform a transaction with error handling."""
```
Wrapper method that provides error handling for transformations.

```python
def report(self):
    """Generate a report of transformer statistics."""
```
Generates a report of transformer statistics including successful and failed transformations.

## Usage Example

Basic usage pattern for a derived scoreboard:

```python
class MyProtocolScoreboard(BaseScoreboard):
    def __init__(self, name, log=None):
        super().__init__(name, log)
        # Protocol-specific initialization
        
    def _compare_transactions(self, expected, actual):
        # Protocol-specific comparison logic
        if not isinstance(expected, MyProtocolPacket) or not isinstance(actual, MyProtocolPacket):
            return False
            
        # Compare relevant fields
        return expected.addr == actual.addr and expected.data == actual.data
        
    def _log_mismatch(self, expected, actual):
        # Enhanced protocol-specific mismatch logging
        self.log.error(f"{self.name} - Mismatch:")
        self.log.error(f"  Expected addr: 0x{expected.addr:X}, data: 0x{expected.data:X}")
        self.log.error(f"  Actual addr: 0x{actual.addr:X}, data: 0x{actual.data:X}")
```

## Best Practices

1. Always override `_compare_transactions()` in derived classes
2. Enhance `_log_mismatch()` with protocol-specific details
3. Use `result()` to get a normalized pass/fail ratio
4. Use `report()` for detailed error information
5. Use transformers when comparing transactions across different protocols
6. Clear the scoreboard between test phases with `clear()`

## Navigation

[↑ Scoreboards Index](index.md) | [↑ CocoTBFramework Index](../index.md)
