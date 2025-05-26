# Scoreboards

## Overview

The Scoreboards module provides the verification components responsible for checking the correctness of transactions in various protocols. These components track and compare expected versus actual transactions, report mismatches, and provide comprehensive statistics on test execution.

For a comprehensive introduction to the scoreboard architecture and functionality, see the [Overview](overview.md) document.

## Key Features

- Base scoreboard architecture with common functionality
- Protocol-specific scoreboards for APB, AXI4, FIFO, and GAXI
- Cross-protocol verification with transformer support
- Detailed mismatch reporting and statistics
- Memory model integration
- Support for out-of-order and parallel transactions
- Configurable comparison modes and filtering

## Components

- [Base Scoreboard](base_scoreboard.md) - Foundation class for all scoreboards
- [APB Scoreboard](apb_scoreboard.md) - Verification for APB transactions
- [AXI4 Scoreboard](axi4_scoreboard.md) - Verification for AXI4 transactions
- [FIFO Scoreboard](fifo_scoreboard.md) - Verification for FIFO transactions
- [GAXI Scoreboard](gaxi_scoreboard.md) - Verification for GAXI transactions
- [APB-GAXI Scoreboard](apb_gaxi_scoreboard.md) - Cross-protocol verification

## Transformers

- [APB-GAXI Transformer](transformers/apb_gaxi_transformer.md) - Converts APB transactions to GAXI format

## Documentation

- [Overview](overview.md) - Introduction to scoreboard architecture and usage
- [Implementation Details](scoreboards-details.md) - Detailed implementation guidance for each scoreboard file

## Common Usage Patterns

### Basic Verification Flow

1. Create a scoreboard for the appropriate protocol
2. Add expected transactions from reference models
3. Add actual transactions from DUT monitors
4. Check for mismatches and review statistics
5. Generate verification reports

### Cross-Protocol Verification

1. Create source and target protocol scoreboards
2. Configure the appropriate transformer
3. Add transactions in the source protocol format
4. Automatically verify against the target protocol

### Memory Model Integration

1. Create a memory-based scoreboard
2. Configure the memory model
3. Add write transactions
4. Verify read transactions against memory contents

## See Also

- [Memory Model](../components/memory_model.md) - Used for data storage and comparison
- [APB Components](../components/apb/index.md) - APB protocol implementation
- [AXI4 Components](../components/axi4/index.md) - AXI4 protocol implementation
- [FIFO Components](../components/fifo/index.md) - FIFO protocol implementation
- [GAXI Components](../components/gaxi/index.md) - GAXI protocol implementation

## Navigation

[↑ CocoTBFramework Index](../index.md)
