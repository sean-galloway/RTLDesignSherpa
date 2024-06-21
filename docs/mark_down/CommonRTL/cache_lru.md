# cache_lru

The `cache_lru` module is designed to implement a set-associative cache with Least Recently Used (LRU) replacement policy. Below is a detailed description of its functionality, operations, and usage. Note: this is an overly simplified implementation to get a feel for the issues.

## Overview

This module is parameterized and can be configured for different cache sizes, associativity, data widths, and address widths. It supports basic read and write operations, as well as complex snoop commands used in multi-core or multi-processor systems to maintain cache coherence. The logic implements True LRU; this is not the ideal in most cases from a gate or timing perspective.

### Parameters

- **DEPTH**: Total number of cache lines.
- **A**: Associativity (number of ways).
- **DW**: Data width in bits.
- **AW**: Address width in bits.
- **LINE_SIZE**: Line size in bytes.
- **LRU_WIDTH**: Width of LRU counter (usually log2 of `A`).

### I/O Ports

#### Inputs

1. **i_clk**: Clock signal.
2. **i_rst_n**: Reset signal (active low).
3. **i_rd_addr**: Read address.
4. **i_rd**: Read request signal.
5. **i_wr_addr**: Write address.
6. **i_wr**: Write request signal.
7. **i_wr_data**: Write data.
8. **i_wr_dm**: Write data mask (byte enables).
9. **i_snoop_addr**: Address for snoop operations.
10. **i_snoop_valid**: Snoop request signal.
11. **i_snoop_cmd**: Snoop command (e.g., read, write, invalidate).

#### Outputs

1. **o_rd_data**: Data read from the cache.
2. **o_rd_hit**: Read hit/miss status.
3. **o_wr_hit**: Write hit/miss status.
4. **o_snoop_hit**: Snoop hit/miss status.
5. **o_snoop_dirty**: Indicates if the snooped data is dirty.
6. **o_snoop_data**: Data retrieved during snoop operation.

## Functionality

### Cache Structure

- **Tag Array**: Stores the tag portion of addresses.
- **Data Array**: Stores actual data.
- **Valid Array**: Indicates whether the cache line is valid.
- **Dirty Array**: Indicates whether the cache line is dirty.
- **LRU Bits**: Store information for LRU replacement policy.

### Address Decomposition

Addresses are decomposed into:

- **Tag**: Upper part of the address used to identify the correct cache line.
- **Index**: Middle part used to identify the set in the cache.
- **Offset**: Lower part used to identify the byte within the cache line.

### Operations

#### Read Operation

1. **Address Decomposition**: Breaks the read address into tag, index, and offset.
2. **Cache Lookup**: Checks if the tag exists in the specified index.
3. **LRU Update**: Updates the LRU bits on a hit.
4. **Data Output**: Outputs the data if it is a hit, otherwise indicates a miss.

#### Write Operation

1. **Address Decomposition**: Breaks the write address into tag, index, and offset.
2. **Cache Lookup**: Checks if the tag exists in the specified index.
3. **Data Update**: Updates data and marks the line as dirty on a hit.
4. **LRU Update**: Updates the LRU bits accordingly.
5. **Allocation on Miss**: Allocates an empty way or replaces the least recently used way on a miss.

#### Snoop Operations

1. **Snoop Read**: Checks if the snoop address exists in the cache and retrieves data if present.
2. **Read for Ownership (RFO)**: Similar to snoop read but also invalidates the cache line.
3. **Invalidate**: Invalidates the cache line if present.
4. **Write Back (WB)**: Handles write-back operations.
5. **Intervention**: Provides requested data directly to the requesting cache.

### LRU Management

LRU counters are updated to keep track of the least recently used cache lines. On each cache access (read/write/snoop), the LRU bits are adjusted accordingly to ensure the LRU policy is maintained.

### Initialization

Initializes the cache by clearing valid, dirty arrays, and setting all LRU bits to zero on reset.

## Usage

This module can be instantiated in a larger SystemVerilog project, particularly in systems requiring cache memory with sophisticated replacement policies. Users can configure the cache by setting the appropriate parameters and providing the necessary inputs for read, write, and snoop operations.

---

[Return to Index](index.md)

---
