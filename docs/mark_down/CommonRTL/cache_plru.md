# cache_plru SystemVerilog Module

The `cache_plru` module is a parametrizable cache controller implemented using SystemVerilog. It manages cache line operations, such as read and write requests, using a Pseudo Least Recently Used (PLRU) replacement policy. This document provides a summary of its functionality, operations, and usage. Note: this is slightly more complex than the cache_lru; it also correctly implements the PLRU policy.

## Parameters

- **DEPTH**: The total number of cache lines.
- **A**: The associativity, or number of cache ways (set associativity).
- **DW**: Data width in bits.
- **AW**: Address width in bits.
- **LINE_SIZE**: Line size in bytes (calculated as `DW/8`).

## Ports

### Inputs

- **i_clk**: Clock signal.
- **i_rst_n**: Asynchronous reset (active low).
- **i_rd_addr**: Address for read requests.
- **i_rd**: Read request signal.
- **i_wr_addr**: Address for write requests.
- **i_wr**: Write request signal.
- **i_wr_data**: Data to be written.
- **i_wr_dm**: Write data mask (byte enables).
- **i_snoop_addr**: Address for snoop requests.
- **i_snoop_valid**: Valid snoop request signal.
- **i_snoop_cmd**: Snoop command (e.g., read, write, invalidate).

### Outputs

- **o_rd_data**: Data read from the cache.
- **o_rd_hit**: Read hit or miss indicator.
- **o_wr_hit**: Write hit or miss indicator.
- **o_snoop_hit**: Snoop hit or miss indicator.
- **o_snoop_dirty**: Indicates if snooped data is dirty.
- **o_snoop_data**: Data for snoop operations.

## Functionality and Operations

### Initialization and Reset

- On reset (`i_rst_n`), cache state arrays, such as `r_valid_array` and `r_dirty_array`, are initialized to zeros. PLRU bits are also reset.

### Address Decoding

- The module decodes address parts (tag, index, and offset) for read and write operations.
- Tag, index, and offset are derived from the input addresses (`i_rd_addr` and `i_wr_addr`).

### Cache Operations

#### Read Operations

- Check if the read address hits on any of the ways.
- If hit, the requested data is read from the appropriate cache line.
- If miss, determine a victim way using the PLRU policy, fetch the data, and update the cache.

#### Write Operations

- Check if the write address hits on any of the ways.
- If hit, update the data in the appropriate cache line and set the dirty bit.
- If miss, determine a victim way using the PLRU policy, write the new data, and update the cache accordingly.

### Snoop Operations

- Handles various snoop commands, such as:
  - **Snoop read**: Searches the cache for the snooped address; if found, returns the data and notifies if the data is dirty.
  - **Snoop read for ownership (RFO)**: Similar to snoop read but also invalidates the cache line if found.
  - **Snoop invalidate**: Invalidates the cache line corresponding to the snooped address if found.

### PLRU (Pseudo Least Recently Used) Policy

- Updates the PLRU bits upon any cache hit/miss to ensure that the least recently used way is selected as the victim way for replacement.

## Usage

The module can be instantiated with desired cache parameters to manage a set of cache lines. It can handle multiple read, write, and snoop operations, making it suitable for use in CPU caches and similar memory management systems. Signals related to snooping allow integration with external coherence protocols and other memory management units.

---

[Return to Index](index.md)

---
