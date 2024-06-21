# cache_plru_mesi

## Overview

The `cache_plru_mesi` module implements a cache controller with the following features:

- **Parameters**: Configurable depth, associativity, data width, address width, and line size.
- **PLRU Replacement Policy**: Implements the Pseudo-Least Recently Used (PLRU) replacement policy.
- **MESI Protocol**: Supports MESI cache coherence protocol with states Modified, Exclusive, Shared, and Invalid.
- **Interface**: Supports SYSBUS and memory interfaces, including snoop requests and cache-to-cache data transfers.

Note: this code is still simplified, but is nearing the complexity seen in an actual implementation.

## Parameters

- `DEPTH` (default: 64): Total number of cache lines.
- `A` (default: 4): Associativity (number of ways).
- `DW` (default: 32): Data width in bits.
- `AW` (default: 32): Address width in bits.
- `DM` (default: DW/8): Number of byte enables.
- `LINE_SIZE` (default: DW/8): Line size in bytes.

## Interfaces

### Inputs

- **Clock and Reset**:
  - `i_clk`: System clock.
  - `i_rst_n`: System reset (active-low).

- **Sysbus Input**:
  - `i_sysbusin_valid`: Valid signal for sysbus input.
  - `i_sysbusin_op_rdxwr`: Read/Write operation for sysbus input.
  - `i_sysbusin_addr`: Address for sysbus input.
  - `i_sysbusin_data`: Data for sysbus input.
  - `i_sysbusin_dm`: Data mask for sysbus input.

- **Sysbus Output**:
  - `i_sysbusout_ready`: Ready signal for sysbus output.

- **Memory Input**:
  - `i_memin_valid`: Valid signal for memory input.
  - `i_memin_op_rdxwr`: Read/Write operation for memory input.
  - `i_memin_addr`: Address for memory input.
  - `i_memin_data`: Data for memory input.
  - `i_memin_dm`: Data mask for memory input.

- **Memory Output**:
  - `i_memout_ready`: Ready signal for memory output.

- **Snoop Port**:
  - `i_snoop_valid`: Valid snoop request.
  - `i_snoop_addr`: Snooped address.
  - `i_snoop_cmd`: Snoop command (read, write, invalidate).

- **Cache-to-Cache Snoop Transfer**:
  - `i_c2c_snp_ready`: Cache-to-cache transfer ready signal.

### Outputs

- **Sysbus Input**:
  - `o_sysbusin_ready`: Ready signal for sysbus input.
  - `o_sysbusin_hit`: Hit signal for sysbus input.

- **Sysbus Output**:
  - `o_sysbusout_valid`: Valid signal for sysbus output.
  - `o_sysbusout_op_rdxwr`: Operation for sysbus output.
  - `o_sysbusout_addr`: Address for sysbus output.
  - `o_sysbusout_data`: Data for sysbus output.
  - `o_sysbusout_dm`: Data mask for sysbus output.

- **Memory Input**:
  - `o_memin_ready`: Ready signal for memory input.

- **Memory Output**:
  - `o_memout_valid`: Valid signal for memory output.
  - `o_memout_op_rdxwr`: Operation for memory output.
  - `o_memout_addr`: Address for memory output.
  - `o_memout_data`: Data for memory output.
  - `o_memout_dm`: Data mask for memory output.

- **Snoop Port**:
  - `o_snoop_ready`: Ready signal for snoop.
  - `o_snoop_hit`: Hit/miss signal for snoop.
  - `o_snoop_dirty`: Dirty data signal for snoop.
  - `o_snoop_data`: Data for snoop.

- **Cache-to-Cache Snoop Transfer**:
  - `o_c2c_snp_valid`: Cache-to-cache transfer valid signal.
  - `o_c2c_snp_addr`: Cache-to-cache transfer address.
  - `o_c2c_snp_data`: Cache-to-cache transfer data.
  - `o_c2c_snp_dm`: Cache-to-cache transfer data mask.

## Key Functional Blocks

### PLRU Replacement

- `get_plru_way`: Function to get the PLRU way.
- `update_plru`: Function to update the PLRU bits.

### Cache Arrays
- `r_tag_array`: Array holding cache tags.
- `r_data_array`: Array holding cache data.
- `r_dm_array`: Array holding data masks.
- `r_valid_array`: Array indicating valid cache lines.
- `r_dirty_array`: Array indicating dirty cache lines.
- `r_plru_bits`: Array holding PLRU bits.
- `r_state_array`: Array holding MESI states.

### FIFO Instantiation

- Implementations for FIFO operations in FIFO stages (sysbus input/output, memory input/output, snoop, and cache-to-cache snoop).

### State Machine Implementation

- Handles operations such as read requests, write requests, memory input (read response), and snoop requests.

## Usage

### Initialization

- The module initializes various cache structures (tag, data, validity, dirty bits, PLRU bits, cache line states) on reset.

### Read Requests

- Checks for read hits and misses.
- On a hit, returns the data.
- On a miss, issues a read to memory.

### Write Requests

- Checks for write hits and misses.
- On a hit, updates the data.
- On a miss, checks for dirty entries to evict, updates the data, and issues a write to memory if required.

### Snoop Operations

- Handles snoop requests (read, read-for-ownership, invalidate).
- Updates the cache line states based on the snoop command.

### Cache-to-Cache Transfers

- Initiates cache-to-cache data transfers for coherent operations between caches.

### MESI Protocol

- Follows the MESI protocol to maintain cache coherence across multiple processors.

## Example

To use this module in a SystemVerilog project, instantiate it with appropriate parameters for depth, associativity, data width, address width, and line size. Ensure that clock, reset, data, address, and control signals are correctly mapped to corresponding ports.

---

By providing this summary, you can get a basic understanding of the functionality, operations, and usage of the `cache_plru_mesi` module. For further usage, implement custom logic and integrate with other system components as needed.

---

[Return to Index](index.md)

---
