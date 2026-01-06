<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# AXI Split Combinational Logic

**Module:** `axi_split_combi.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AXI Split Combinational Logic module provides pure combinational boundary crossing detection and split length calculation for AXI transactions. It serves as the core computational engine for both read and write transaction splitters, enabling real-time decision-making without state machine overhead.

### Key Features

- Pure combinational logic (zero latency)
- Boundary crossing detection for arbitrary alignment boundaries
- Automatic split length calculation (AXI encoding)
- Optimized for synthesis (bit shifts instead of division)
- Comprehensive assertion-based validation
- Configurable address and data widths
- No address wraparound assumption (simplified logic)

---

## Module Purpose

AXI transaction splitting requires complex address arithmetic to determine:
1. Does this transaction cross a boundary?
2. How many beats fit before the boundary?
3. What address/length for the next split?

This module encapsulates all splitting calculations into reusable combinational logic, ensuring consistent behavior across read and write splitters.

**Design Philosophy:**
- Separation of concerns: Calculation logic separate from state management
- Reusability: Single module used by both read and write splitters
- Performance: Combinational path enables single-cycle decisions
- Correctness: Extensive assertions validate assumptions

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AW | int | 32 | Address width in bits (typically 32 or 64) |
| DW | int | 32 | Data width in bits, must be power of 2 (32, 64, 128, 256, 512, 1024) |

**Derived Constants (localparam):**

| Constant | Calculation | Description |
|----------|-------------|-------------|
| BYTES_PER_BEAT | DW / 8 | Bytes transferred per beat (e.g., 8 for 64-bit bus) |
| LOG2_BYTES_PER_BEAT | $clog2(BYTES_PER_BEAT) | Bit shift amount for beat calculations |
| EXPECTED_AX_SIZE | LOG2_BYTES_PER_BEAT | Expected value of ax_size input (for assertions) |
| ADDR_ALIGN_MASK | BYTES_PER_BEAT - 1 | Mask for address alignment checking |

---

## Port Groups

### Clock and Reset (For Assertions Only)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Clock for assertion evaluation (not used in functional logic) |
| aresetn | input | 1 | Active-low reset for assertion gating (not used in functional logic) |

### Input Signals

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| current_addr | input | AW | Current transaction starting address (may be mid-split) |
| current_len | input | 8 | Current transaction length in AXI encoding (beats - 1) |
| ax_size | input | 3 | AXI size field (log2 of bytes per beat) |
| alignment_mask | input | 12 | 12-bit boundary alignment mask (e.g., 0xFFF for 4KB) |
| is_idle_state | input | 1 | Indicates whether state machine is in IDLE (first transaction) |
| transaction_valid | input | 1 | Valid transaction present on inputs |

### Output Signals

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| split_required | output | 1 | Transaction crosses boundary and requires splitting |
| split_len | output | 8 | Length of current split in AXI encoding (beats - 1) |
| next_boundary_addr | output | AW | Address at next boundary alignment |
| remaining_len_after_split | output | 8 | Remaining length after current split (AXI encoding) |
| new_split_needed | output | 1 | Helper signal: split_required AND is_idle_state AND transaction_valid |

---

## Functional Description

### Boundary Crossing Detection Algorithm

The module implements a simplified boundary detection algorithm based on key AXI assumptions:

**Step 1: Calculate Transaction Parameters**
```
total_bytes = (current_len + 1) << ax_size
transaction_end_addr = current_addr + total_bytes - 1
```

**Step 2: Calculate Next Boundary**
```
next_boundary_addr = (current_addr | alignment_mask) + 1
```

Example (4KB boundary, ADDR=0x0FC0, mask=0xFFF):
```
current_addr      = 0x0FC0
alignment_mask    = 0x0FFF
OR result         = 0x0FFF
next_boundary     = 0x0FFF + 1 = 0x1000
```

**Step 3: Calculate Space to Boundary**
```
bytes_to_boundary = next_boundary_addr - current_addr
beats_to_boundary = bytes_to_boundary >> ax_size
```

Example (continuing above, ax_size=3 for 8-byte beats):
```
bytes_to_boundary = 0x1000 - 0x0FC0 = 64 bytes
beats_to_boundary = 64 >> 3 = 8 beats
```

**Step 4: Determine Split Requirement**

Transaction requires splitting if:
1. It ends at or past the next boundary (crosses_boundary)
2. There is space for at least one beat before boundary (has_beats_before_boundary)
3. The beats to boundary fit within total transaction (beats_fit_before_boundary)

```
crosses_boundary = (transaction_end_addr >= next_boundary_addr)
has_beats_before_boundary = (beats_to_boundary > 0)
beats_fit_before_boundary = (beats_to_boundary <= (current_len + 1))

split_required = crosses_boundary AND has_beats_before_boundary
                 AND beats_fit_before_boundary
```

### Split Length Calculation

If splitting is required, the split length represents how many beats to consume before the boundary:

```
split_len = split_required ? (beats_to_boundary - 1) : current_len
```

**AXI Encoding:** Length is always encoded as (beats - 1):
- 1 beat → LEN=0
- 2 beats → LEN=1
- 8 beats → LEN=7

### Remaining Length Calculation

After consuming the current split, calculate remaining beats:

```
original_beats_total = current_len + 1
split_beats_actual = split_required ? beats_to_boundary : original_beats_total
remaining_beats_actual = split_required ? (original_beats_total - split_beats_actual) : 0

// Convert back to AXI encoding
remaining_len_after_split = split_required ?
                            ((remaining_beats_actual > 0) ? (remaining_beats_actual - 1) : 0)
                            : 0
```

### State Machine Helper

The `new_split_needed` output simplifies state machine control:

```
new_split_needed = split_required AND is_idle_state AND transaction_valid
```

This signal indicates a new split sequence is starting (as opposed to continuing an existing split).

---

## Design Assumptions

The module enforces several critical assumptions to enable simplified, high-performance logic:

### Assumption 1: Address Alignment

**Assumption:** All AXI addresses are aligned to the data bus width.

**Implication:**
- If DATA_WIDTH = 512 bits (64 bytes), address is always 64-byte aligned
- Low-order address bits are always zero

**Verification:**
```systemverilog
assert ((current_addr & ADDR_ALIGN_MASK) == '0)
```

### Assumption 2: Fixed Transfer Size

**Assumption:** All AXI transfers use maximum transfer size equal to bus width.

**Implication:**
- ax_size always matches log2(DATA_WIDTH/8)
- Example: 64-bit bus → ax_size = 3'b011 (8 bytes)

**Verification:**
```systemverilog
assert (ax_size == EXPECTED_AX_SIZE)
```

### Assumption 3: Incrementing Bursts Only

**Assumption:** All bursts use incrementing address mode (AxBURST = 2'b01).

**Implication:**
- No FIXED or WRAP burst handling
- Address calculation simplified

**Rationale:**
- Covers 95%+ of real-world use cases
- FIXED bursts rarely cross boundaries
- WRAP bursts require complex modulo arithmetic

### Assumption 4: No Address Wraparound

**Assumption:** Transactions never wrap around top of address space (0xFFFFFFFF → 0x00000000).

**Implication:**
- No wraparound detection or handling
- Simplified comparison logic

**Verification:**
```systemverilog
assert (transaction_end_addr >= current_addr) // No overflow
assert (next_boundary_addr > current_addr)    // Boundary doesn't wrap
```

**Rationale:**
- Top of address space typically reserved for device registers
- Memory allocators avoid near-boundary allocations
- Real systems never allow this condition

---

## Usage Example

### Integration with Read Splitter

```systemverilog
// Instantiate split logic within read splitter
axi_split_combi #(
    .AW             (32),
    .DW             (64)
) u_split_logic (
    // Clock/reset for assertions only
    .aclk                       (aclk),
    .aresetn                    (aresetn),

    // Transaction parameters
    .current_addr               (w_current_addr),        // From state machine
    .current_len                (w_current_len),         // From state machine
    .ax_size                    (w_current_size),        // ARSIZE
    .alignment_mask             (12'hFFF),               // 4KB boundary
    .is_idle_state              (r_state == IDLE),
    .transaction_valid          (fub_arvalid),

    // Splitting decision outputs
    .split_required             (w_split_required),
    .split_len                  (w_split_len),
    .next_boundary_addr         (w_next_boundary_addr),
    .remaining_len_after_split  (w_remaining_len_after_split),
    .new_split_needed           (w_new_split_needed)
);

// Use outputs in state machine
always_comb begin
    case (r_state)
        IDLE: begin
            if (fub_arvalid && m_axi_arready) begin
                if (w_new_split_needed) begin
                    // Split required - start sequence
                    next_state = SPLITTING;
                    // Buffer next split parameters
                    buffer_addr = w_next_boundary_addr;
                    buffer_len = w_remaining_len_after_split;
                end else begin
                    // No split - pass through
                    next_state = IDLE;
                end
            end
        end

        SPLITTING: begin
            if (m_axi_arvalid && m_axi_arready) begin
                if (w_split_required) begin
                    // More splits needed
                    buffer_addr = w_next_boundary_addr;
                    buffer_len = w_remaining_len_after_split;
                end else begin
                    // Final split complete
                    next_state = IDLE;
                end
            end
        end
    endcase
end

// Use split_len for address channel
assign m_axi_araddr = w_current_addr;
assign m_axi_arlen = w_split_required ? w_split_len : w_current_len;
```

### Example Calculation Walkthrough

**Scenario:** 4KB boundary, 64-bit data bus

**Inputs:**
- current_addr = 0x0FC0
- current_len = 7 (8 beats in AXI encoding)
- ax_size = 3 (8 bytes per beat)
- alignment_mask = 0xFFF

**Calculations:**

**Step 1: Transaction parameters**
```
total_bytes = (7 + 1) << 3 = 8 << 3 = 64 bytes
transaction_end_addr = 0x0FC0 + 64 - 1 = 0x0FFF
```

**Step 2: Next boundary**
```
next_boundary_addr = (0x0FC0 | 0x0FFF) + 1
                   = 0x0FFF + 1
                   = 0x1000
```

**Step 3: Space to boundary**
```
bytes_to_boundary = 0x1000 - 0x0FC0 = 64 bytes
beats_to_boundary = 64 >> 3 = 8 beats
```

**Step 4: Split decision**
```
crosses_boundary = (0x0FFF >= 0x1000) = False
split_required = False
```

**Outputs:**
- split_required = 0 (transaction ends exactly at boundary, no split)
- split_len = 7 (pass through original length)
- remaining_len_after_split = 0

**Modified Scenario: Transaction crosses boundary**

**Inputs:**
- current_addr = 0x0FC0
- current_len = 8 (9 beats)
- ax_size = 3
- alignment_mask = 0xFFF

**Calculations:**

**Step 1: Transaction parameters**
```
total_bytes = (8 + 1) << 3 = 72 bytes
transaction_end_addr = 0x0FC0 + 72 - 1 = 0x1007
```

**Step 4: Split decision**
```
crosses_boundary = (0x1007 >= 0x1000) = True
has_beats_before_boundary = (8 > 0) = True
beats_fit_before_boundary = (8 <= 9) = True
split_required = True
```

**Outputs:**
- split_required = 1
- split_len = 7 (8 beats - 1 in AXI encoding)
- next_boundary_addr = 0x1000
- remaining_len_after_split = 0 (1 beat - 1 in AXI encoding)

---

## Design Notes

### Synthesis Optimization

**Bit Shifts Instead of Division:**
```
// Original (expensive):
beats_to_boundary = bytes_to_boundary / (1 << ax_size)

// Optimized (single barrel shifter):
beats_to_boundary = bytes_to_boundary >> ax_size
```

**Fixed Alignment Assumptions:**
- Removes modulo arithmetic
- Enables simple OR-based boundary calculation
- Critical for timing closure in high-speed designs

### Assertion Coverage

The module includes comprehensive assertions for validation:

**Input Validation (Triggered on transaction_valid && is_idle_state):**
- Address alignment to data width
- ax_size matches expected value for data width
- No address wraparound in transaction
- No boundary calculation wraparound

**Output Validation (Triggered on transaction_valid):**
- Beats to boundary within reasonable range
- Split length conservation (split_beats + remaining_beats = original_beats)
- Boundary alignment verification
- Comparison logic consistency

### Timing Considerations

**Critical Path:**
1. Address OR with alignment_mask (next_boundary_addr)
2. Subtraction (bytes_to_boundary)
3. Variable barrel shift by ax_size (beats_to_boundary)
4. Comparison and output muxing (split_required, split_len)

**Optimization Strategies:**
- Pipeline if timing closure issues (adds 1 cycle latency)
- Use registered alignment_mask if it's static
- Consider ax_size as constant parameter if fixed data width

### Debug Support

**DEBUG_AXI_SPLIT Macro:**

Enable detailed transaction logging:
```systemverilog
`define DEBUG_AXI_SPLIT

// Generates console output:
=== AXI SPLIT DEBUG (NO WRAPAROUND) ===
current_addr = 0x00000FC0
current_len = 7 (total beats = 8)
ax_size = 3 (bytes_per_beat = 8)
alignment_mask = 0xFFF
transaction_end_addr = 0x00000FFF
next_boundary_addr = 0x00001000
bytes_to_boundary = 64
beats_to_boundary = 8
crosses_boundary = 0
split_required = 0
split_len = 7 (split beats = 8)
remaining_len_after_split = 0 (remaining beats = 0)
=======================================
```

---

## Related Modules

### Used By
- **axi_master_rd_splitter.sv** - Read transaction splitting (AR channel)
- **axi_master_wr_splitter.sv** - Write transaction splitting (AW channel)

### Dependencies
- None (pure combinational logic)

### See Also
- **axi_master_rd_splitter.sv** - Full read splitter with state machine
- **axi_master_wr_splitter.sv** - Full write splitter with response consolidation

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi_split_combi.sv`
- Tests: Indirectly tested via splitter tests (`test_axi_master_rd_splitter.py`, `test_axi_master_wr_splitter.py`)

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- AXI Specification: AMBA AXI4 Protocol Specification (ARM IHI 0022E)
- Design Guide: `rtl/amba/PRD.md`

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
