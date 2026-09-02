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

# AXI Burst Address Generator

**Module:** `axi_gen_addr.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AXI burst address generator calculates the next address for AXI burst transactions, supporting FIXED, INCR, and WRAP burst types. It handles data width conversions and provides both next-address and aligned-address outputs for boundary-aware transaction processing.

### Key Features

- Support for all AXI burst types (FIXED, INCR, WRAP)
- Data width conversion handling (DW != ODW)
- Next address calculation with proper increment
- Aligned address generation for boundary checking
- Pure combinational logic for zero-latency operation

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AW | int | 32 | Address bus width |
| DW | int | 32 | Input data width (internal) |
| ODW | int | 32 | Output data width (external bus) |
| LEN | int | 8 | Burst length field width |

---

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| curr_addr | input | AW | Current address |
| size | input | 3 | AXI size encoding (2^size bytes per beat) |
| burst | input | 2 | AXI burst type (00=FIXED, 01=INCR, 10=WRAP) |
| len | input | LEN | AXI burst length (beats - 1) |
| next_addr | output | AW | Next transaction address |
| next_addr_align | output | AW | Next address aligned to ODW |

---

## Functional Description

### Increment Calculation

The address increment comes from the size field:
```systemverilog
increment_pre = (1 << size)  // 2^size bytes per beat
```

When the data widths differ (DW != ODW), the increment is clamped:
```systemverilog
if (increment_pre > ODWBYTES)
    increment = ODWBYTES;
```

### Burst Type Handling

**FIXED burst (burst = 2'b00)**:
- Address stays constant for all beats
- `next_addr = curr_addr`

**INCR burst (burst = 2'b01)**:
- Address increments by size each beat
- `next_addr = curr_addr + increment`

**WRAP burst (burst = 2'b10)**:
- Address wraps at the burst boundary
- Wrap mask = (1 << (size + log2(len+1))) - 1
- Aligned address = (curr_addr + increment) & ~(increment - 1)
- Wrap address = (curr_addr & ~wrap_mask) | (aligned_addr & wrap_mask)

### Aligned Address Output

The aligned output aligns the next address to the output data width:
```systemverilog
alignment_mask = ODWBYTES - 1
next_addr_align = next_addr & ~alignment_mask
```

That's what the boundary-crossing detection in the transaction splitters consumes.

---

## Timing Characteristics

This module is **purely combinational** -- it contains no `always_ff` and no
latch, so it holds no state and adds no clock cycles. Its outputs settle a
propagation delay after its inputs, and it introduces no latency into a
pipeline that instantiates it.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
```systemverilog
// Generate next address for AXI4 64-bit bus
axi_gen_addr #(
    .AW   (32),
    .DW   (64),   // Internal 64-bit
    .ODW  (64),   // External 64-bit
    .LEN  (8)
) u_addr_gen (
    .curr_addr       (32'h1000),
    .size            (3'b011),    // 8 bytes per beat
    .burst           (2'b01),     // INCR
    .len             (8'd3),      // 4 beats total
    .next_addr       (addr_next),
    .next_addr_align (addr_aligned)
);

// addr_next = 0x1000 + 8 = 0x1008
// addr_aligned = 0x1008 (already aligned to 8-byte boundary)
```

---

## Design Notes

### Data Width Conversion

When DW != ODW, the module handles the mismatch:
- If increment > output bus bytes, clamp to the output bus width
- This prevents address increments larger than the physical bus

### WRAP Burst Alignment

WRAP bursts need careful address math:
- The wrap boundary is determined by size and length
- The wrapped address stays within the wrap region
- Example: 4-beat wrap (len=3), 8 bytes/beat, at 0x0FF8: wrap_mask = (1<<(3+2))-1 = 0x1F, aligned next = 0x1000, so next_addr = (0x0FF8 & ~0x1F) | (0x1000 & 0x1F) = **0x0FE0** — the address wraps to the start of the 32-byte-aligned region, not past 0x1000

### Pure Combinational

The module is purely combinational, for zero latency:
- No clock, no reset
- Instant address generation
- Drop it into address calculation pipelines

---

## Related Modules

### Used By
- sdpram_core.sv (both BRAM address trackers)
- axi4_to_apb4_convert.sv (APB beat addressing)
- (The splitters do NOT use this module — their boundary math is inline in axi_split_combi)

### See Also
- axi_split_combi.sv (uses aligned addresses for split decisions)

---

## Testing

Covered from `val/amba/` with the rest of the shared area — run everything with `make -C val/amba clean-all && make -C val/amba run-all-func-parallel`.

---

## References

### Specifications
- ARM IHI 0022E: AMBA AXI4 Protocol Specification (Section A3.4 - Address Structure)
- Internal: docs/markdown/rtl-amba/index.md

### Source Code
- RTL: `rtl/amba/shared/axi_gen_addr.sv`

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
