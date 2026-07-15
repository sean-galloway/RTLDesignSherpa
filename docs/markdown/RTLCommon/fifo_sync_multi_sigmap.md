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

# Multi-Field Synchronous FIFO (Signal-Map Variant)

**Module:** `fifo_sync_multi_sigmap.sv`
**Location:** `rtl/common/`
**Status:** Production Ready

## Overview

`fifo_sync_multi_sigmap` is a variant of [`fifo_sync_multi`](fifo_sync_multi.md) that carries the same four-field payload through one [`fifo_sync`](fifo_sync.md) instance, but exposes the fields under **generic, position-oriented signal names** (`siga`, `sigb`, `sigc`, `sigd` in, `sige`, `sigf`, `sigg`, `sigh` out) instead of role-specific names like `addr` / `ctrl` / `data`. This makes it a convenient building block when the fields do not have fixed semantic roles, or when a generator maps an array of arbitrary signals onto FIFO slots by position.

As with the base wrapper, all storage, pointers, and status-flag generation come from the single underlying `fifo_sync`; this module only supplies the field-packing wiring.

### Key Features

- **Generic field names:** Four write fields `wr_siga`..`wr_sigd` and four read fields `rd_sige`..`rd_sigh`
- **Single storage instance:** All fields packed into one `fifo_sync` payload of `AW + CW + DW + DW` bits
- **Inherited status flags:** `wr_full`, `wr_almost_full`, `rd_empty`, `rd_almost_empty` from `fifo_sync`
- **Mux / flop output modes:** `REGISTERED` selects combinational (mux) or registered (flop) read output
- **Any depth:** Depth passed through to `fifo_sync`

## Module Purpose

This module serves the same buffering role as `fifo_sync_multi`, but its port names are deliberately semantic-free so it can be dropped in wherever a bundle of same-shaped fields is mapped by position rather than by meaning. It is especially handy for generated or templated instantiations that assign an ordered list of signals to FIFO slots.

**Use Cases:**

- Buffering a bundle of positionally-mapped fields whose roles are assigned by the caller
- Generated / templated wiring that connects an ordered signal list to FIFO slots
- A neutral-named alternative to `fifo_sync_multi` when `addr` / `ctrl` / `data` labels do not fit

**Key Benefit:** Provides the same single-`fifo_sync` field bundling as `fifo_sync_multi` while keeping port names generic, so callers assign meaning by position.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `REGISTERED` | int | 0 | Read output mode: `0` = mux mode (combinational), `1` = flop mode (registered) |
| `ADDR_WIDTH` | int | 4 | Width of the first field (`wr_siga` / `rd_sige`) |
| `CTRL_WIDTH` | int | 4 | Width of the second field (`wr_sigb` / `rd_sigf`) |
| `DATA_WIDTH` | int | 4 | Width of each of the two data-sized fields (`sigc/sigd`, `sigg/sigh`) |
| `DEPTH` | int | 4 | FIFO depth in entries |
| `ALMOST_WR_MARGIN` | int | 1 | Almost-full threshold, passed to `fifo_sync` |
| `ALMOST_RD_MARGIN` | int | 1 | Almost-empty threshold, passed to `fifo_sync` |
| `AW` | int | `ADDR_WIDTH` | Derived alias for `ADDR_WIDTH` (do not override) |
| `CW` | int | `CTRL_WIDTH` | Derived alias for `CTRL_WIDTH` (do not override) |
| `DW` | int | `DATA_WIDTH` | Derived alias for `DATA_WIDTH` (do not override) |
| `D` | int | `DEPTH` | Derived alias for `DEPTH` (do not override) |

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | System clock |
| `rst_n` | Input | 1 | Active-low reset |

### Write Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `write` | Input | 1 | Write enable |
| `wr_siga` | Input | AW | First field to enqueue |
| `wr_sigb` | Input | CW | Second field to enqueue |
| `wr_sigc` | Input | DW | Third (data-sized) field to enqueue |
| `wr_sigd` | Input | DW | Fourth (data-sized) field to enqueue |
| `wr_full` | Output | 1 | Full flag |
| `wr_almost_full` | Output | 1 | Almost-full flag |

### Read Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `read` | Input | 1 | Read enable |
| `rd_sige` | Output | AW | Dequeued first field (maps from `wr_siga`) |
| `rd_sigf` | Output | CW | Dequeued second field (maps from `wr_sigb`) |
| `rd_sigg` | Output | DW | Dequeued third field (maps from `wr_sigc`) |
| `rd_sigh` | Output | DW | Dequeued fourth field (maps from `wr_sigd`) |
| `rd_empty` | Output | 1 | Empty flag |
| `rd_almost_empty` | Output | 1 | Almost-empty flag |

## Functional Description

### Field Packing

The four write fields are concatenated into the single `fifo_sync` payload with `wr_siga` in the most significant bits, then `wr_sigb`, then `wr_sigd`, then `wr_sigc` in the least significant bits:

```systemverilog
.wr_data ({wr_siga, wr_sigb, wr_sigd, wr_sigc})
```

The payload width is `AW + CW + DW + DW`.

### Field Unpacking

The read side splits the payload back out using the matching order, so each field re-emerges on its own output. `sigc`/`sigd` map to `sigg`/`sigh` respectively:

```systemverilog
.rd_data ({rd_sige, rd_sigf, rd_sigh, rd_sigg})
```

The packing order pairs the two data-sized fields identically on both sides (`sigd`/`sigc` in, `sigh`/`sigg` out), preserving the positional mapping through the FIFO.

### Storage and Flow Control

As with `fifo_sync_multi`, all pointer management, memory, and full/almost-full/empty/almost-empty flag generation is provided by the single `fifo_sync` instance. See [`fifo_sync`](fifo_sync.md) for the underlying storage and the mux-vs-flop read-timing behavior selected by `REGISTERED`.

## Usage Example

```systemverilog
fifo_sync_multi_sigmap #(
    .REGISTERED (1),     // 1 = registered (flop) read output
    .ADDR_WIDTH (10),
    .CTRL_WIDTH (2),
    .DATA_WIDTH (16),
    .DEPTH      (8)
) u_sigmap_fifo (
    .clk             (clk),
    .rst_n           (rst_n),
    // write side (positional fields)
    .write           (wr_en),
    .wr_siga         (field_a),
    .wr_sigb         (field_b),
    .wr_sigc         (field_c),
    .wr_sigd         (field_d),
    .wr_full         (fifo_full),
    .wr_almost_full  (fifo_afull),
    // read side (positional fields)
    .read            (rd_en),
    .rd_sige         (out_a),
    .rd_sigf         (out_b),
    .rd_sigg         (out_c),
    .rd_sigh         (out_d),
    .rd_empty        (fifo_empty),
    .rd_almost_empty (fifo_aempty)
);
```

## Design Notes

- **Naming is the only difference.** Structurally this is identical to `fifo_sync_multi`; only the port names change from role-based (`addr`/`ctrl`/`data`) to positional (`siga`..`sigh`).
- **Positional mapping.** `siga -> sige`, `sigb -> sigf`, `sigc -> sigg`, `sigd -> sigh`. The two data-sized fields keep their pairing because the write and read concatenations use the same order.
- **Pure wiring wrapper.** No storage or control logic lives here; all timing, flags, and depth behavior come from `fifo_sync`.

## Related Modules

### Used By

- Generated or templated instantiations that map an ordered signal list onto FIFO slots

### Uses

- [fifo_sync](fifo_sync.md) - The underlying single-payload synchronous FIFO providing storage and flow control

### See Also

- [fifo_sync_multi](fifo_sync_multi.md) - The role-named (`addr` / `ctrl` / `data0` / `data1`) equivalent
- [fifo_control](fifo_control.md) - Shared full/empty flag generation used by `fifo_sync`
- [fifo_async](fifo_async.md) - Clock-domain-crossing FIFO variant

## References

### Source Code

- `rtl/common/testcode/fifo_sync_multi_sigmap.sv`
- `rtl/common/fifo_sync.sv` (instantiated submodule)

### Documentation

- `rtl/common/PRD.md`

**Last Updated:** 2026-07-15

## Navigation

- [Back to RTLCommon Index](index.md)
