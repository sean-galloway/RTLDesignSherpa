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

# Multi-Field Synchronous FIFO

**Module:** `fifo_sync_multi.sv`
**Location:** `rtl/integ_common/`
**Status:** Integration example -- not a rtl/common library module

> This module lives in `rtl/integ_common/`, alongside `rtl/integ_amba`'s
> examples. It wires rtl/common blocks together to demonstrate a pattern
> rather than being a library primitive itself. It has a filelist
> (`rtl/integ_common/filelists/fifo_sync_multi.f`), tests in `val/integ_common/`, and a
> formal harness under `formal/integ_common/fifo_sync_multi/`.

## Overview

`fifo_sync_multi` is a thin convenience wrapper around [`fifo_sync`](../rtl-common/fifo_sync.md) for callers who'd rather push and pop several **named fields** through one synchronous FIFO than hand-pack them into a single wide bus. On the write side it concatenates an address field, a control field, and two data words into one `fifo_sync` payload; on the read side it splits that payload back out into the same named fields.

All the real work—storage, pointer management, full/empty/almost flag generation—comes from the underlying `fifo_sync` instance. This wrapper contributes only the field-packing wiring.

### Key Features

- **Field-oriented interface:** Separate `wr_addr` / `wr_ctrl` / `wr_data0` / `wr_data1` write ports and matching read ports
- **Single storage instance:** All fields ride one `fifo_sync` with a combined `AW + CW + DW + DW` payload
- **Inherited status flags:** `wr_full`, `wr_almost_full`, `rd_empty`, `rd_almost_empty` come straight from `fifo_sync`
- **Mux / flop output modes:** `REGISTERED` selects combinational (mux) or registered (flop) read output
- **Any depth:** Depth is passed through to `fifo_sync`

## Module Purpose

Datapaths move little bundles of related fields around all the time (an address plus a control tag plus a pair of data beats, for example). You *could* make every caller concatenate and slice those fields by hand around a plain `fifo_sync`, but why would you? This wrapper exposes the fields as individual ports and does the packing internally, so call sites stay readable and consistent.

**Use Cases:**

- Buffering an {address, control, data0, data1} bundle between two pipeline stages
- Queuing descriptor-like records where fields have distinct widths
- Any place a plain `fifo_sync` would be used but the payload is naturally several fields

**Key Benefit:** Callers work with named fields of distinct widths while still using a single, well-tested `fifo_sync` for all storage and flow control.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `REGISTERED` | int | 0 | Read output mode: `0` = mux mode (combinational), `1` = flop mode (registered) |
| `ADDR_WIDTH` | int | 4 | Width of the address field (`wr_addr` / `rd_addr`) |
| `CTRL_WIDTH` | int | 4 | Width of the control field (`wr_ctrl` / `rd_ctrl`) |
| `DATA_WIDTH` | int | 4 | Width of each data word (`wr_data0/1`, `rd_data0/1`) |
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
| `wr_addr` | Input | AW | Address field to enqueue |
| `wr_ctrl` | Input | CW | Control field to enqueue |
| `wr_data0` | Input | DW | Data word 0 to enqueue |
| `wr_data1` | Input | DW | Data word 1 to enqueue |
| `wr_full` | Output | 1 | Full flag |
| `wr_almost_full` | Output | 1 | Almost-full flag |

### Read Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `read` | Input | 1 | Read enable |
| `rd_addr` | Output | AW | Dequeued address field |
| `rd_ctrl` | Output | CW | Dequeued control field |
| `rd_data0` | Output | DW | Dequeued data word 0 |
| `rd_data1` | Output | DW | Dequeued data word 1 |
| `rd_empty` | Output | 1 | Empty flag |
| `rd_almost_empty` | Output | 1 | Almost-empty flag |

## Functional Description

### Field Packing

On the write side, the four fields get concatenated into the single `fifo_sync` payload. Order matters: `wr_addr` takes the most significant bits, then `wr_ctrl`, then `wr_data1`, with `wr_data0` in the least significant bits:

```systemverilog
.wr_data ({wr_addr, wr_ctrl, wr_data1, wr_data0})
```

So the `fifo_sync` payload width works out to `AW + CW + DW + DW`.

### Field Unpacking

The read side uses that same concatenation order to split the payload back into named outputs, so each field pops back out on its own port:

```systemverilog
.rd_data ({rd_addr, rd_ctrl, rd_data1, rd_data0})
```

### Storage and Flow Control

Everything else—binary read/write pointers, the memory array, and full/almost-full/empty/almost-empty flag generation—is delegated to the single `fifo_sync` instance. See [`fifo_sync`](../rtl-common/fifo_sync.md) for the pointer, memory, and flag details, including the mux-vs-flop read timing controlled by `REGISTERED`.

## Usage Example

```systemverilog
fifo_sync_multi #(
    .REGISTERED (0),     // 0 = mux (combinational read), 1 = flop (registered)
    .ADDR_WIDTH (8),
    .CTRL_WIDTH (4),
    .DATA_WIDTH (32),
    .DEPTH      (16)
) u_bundle_fifo (
    .clk             (clk),
    .rst_n           (rst_n),
    // write side
    .write           (wr_en),
    .wr_addr         (req_addr),
    .wr_ctrl         (req_tag),
    .wr_data0        (req_data_lo),
    .wr_data1        (req_data_hi),
    .wr_full         (fifo_full),
    .wr_almost_full  (fifo_afull),
    // read side
    .read            (rd_en),
    .rd_addr         (out_addr),
    .rd_ctrl         (out_tag),
    .rd_data0        (out_data_lo),
    .rd_data1        (out_data_hi),
    .rd_empty        (fifo_empty),
    .rd_almost_empty (fifo_aempty)
);
```

## Design Notes

- **Pure wiring wrapper.** The module contains no storage or control logic of its own; it only concatenates and slices fields around one `fifo_sync`. All timing, flag, and depth behavior is that of `fifo_sync`.
- **Concatenation order matters.** Write and read use the same `{addr, ctrl, data1, data0}` order, so the fields map back correctly. Do not reorder one side without the other.
- **Two data words.** The wrapper is fixed at exactly two data words (`data0`, `data1`) plus an address and control field. For a different bundle shape, see the signal-map variant below or use `fifo_sync` directly.
- **REGISTERED read latency.** As with `fifo_sync`, mux mode gives 0-cycle combinational read and flop mode gives 1-cycle registered read.

## Related Modules

### Used By

- Pipeline stages that buffer an {address, control, data0, data1} bundle

### Uses

- [fifo_sync](../rtl-common/fifo_sync.md) - The underlying single-payload synchronous FIFO providing storage and flow control

### See Also

- [fifo_sync_multi_sigmap](fifo_sync_multi_sigmap.md) - Same structure with a generic signal-map naming style (`siga`..`sigh`)
- [fifo_control](../rtl-common/fifo_control.md) - Shared full/empty flag generation used by `fifo_sync`
- [fifo_async](../rtl-cdc/fifo_async.md) - Clock-domain-crossing FIFO variant

## References

### Source Code

- `rtl/integ_common/fifo_sync_multi.sv`
- `rtl/common/fifo_sync.sv` (instantiated submodule)

### Documentation

- `docs/markdown/rtl-common/index.md`

**Last Updated:** 2026-07-26

## Navigation

- [Back to rtl-integ-common Index](index.md)
