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

# gaxi_skid_buffer_dbldrn

**Module:** `gaxi_skid_buffer_dbldrn.sv`
**Location:** `rtl/amba/gaxi/`
**Status:** Production Ready

---

## Overview

`gaxi_skid_buffer_dbldrn` is the double-drain variant of the [`gaxi_skid_buffer`](gaxi_skid_buffer.md). The elastic write side and the single-read output are unchanged; what's new is a **second read output** (`rd_data2`) and a **second drain request** (`rd_ready2`), so the consumer can pop **two entries in one clock** when at least two are buffered. That matters for consumers that can retire two items per cycle — a 2-wide unpack, a burst aligner — and would otherwise be throughput-limited by a one-per-cycle drain.

Like the base skid buffer, storage is a shift register of `DEPTH` entries and the read/write handshakes use the GAXI valid/ready convention. The base buffer drains at most one entry per cycle, which caps a fast consumer at one item per clock; this variant lets the consumer drain the lowest and next-lowest entries together, doubling drain throughput while still honoring GAXI backpressure and preserving in-order (lowest-position-first) delivery.

### Key Features

- **Double-drain:** Assert `rd_ready2` (legal only when `rd_count >= 2`) to pop two entries in a single cycle
- **Two read data outputs:** `rd_data` (lowest entry) and `rd_data2` (next entry) presented simultaneously
- **Single-drain compatible:** With `rd_ready2` low it behaves as an ordinary single-drain skid buffer
- **Priority-encoded update:** Write / single-read / double-read combinations handled by a one-hot case, double-drain prioritized over single-drain
- **Backpressure-aware ready/valid:** `wr_ready` and `rd_valid` account for both drain widths
- **Legality assertion:** Simulation `$error` fires if `rd_ready2` is asserted with fewer than two entries buffered

**Use Cases:**

- Feeding a consumer that retires two entries per clock (2-wide unpack, dual-issue, burst aligner)
- Draining a buffer faster than one-per-cycle to relieve upstream backpressure
- Any place a `gaxi_skid_buffer` is used but the sink can opportunistically take a pair

**Key Benefit:** Doubles peak drain throughput (two entries per clock) when two or more are buffered, while degrading gracefully to ordinary single-drain skid-buffer behavior when only one entry is available.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `DATA_WIDTH` | int | 32 | Data bus width in bits |
| `DEPTH` | int | 4 | Buffer depth in entries (must be 2..8 inclusive (any integer)) |
| `DW` | int | `DATA_WIDTH` | Derived alias for `DATA_WIDTH` (do not override) |
| `BUF_WIDTH` | int | `DATA_WIDTH * DEPTH` | Derived total shift-register width (do not override) |
| `BW` | int | `BUF_WIDTH` | Derived alias for `BUF_WIDTH` (do not override) |

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | Clock |
| `axi_aresetn` | input | 1 | Active-low asynchronous reset |

### Write Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `wr_valid` | input | 1 | Write data valid |
| `wr_ready` | output | 1 | Ready to accept a write (registered) |
| `wr_data` | input | DATA_WIDTH | Write data |

### Read Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `rd_valid` | output | 1 | Read data valid (registered) |
| `rd_ready` | input | 1 | Consumer ready to accept a read |
| `rd_ready2` | input | 1 | Double-drain request; legal only when `rd_count >= 2` |
| `rd_data` | output | DATA_WIDTH | First (lowest-position) entry |
| `rd_data2` | output | DATA_WIDTH | Second (next-position) entry, valid when double-draining |

### Status

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `count` | output | 4 | Current buffer occupancy |
| `rd_count` | output | 4 | Same as `count` (read-side occupancy) |

---

## Functional Description

### Transfer Detection

Three transfer conditions are decoded combinationally. A single read is only recognized when `rd_ready2` is **not** asserted, and a double read additionally requires two entries present:

```systemverilog
assign w_wr_xfer     = wr_valid & wr_ready;
assign w_rd_xfer     = rd_valid & rd_ready & ~rd_ready2;                     // single drain
assign w_rd_dbl_xfer = rd_valid & rd_ready & rd_ready2 & (r_data_count >= 2);// double drain
```

### Storage Update

The shift register `r_data` and occupancy `r_data_count` are updated from a one-hot case over `{w_wr_xfer, w_rd_dbl_xfer, w_rd_xfer}`, with double-drain prioritized above single-drain:

| Case | Meaning | `r_data` action | count change |
|------|---------|-----------------|--------------|
| `3'b100` | Write only | Load `wr_data` at the top of the occupied region | +1 |
| `3'b001` | Single read only | Shift down by one entry | −1 |
| `3'b010` | Double read only | Shift down by two entries | −2 |
| `3'b101` | Write + single read | Shift down one, then insert `wr_data` at the new top | 0 |
| `3'b110` | Write + double read | Shift down two, then insert `wr_data` at the new top | −1 |
| default | Idle / illegal (`000`, `011`, `111`) | No change | 0 |

The `011` and `111` combinations are illegal (a single- and double-drain cannot both fire) and fall through to the no-change default. Reads always drain from the low positions (`rd_data` = entry 0, `rd_data2` = entry 1), preserving in-order delivery.

### Ready/Valid Logic

`wr_ready` and `rd_valid` are registered and computed one cycle ahead, accounting for both drain widths so that space freed by a double-drain is reflected in `wr_ready`:

```systemverilog
wr_ready <= (r_data_count <= DEPTH-2) ||
            (r_data_count == DEPTH-1 && (~w_wr_xfer || w_rd_xfer || w_rd_dbl_xfer)) ||
            (r_data_count == DEPTH   && (w_rd_xfer || w_rd_dbl_xfer));

rd_valid <= (r_data_count >= 3) ||
            (r_data_count == 2 && (~w_rd_dbl_xfer || w_wr_xfer)) ||
            (r_data_count == 1 && (~w_rd_xfer || w_wr_xfer)) ||
            (r_data_count == 0 && w_wr_xfer);
```

The `count == 2` term is the one the double drain makes load-bearing: the
base buffer's plain `count >= 2` is safe only for single drain (which always
leaves at least one entry), but a double drain from exactly two leaves ZERO.
The unfixed equation held `rd_valid` high for one cycle on the empty buffer,
and a streaming consumer holding `rd_ready` through that cycle accepted a
phantom entry -- underflowing the count to 15 and wedging the module until
reset. The double-drain-to-empty scenario in the TB is the regression for
exactly this corner.

### Output Assignments

The two lowest shift-register slots are presented on the two data outputs, and the occupancy drives both status ports:

```systemverilog
assign rd_data  = r_data[DW-1:0];      // first item (lowest position)
assign rd_data2 = r_data[2*DW-1:DW];   // second item (next position)
assign rd_count = r_data_count;
assign count    = r_data_count;
```

### Legality Assertion

A simulation-only check enforces the double-drain contract: asserting `rd_ready2` (with `rd_ready`) when fewer than two entries are buffered raises a `$error`. This catches consumers that request a double-drain the buffer cannot service.

---

## Usage Examples

```systemverilog
// Skid buffer feeding a consumer that can retire two entries per clock.
gaxi_skid_buffer_dbldrn #(
    .DATA_WIDTH(32),
    .DEPTH(4)
) u_dbldrn (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),
    // write side
    .wr_valid    (src_valid),
    .wr_ready    (src_ready),
    .wr_data     (src_data),
    // read side
    .rd_valid    (dst_valid),
    .rd_ready    (dst_ready),
    .rd_ready2   (dst_take_two & (rd_occupancy >= 2)),  // only when >= 2 buffered
    .rd_data     (dst_data0),
    .rd_data2    (dst_data1),
    // status
    .count       (rd_occupancy),
    .rd_count    ()
);
```

---

## Design Notes

- **`rd_ready2` legality.** Only assert `rd_ready2` (together with `rd_ready`) when `rd_count >= 2`. The RTL guards the transfer with the same condition, and the simulation assertion flags misuse.
- **Priority.** When both a single- and double-drain could be decoded, double-drain wins; the illegal simultaneous cases (`011`, `111`) are ignored by the default branch.
- **In-order delivery.** Entry 0 is always the oldest; `rd_data`/`rd_data2` expose the two oldest entries, and drains shift the register down, so ordering is preserved.
- **Graceful degradation.** With `rd_ready2` tied low the module is functionally an ordinary single-drain skid buffer.
- **Reset macros.** The module uses the project `reset_defs.svh` `ALWAYS_FF_RST` / `RST_ASSERTED` macros for its registered state.

---

## Related Modules

- [gaxi_skid_buffer](gaxi_skid_buffer.md) - The single-drain base skid buffer this variant extends
- [gaxi_skid_buffer_struct](gaxi_skid_buffer_struct.md) - Struct-typed skid buffer variant
- [gaxi_fifo_sync](gaxi_fifo_sync.md) - Larger-depth synchronous FIFO with optional registered output

Self-contained: no RTL dependencies beyond the `reset_defs.svh` reset macros. Typical integrators are consumers that retire two GAXI entries per clock (2-wide unpack / aligner front-ends).

---

## References

- **Source:** `rtl/amba/gaxi/gaxi_skid_buffer_dbldrn.sv`
- **Base variant:** `rtl/amba/gaxi/gaxi_skid_buffer.sv`
- **Documentation:** `docs/markdown/rtl-amba/index.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- **[← Back to GAXI Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
