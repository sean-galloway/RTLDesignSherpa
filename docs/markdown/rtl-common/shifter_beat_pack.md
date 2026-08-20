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

# Beat-Packing Shifter Module

**Module:** `shifter_beat_pack.sv`
**Location:** `rtl/common/`
**Status:** Production Ready

## Purpose

`shifter_beat_pack` is a bit-granular packing/aligning shifter. It accepts fixed-width `CHUNK_BITS` entries on a push handshake, accumulates them in a multi-chunk staging register, and drains **configurable-width "beats"** out the low end on a pop handshake. The beat width is a runtime input (bytes minus one), so the same instance can emit different beat sizes across bursts.

All of the shift/load/mux logic lives inside this one module so that callers — an aligner that needs to repack DFI cycles into DRAM beats, say — don't have to invent their own shift-and-compensate scheme. Push and pop can occur in the same cycle; the next-state logic applies the pop first and the push second, and a single non-blocking assignment commits the result, so no internal last-assignment race is possible.

This module exists for a problem that shows up constantly: repacking a stream of one fixed width into beats of another (often runtime-selected) width. Data arrives one whole chunk at a time and leaves as beats whose width is chosen at run time; the module holds the partial-beat residue between cycles and shifts it down as beats drain, so the caller sees clean valid/ready handshakes on both sides.

**Use Cases:**

- Packing DFI cycles into DRAM beats in a memory-controller aligner
- Width adaptation where ingress chunk width and egress beat width differ and the beat width is runtime-configurable
- Any packer that must hold partial-beat residue while new fixed-width data lands

**Key Benefit:** Centralizes the shift, load, and residue-compensation logic behind two simple handshakes, so callers get runtime-variable beat repacking without hand-rolling their own barrel shifter.

## Key Features

- **Bit-granular staging:** A `DEPTH_CHUNKS × CHUNK_BITS` register packs chunks and drains beats at bit resolution
- **Runtime beat width:** `cfg_beat_bytes_m1` selects the beat size (bytes − 1) per burst without re-elaboration
- **Independent ingress / egress sizing:** Chunk width and beat cap are separate parameters
- **Same-cycle push + pop:** Pop-then-push ordering with one NBA eliminates internal races
- **Elaboration-time contract checks:** `$error` guards enforce `DEPTH_CHUNKS >= 2` and `MAX_BEAT_BITS < STORAGE_BITS`
- **Status outputs:** `empty` and `count_bits_o` expose occupancy to the wrapper

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CHUNK_BITS` | int | 128 | Width of one push entry (ingress granularity) |
| `MAX_BEAT_BYTES` | int | 16 | Maximum beat width in bytes; caps what reaches `pop_data` |
| `CFG_BITS` | int | 8 | Width of the runtime `cfg_beat_bytes_m1` field. 8 bits gives beat_bytes ∈ 1..256; 4 bits gives 1..16, etc. |
| `DEPTH_CHUNKS` | int | 2 | Staging-register depth in chunks. Default 2 = "current + prefetched-next". Must be `>= 2`. Larger depths absorb more before draining but widen the pop-side barrel shifter (timing cost). |
| `MAX_BEAT_BITS` | int | `MAX_BEAT_BYTES * 8` | Derived (do not override): maximum beat width in bits |
| `STORAGE_BITS` | int | `DEPTH_CHUNKS * CHUNK_BITS` | Derived (do not override): total staging-register width |
| `COUNT_BITS` | int | `$clog2(STORAGE_BITS + 1)` | Derived (do not override): width of the bit-occupancy counter |
| `IDX_BITS` | int | `$clog2(STORAGE_BITS)` | Derived (do not override): index width for `r_data` part-selects |

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | Clock |
| `rst_n` | Input | 1 | Active-low reset (via `reset_defs.svh` macros) |

### Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_beat_bytes_m1` | Input | CFG_BITS | Beat width in bytes − 1 (0 → 1 byte). Held stable per burst. |

### Push Interface (ingress)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `push_valid` | Input | 1 | New chunk valid |
| `push_ready` | Output | 1 | Room for another whole chunk (post-push count `<= STORAGE_BITS`) |
| `push_data` | Input | CHUNK_BITS | The chunk to pack |

### Pop Interface (egress)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `pop_valid` | Output | 1 | At least one whole beat is available |
| `pop_ready` | Input | 1 | Consumer accepts a beat |
| `pop_data` | Output | MAX_BEAT_BITS | Low `MAX_BEAT_BITS` of the staging register; consumer reads only the low `(cfg_beat_bytes_m1+1)*8` bits |

### Status

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `empty` | Output | 1 | Staging register holds no bits (`r_count == 0`) |
| `count_bits_o` | Output | COUNT_BITS | Current occupancy in bits |

## Functional Description

### Runtime Beat Width

The runtime beat width in bits comes from the byte-minus-one config field, widened by 4 bits so the counter math can represent the largest beat any `CFG_BITS`-wide value can encode:

```systemverilog
localparam int BEAT_BITS_W = CFG_BITS + 4;
assign w_beat_bits = ({..., cfg_beat_bytes_m1} + 1) << 3;   // (bytes_m1 + 1) * 8
```

`MAX_BEAT_BYTES` caps what actually appears on `pop_data`; `w_beat_bits` is used only for the occupancy accounting.

### Handshake and Status

The combinational handshakes are driven directly from the bit-occupancy counter `r_count`:

- `empty` = (`r_count == 0`)
- `push_ready` = there is room for another whole chunk, i.e. `r_count <= STORAGE_BITS - CHUNK_BITS`
- `pop_valid` = the register holds at least one whole beat, i.e. `r_count >= w_beat_bits` and non-zero
- `pop_data` = the low `MAX_BEAT_BITS` of `r_data` (a plain slice, well-defined because a beat is always strictly narrower than the staging window)

When the configured beat is narrower than `MAX_BEAT_BITS`, the upper bits of `pop_data` are stale bytes belonging to the next beat. That's fine — the consumer already knows the width from `cfg` and reads only the low valid bits.

### Next-State: Pop First, Push Second

Each cycle the combinational block computes next-state `w_v_data` / `w_v_count` in two ordered steps:

1. **Pop** (when `pop_valid && pop_ready`): shift the register down by `w_beat_bits` and subtract that many bits from the count, draining the low beat.
2. **Push** (when `push_valid && push_ready`): land the new chunk at `[w_v_count +: CHUNK_BITS]` using the *post-pop* occupancy, so the chunk sits right above the still-valid bits whether or not a pop fired, then add `CHUNK_BITS` to the count.

```systemverilog
if (pop_valid && pop_ready) begin
    w_v_data  = w_v_data >> w_beat_bits;
    w_v_count = w_v_count - COUNT_BITS'(w_beat_bits);
end
if (push_valid && push_ready) begin
    w_v_data[w_v_count[IDX_BITS-1:0] +: CHUNK_BITS] = push_data;
    w_v_count = w_v_count + COUNT_BITS'(CHUNK_BITS);
end
```

One non-blocking assignment then writes `r_data` / `r_count` from `w_v_data` / `w_v_count`, so same-cycle push + pop has no internal last-assignment race.

### Elaboration-Time Contract

Two `$error` guards enforce the sizing rules that keep forward progress guaranteed:

- `DEPTH_CHUNKS >= 2`: a single-chunk register cannot hold partial-beat residue while a new chunk lands.
- `MAX_BEAT_BITS < STORAGE_BITS`: a beat must be strictly narrower than the staging window.

### Sizing Guidance

Pick `CHUNK_BITS` and `MAX_BEAT_BYTES` so any runtime beat width fits in the `2N` (or deeper) storage, i.e. `cfg_beat_bytes × 8 <= DEPTH_CHUNKS × CHUNK_BITS`. Ingress chunk width and egress beat cap are independent, so callers can right-size both.

## Design Notes

- **Bit occupancy, not entry count.** `r_count` tracks bits, not entries, because chunks land whole but beats drain at a runtime-variable bit width.
- **Pop-then-push ordering is deliberate.** Draining first frees the low bits so the incoming chunk lands at the correct post-pop position, which is what makes same-cycle push + pop safe.
- **`pop_data` upper bits may be stale.** Only the low `(cfg_beat_bytes_m1+1)*8` bits are meaningful; the consumer must mask to the configured width.
- **Depth vs. timing.** Increasing `DEPTH_CHUNKS` lets the packer absorb more data before draining but widens the pop-side barrel shifter, degrading timing.
- **Reset macros.** The module uses the project `reset_defs.svh` `ALWAYS_FF_RST` / `RST_ASSERTED` macros for the registered state.

## Usage Example

```systemverilog
// Repack 128-bit DFI cycles into runtime-sized DRAM beats (up to 16 bytes).
shifter_beat_pack #(
    .CHUNK_BITS     (128),
    .MAX_BEAT_BYTES (16),
    .CFG_BITS       (8),
    .DEPTH_CHUNKS   (2)
) u_beat_pack (
    .clk               (clk),
    .rst_n             (rst_n),
    .cfg_beat_bytes_m1 (beat_bytes - 8'd1),   // e.g. 8 bytes -> 7

    // ingress: one 128-bit chunk per handshake
    .push_valid        (dfi_valid),
    .push_ready        (dfi_ready),
    .push_data         (dfi_cycle),

    // egress: one beat per handshake
    .pop_valid         (beat_valid),
    .pop_ready         (beat_ready),
    .pop_data          (beat_data),           // read low (beat_bytes*8) bits

    // status
    .empty             (pack_empty),
    .count_bits_o      (pack_bits)
);
```

## Related Modules

### Used By

- Memory-controller aligners that repack DFI cycles into DRAM beats

### Uses

- None (self-contained; relies only on the `reset_defs.svh` reset macros)

### See Also

- [fifo_sync](fifo_sync.md) - Whole-entry synchronous FIFO (contrast: this module repacks at bit granularity)

## References

### Source Code

- `rtl/common/shifter_beat_pack.sv`

### Documentation

- `docs/markdown/rtl-common/index.md`

**Last Updated:** 2026-07-15

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
