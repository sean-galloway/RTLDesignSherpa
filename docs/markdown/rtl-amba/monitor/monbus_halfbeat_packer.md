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

# monbus_halfbeat_packer

**Module:** `monbus_halfbeat_packer.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The `monbus_halfbeat_packer` module packs two 30-bit half-slots into a single 64-bit beat, sitting downstream of `monbus_compressor`. The compressor emits one 64-bit beat per tier-1 record — a 66.7% reduction ceiling, 1 beat per 3-beat raw record. Pair two compatible records into one beat and this packer pushes the reduction to as much as 83.3% (0.5 beat per record). It is bit-exact to the Python golden model `Encoder(half_beat=True)`.

### Key Features

- Pairs two 30-bit half-slots into one `TAG_HALF_PAIR` (0x4) beat
- Buffers one half-slot until a partner arrives
- Preserves record order: flushes a buffered half before forwarding a non-half beat
- Flushes a lone trailing half when the input goes idle (last record never stranded)
- Forwards full 64-bit slots and raw-escape beats verbatim
- Bit-exact to the compressor Python golden model for gap-free record streams
- Simple valid/ready handshake on both ports

Trace-capture bandwidth is precious. The compressor already reduces most records to a single 64-bit beat, but records that also fit in 30 bits can be paired two-to-a-beat. This packer performs that pairing with a one-slot holding buffer, emitting a combined beat when a second eligible half arrives while preserving strict record order for everything that cannot be paired.

**Use Cases:**
- Maximizing trace history stored in a fixed capture buffer
- Reducing MonBus write bandwidth to memory in compressed-capture builds
- Matching the software decoder's half-beat encoding exactly (cosim parity)

**Key Benefit:** Breaks the compressor's 1-beat-per-record floor without changing record semantics — pairing is opportunistic and always order-preserving, so it is never wrong, only occasionally less-packed under input bubbles.

---

## Parameters

This module has no parameters.

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | input | 1 | Clock |
| `rst_n` | input | 1 | Active-low asynchronous reset |

### Input — Beats from the Compressor

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `in_valid` | input | 1 | Input beat valid |
| `in_ready` | output | 1 | Packer ready to accept the input beat |
| `in_slot` | input | 64 | Full 64-bit slot (tier-1 slot or one of a raw record's 3 beats) |
| `in_half_valid` | input | 1 | Set when `in_slot`'s record also fits a 30-bit half-slot |
| `in_half_slot` | input | 30 | The 30-bit half-slot for the current record |

### Output — Packed Beats to the Write FIFO

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `out_valid` | output | 1 | Output beat valid |
| `out_ready` | input | 1 | Downstream ready |
| `out_slot` | output | 64 | Packed beat (paired half-slots, forwarded full slot, or half + NOP flush) |

---

## Functional Description

### Beat Layout

The paired beat matches `monbus_compressor.py`:

```
TAG_HALF_PAIR beat = {tag[63:60]=0x4, slotA[59:30], slotB[29:0]}
half-slot          = {sub[29:28], idx[27:23], delta_ts[22:13], data[12:0]}
NOP slot           = 30'd0   (sub == HSUB_NOP)
```

### Case Decode

Five mutually-considered cases drive the packer combinationally, based on `in_valid`, `in_half_valid`, and whether a half is buffered (`r_pend_valid`):

| Signal | Condition | Action |
|--------|-----------|--------|
| `pair_now` | half arrives, one already buffered | Emit the pair `{TAG, pend, in_half}`, consume input on accept |
| `buffer_now` | half arrives, none buffered | Latch it, emit nothing, always consume input |
| `fwd_now` | non-half, none buffered | Forward `in_slot` verbatim, consume input on accept |
| `flush_fwd` | non-half, one buffered | Emit the lone buffered half (paired with NOP) first, **hold** the input |
| `idle_flush` | input idle, one buffered | Emit the lone trailing half (paired with NOP) |

`out_valid` asserts for any of `pair_now`, `fwd_now`, `flush_fwd`, or `idle_flush`.

### Handshake and Ordering

`in_ready` is asserted unconditionally for `buffer_now` (no output is produced that cycle), and follows `out_ready` for `pair_now`/`fwd_now`. For `flush_fwd`, `in_ready` is held low: the buffered half must be flushed first, so the non-half input is consumed the next cycle as `fwd_now`. This is what preserves record order — a full slot can never jump ahead of a still-buffered earlier half.

### Pending-Slot Register

`r_pend_valid` / `r_pend_slot` hold the first-of-pair half. The register sets on `buffer_now` and clears when the buffered half is consumed — either paired (`pair_now`) or flushed (`flush_fwd` / `idle_flush`) — gated by `out_ready`.

### Bit-Exactness

The golden model flushes a lone trailing half exactly once at end-of-stream. This packer flushes whenever its input is idle with a half buffered, which is identical for a gap-free record stream (the cosim drives records back-to-back, then idles once). A mid-stream input bubble would flush early — harmless (slightly less packing), never wrong.

---

## Timing Characteristics

This module is **sequential**: it contains clocked logic (via `always_ff` or
the repository's `ALWAYS_FF_RST` macro) and therefore holds state. Outputs
driven from those blocks are registered and appear one clock after the inputs
that produced them.

Per-path cycle counts are not enumerated here; read the block that drives the
signal you care about. No synthesis frequency or area figures are quoted --
none have been measured against a target device.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
The packer is instantiated inside `monbus_group_core` under the `HALF_BEAT_EN==1` generate branch:

```systemverilog
monbus_halfbeat_packer u_packer (
    .clk           (axi_aclk),
    .rst_n         (axi_aresetn),
    .in_valid      (comp_out_valid),
    .in_ready      (comp_out_ready),
    .in_slot       (comp_out_slot),
    .in_half_valid (comp_out_half_valid),
    .in_half_slot  (comp_out_half_slot),
    .out_valid     (comp_wr_valid),
    .out_ready     (write_fifo_wr_ready),
    .out_slot      (comp_wr_data)
);
```

When `HALF_BEAT_EN==0`, the compressor drives the write FIFO directly (the committed, timing-closed path) and this packer is not elaborated.

---

## Design Notes

### Requires the Compressor

Half-beat packing only makes sense downstream of the compressor, so `HALF_BEAT_EN==1` requires `USE_COMPRESSION==1`. In raw-only builds neither block exists.

### Order Preservation Is Non-Negotiable

The `flush_fwd` hold is the crux of correctness: without it, a full slot could be emitted while an earlier half still sits buffered, reordering the record stream. The single-cycle hold guarantees the buffered half is written first.

### One-Slot Buffer Only

The packer holds at most one pending half. It never accumulates more than two records' worth of state, keeping it cheap and its latency bounded to a single beat.

---

## Related Modules

### Used By
- **monbus_group_core.sv** — instantiates the packer in the `HALF_BEAT_EN==1` branch

### Uses
- **reset_defs.svh** — reset macros (`ALWAYS_FF_RST`, `RST_ASSERTED`)

### See Also
- **monbus_compressor.sv** — upstream compressor supplying the half sideband
- **monbus_group_core.sv** — capture core that owns the compressed write path

---

## Testing

**No dedicated testbench for this module.** It has no
`val/**/test_monbus_halfbeat_packer.py`. It is exercised indirectly, through the tests of
modules that instantiate it (directly or further up):

- `monbus_axi4_axil4_group` -- `val/**/test_monbus_axi4_axil4_group.py`
- `monbus_axil4_axi4_group` -- `val/**/test_monbus_axil4_axi4_group.py`
- `monbus_axil4_axil4_group` -- `val/**/test_monbus_axil4_axil4_group.py`

Indirect coverage exercises this module only in the configurations those
parents elaborate. A parameter or mode no parent uses is untested.

Treat any behaviour described on this page as unverified by simulation.

---

## References

### Source Code
- RTL: `rtl/amba/monitor/monbus_halfbeat_packer.sv`
- Golden model: `monbus_compressor.py` (`Encoder(half_beat=True)`)

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Compressor: `docs/markdown/rtl-amba/monitor/monbus_compressor.md`
- Group Core: `docs/markdown/rtl-amba/monitor/monbus_group_core.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to rtl-amba Index](../index.md)
