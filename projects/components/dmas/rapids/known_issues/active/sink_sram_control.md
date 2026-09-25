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

# Sink SRAM Control - Known RTL Issues

## Single Read Operation Limitation

**Severity**: Low
**Impact**: Concurrent read operations not supported
**Status**: CONFIRMED structural against the beats RTL 2026-09-25
**Discovery Date**: During RTL review

### Description

The SRAM control module is implemented with a simplified architecture that only supports one read operation at a time, which may limit throughput in high-performance scenarios.

### Location

**File**: `projects/components/dmas/rapids/rtl/macro_beats/snk_sram_controller_beats.sv` (issue was filed against the retired pre-beats sink_sram_control.sv line 685; re-verify against the beats controller)

### Current Code (Limitation)
```systemverilog
// TODO: This is a simplified implementation that only supports one read at a time
```

### Impact on Functionality

1. **Throughput**: Multiple concurrent reads cannot be processed
2. **Performance**: Potential bottleneck in read-heavy workloads
3. **Utilization**: SRAM bandwidth may be underutilized
4. **Latency**: Read operations must be serialized

### Root Cause

The current implementation was designed for simplicity rather than maximum performance, implementing a single-read-at-a-time architecture.

### Potential Enhancement

A full implementation could support:
1. Multiple concurrent read operations
2. Read operation pipelining
3. Improved memory bandwidth utilization
4. Reduced read latency through parallelism

### Fix Priority

**Low Priority** - This is an architectural simplification rather than a bug. Enhancement would be beneficial for high-performance applications but current implementation is functionally correct.

### Additional Notes

- Current implementation is stable and functionally correct
- All other SRAM control features work as designed
- Enhancement would require significant architectural changes
- Performance impact depends on specific workload characteristics

### Re-verified against the beats RTL (2026-09-25) -- THE ARCHITECTURE CHANGED

This entry asks to "re-verify against the beats controller". Done:

- No `TODO`, `simplified`, `one read` or `single read` comment exists in
  `snk_sram_controller_beats.sv` (237 lines).
- The pre-beats `sink_sram_control.sv` it was filed against is retired.
- The current module is built around a per-channel decode -- `fill_ready`
  (`:70`), `drain_read` (`:86`), `fill_ready_per_channel` (`:109`),
  `drain_read_decoded` (`:110`), with a fill-ready mux (`:132-138`) and a
  drain-read decode (`:143-145`) -- not the single-read-at-a-time structure the
  entry describes.

Whether a concurrency limitation still exists is an open question, but it is NOT
the one documented here, and the quoted code is gone. Needs re-filing against
the beats RTL before it can be mapped.

---

## Re-verified against the beats RTL (2026-09-25)

Filed against the retired pre-beats `sink_sram_control.sv:685`, so the anchor
was stale. The claim holds, and it is **structural** rather than a missing
feature -- the limitation is visible in the port shape of
`snk_sram_controller_beats.sv`, which is why a keyword search for
"single read" finds nothing.

One drain port is shared across all `NC` channels and selected by a single
`drain_id`:

```systemverilog
// snk_sram_controller_beats.sv:143-151  -- one-hot read decode
drain_read_decoded = '0;
if (drain_read && drain_id < NC) begin
    drain_read_decoded[drain_id] = 1'b1;
end

// :153-160  -- single data mux
if (drain_id < NC) begin
    drain_data = drain_data_per_channel[drain_id];
end
```

`drain_read` is a single bit and `drain_id` a single index, so exactly one
channel can be drained per cycle by construction. "Concurrent read operations
not supported" is therefore not an omission that could be patched inside the
module -- it is the interface. Supporting concurrent drains would mean
widening `drain_read`/`drain_id`/`drain_data` to per-channel vectors and
giving the consumer a way to accept more than one beat per cycle.

The fill side has the identical shape (`fill_valid_decoded` /
`fill_ready` mux on `fill_id`, `:122-141`), so the same statement applies to
writes.

This matches the original entry's own assessment -- "an architectural
simplification rather than a bug... current implementation is functionally
correct" -- and the Low priority stands. Recorded so the next reader does not
go looking for missing logic inside the controller.
