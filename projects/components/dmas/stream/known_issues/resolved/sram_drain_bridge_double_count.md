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

# SRAM Drain Accounting - Latency-Bridge Double-Count Deadlock

## Bridge occupancy counted twice, over-draining the drain FIFO and freezing all channels

**Severity**: High
**Impact**: All channels deadlock permanently; would also hang on real hardware
**Status**: RESOLVED
**Discovery Date**: 2026-07-20 (found via `stream_top_ch8` 8-channel `slow_producer` regression)

### Description

With 8 channels active under the `slow_producer` AXI timing profile, the whole
design froze: W-channel activity proceeded normally and then stopped completely
in a single cycle, with no further progress until the testbench timed out.

Symptoms at the freeze point:

- Channel 0 in scheduler state `CH_COMPLETE`, waiting forever on
  `w_write_complete` (`r_write_beats_to_commit == 0`), i.e. waiting for write
  `B` responses that never arrive.
- Channels 1-7 all stuck in `CH_XFER_DATA` with `d2s_v=1 d2s_r=0`, no error flags.
- `USE_AXI_MONITORS=0` for this test, so the monitor subsystem is not involved.

The failure is timing-profile dependent: `fixed` and `mixed` pass, only
`slow_producer` fails, and only with many concurrent channels.

### Location

**File**: `projects/components/dmas/stream/rtl/fub/sram_controller_unit.sv`
**Line**: `axi_wr_drain_data_avail` assignment

### Root Cause

The reported drain availability added the latency bridge's occupancy on top of
the drain controller's occupancy:

```systemverilog
// BEFORE (buggy)
assign axi_wr_drain_data_avail = drain_data_available + SCW'(bridge_occupancy);
```

That addend double-counts. `drain_data_available` is `(wr_ptr - rd_ptr)` from
`stream_drain_ctrl`, where:

- `wr_ptr` advances at the FIFO **write** port
  (`.wr_valid(axi_rd_sram_valid && axi_rd_sram_ready)`), and
- `rd_ptr` advances only on a drain **reservation** (`.rd_valid(axi_wr_drain_req)`).

Neither pointer is tied to the FIFO **read** port. A beat that has moved out of
the FIFO into the latency bridge's skid buffer is therefore still counted in
`drain_data_available`; adding `bridge_occupancy` counted it a second time. The
bridge prefetches unconditionally (`stream_latency_bridge.sv`, `s_ready` does not
depend on `m_ready`), so it holds up to `SKID_DEPTH` (4) beats whenever the FIFO
is non-empty. The over-report was thus 0..4 beats, and was largest exactly when
the FIFO ran near-empty with the bridge holding its prefetch -- the
`slow_producer` steady state.

The resulting deadlock chain:

1. `axi_write_engine` sized a burst against beats that do not physically exist
   and issued `axi_wr_drain_req` with `size = awlen+1`.
2. `stream_drain_ctrl` advances `r_rd_ptr_bin` by the **full** requested size,
   gated only on `!r_rd_empty` -- which is false here, since the count is small
   but non-zero. `rd_ptr` overshot `wr_ptr`.
3. `fifo_control` computes the occupancy with a wrap correction, so an overshoot
   of 4 evaluates as `DEPTH - 4` (~4092). Both pointers then advance in
   lockstep, so **the corruption is permanent** -- the channel reports a
   nearly-full FIFO forever.
4. The engine kept issuing AWs with no backing data. `m_axi_wvalid` is gated on
   the channel's SRAM valid, so the starved channel drove `wvalid` low.
5. The W-phase FIFO is a **single shared, strictly in-order** FIFO, so the
   stalled entry at its head could not be skipped: all 8 channels' W traffic
   stopped in the same cycle.
6. No W bursts completed, so no `B` responses returned, so channel 0 waited in
   `CH_COMPLETE` forever.

Observed directly: channel 0 requested `rd_size=17` against `data_available=13`
-- an overshoot of exactly 4, the bridge skid depth.

### Fix

Report only the drain controller's own occupancy:

```systemverilog
// AFTER (fixed)
assign axi_wr_drain_data_avail = drain_data_available;
```

Beats already reserved by an in-flight drain are excluded from the count. That is
conservative in the safe direction: it can only delay an AW, never over-issue one.

### Detection

`stream_drain_ctrl.sv` gained a permanent simulation check that fires the moment
a reservation exceeds the real occupancy, instead of leaving a silently corrupted
counter to surface as a deadlock hundreds of microseconds later:

```systemverilog
if (axi_aresetn && rd_valid && !r_rd_empty && (rd_size > data_available))
    $error("stream_drain_ctrl: over-drain ...");
```

Note it is written as a procedural `always_ff` + `$error`, not an
`assert property`: Verilator silently ignores SVA unless built with `--assert`,
which this flow does not pass, so a concurrent assertion would have been dead code.

Pre-fix this check fires at ~3.97 us on channel 0 -- roughly 250 us before the
deadlock previously became visible.

### Verification

- `test_stream_top_multi_channel[slow_producer]`: was deadlock, now PASS.
- `test_stream_top_stress[slow_producer]`: was deadlock, now PASS.
- Over-drain check silent across the full STREAM regression.
- `fixed` / `mixed` profiles unchanged (PASS).

### Relationship to the WLAST/drain issue

This shares the "every signal freezes at once" signature with
[axi_write_engine WLAST/drain lost-beat deadlock](axi_write_engine_wlast_drain.md)
but has a different root cause. That issue's Verification section claimed
`slow_producer` coverage; this deadlock shows that claim was too strong -- the
WLAST fix was necessary but not sufficient.
