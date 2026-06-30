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

# AXI Write Engine - WLAST/Drain Lost-Beat Deadlock

## Final WLAST beat lost under W-channel backpressure

**Severity**: High
**Impact**: Write burst never completes; channel hangs permanently (would also hang on real hardware)
**Status**: RESOLVED
**Discovery Date**: 2026-06-29 (found via per-channel AXI timing-profile skew in the STREAM dv environment)

### Description

Under W-channel backpressure (`m_axi_wready` deasserting) combined with skewed
per-channel timing, the final beat of a write burst was transferred with
`m_axi_wlast` de-asserted, and `WLAST` instead pulsed one cycle later while
`m_axi_wvalid` was low. As a result the AXI write transaction never closed: the
slave received all data beats but never a beat with `WLAST=1`, so no `B`
response was returned, the scheduler stayed in `XFER_DATA`, the channel never
returned to idle, and the cocotb test eventually hit `SimTimeoutError`. After the
stall point every signal froze, confirming a true deadlock rather than slow
progress.

The defect is **seed dependent** and only appears under **per-channel timing
skew**. Uniform BFM timing profiles (`fixed`, `fast`, `constrained`) all pass on
every seed, because uniform timing never deasserts `wready` on the exact
final-beat boundary cycle that triggers the bug.

### Location

**File**: `projects/components/stream/rtl/fub/axi_write_engine.sv`
**Line**: 693 (`axi_wr_sram_drain` assignment)

### Root Cause

The SRAM drain (pop) was decoupled from the actual W-channel handshake:

```systemverilog
// BEFORE (buggy)
assign axi_wr_sram_drain = r_w_active && m_axi_wready;
```

The SRAM controller unit pops a beat when `axi_wr_sram_valid_comb && drain`
(`sram_controller.sv`, the unit's `valid`/`ready` pair). However `m_axi_wvalid`
is intentionally gated by BOTH the combinational valid and the **registered**
valid:

```systemverilog
assign m_axi_wvalid = r_w_active
                   && axi_wr_sram_valid[r_w_channel_id]        // registered (lags 1 cycle)
                   && axi_wr_sram_valid_comb[r_w_channel_id];  // combinational
```

(The registered-valid term is a deliberate guard against a spurious `wvalid`
pulse with stale data when the latency-bridge skid empties; see the in-code
comment.)

In the one-cycle window where `axi_wr_sram_valid_comb = 1` but the registered
`axi_wr_sram_valid = 0` (skid just refilled) and `m_axi_wready = 1`:

- `drain = r_w_active && m_axi_wready = 1`, so the unit popped a beat
  (`valid_comb && drain`),
- but `m_axi_wvalid = 0` (suppressed by the lagging registered valid), so that
  beat was **never transmitted on the W bus**.

`r_w_beats_remaining` only decrements on `m_axi_wvalid && m_axi_wready`, so it
stuck at 1 (holding `m_axi_wlast = (r_w_beats_remaining == 8'd1)` asserted), the
SRAM went empty (`valid` stayed low), `m_axi_wvalid` could never re-assert, and
the burst deadlocked. The earlier guard fixed the spurious *valid* but not the
spurious *drain*.

### Fix

Gate the drain on the real W-channel handshake so the SRAM is popped only for
beats that are actually transmitted:

```systemverilog
// AFTER (fixed)
assign axi_wr_sram_drain = m_axi_wvalid && m_axi_wready;
```

Since `m_axi_wvalid` already folds in `r_w_active`, the registered valid, and the
combinational valid, this pops exactly the beats accepted on the bus. This is the
canonical "pop on valid && ready" pattern.

### Verification

- Previously deadlocking per-channel-skew seeds (4, 5, 6 with `TIMING_PROFILE=mixed`): PASS.
- Heavy read + write backpressure (`slow_producer` / `burst_pause` on the read
  path and W channel), seeds 1/4/6/9: PASS.
- Uniform profiles (`fixed`, `fast`, `constrained`): unchanged (PASS).
- FUB timing sweeps: `descriptor_engine` (8 rows) and `scheduler` (7 rows): PASS.

### Regression Sentinel

The `mixed` timing profile is now a real per-channel skew with
`wr_w = 'burst_pause'` (W-channel backpressure, the bug locus). See
`MIXED_AXI_PROFILES` in `dv/tbclasses/stream_core_tb.py` and `stream_top_tb.py`.
The `stream_core` and `stream_top` `full` test levels use `timing_profile='mixed'`,
so this class of bug now has a standing regression sentinel.

### Reproduction (pre-fix)

```bash
source env_python
SEED=6 TIMING_PROFILE=mixed \
  pytest "projects/components/stream/dv/tests/macro/test_stream_core.py::test_stream_core_single_channel[params0]"
```

To bound a waveform capture, set `COCOTB_TIMEOUT_US` (default 500) and `WAVES=1`;
the deadlock freezes all activity within a few microseconds of the stall onset.
