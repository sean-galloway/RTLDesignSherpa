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

# Sink Data Path - Known RTL Issues

## AXI Timeout Detection Missing

**Severity**: Medium
**Impact**: Timeout errors not detected or reported
**Status**: RESOLVED 2026-09-25. The one real defect (the discarded write-error flag) is fixed; the "missing timeout" half is BY DESIGN -- timeouts are the monitor's job, not the datapath's.
**Discovery Date**: During RTL review

### Description

AXI timeout detection is not implemented in the sink data path, with only a placeholder assignment that always returns false.

### Location

**File**: `projects/components/dmas/rapids/rtl/macro_beats/snk_data_path_beats.sv` (issue was filed against the retired pre-beats sink_data_path.sv line 283; re-verify against the beats module)

### Current Code (Incomplete)
```systemverilog
assign error_axi_timeout = 1'b0;  // TODO: Add timeout detection from AXI engine
```

### Impact on Functionality

1. **Error Detection**: AXI transaction timeouts are not detected
2. **System Monitoring**: No visibility into stuck AXI transactions
3. **Error Recovery**: Timeout-based recovery mechanisms cannot operate
4. **Debug Capability**: Cannot identify slow or hanging AXI transactions

### Root Cause

Timeout detection logic was not implemented in the initial version, leaving only a placeholder that disables timeout reporting.

### Required Implementation

The timeout detection should:
1. Monitor AXI transaction duration
2. Compare against configurable timeout threshold
3. Assert error when threshold exceeded
4. Provide timeout event reporting via monitor bus

### Fix Priority

**Medium Priority** - Required for robust error handling and system monitoring in production environments with potential AXI slave latency issues.

### Additional Notes

- Error signal is properly connected to higher-level error reporting
- Infrastructure exists for timeout error handling
- Only the detection logic itself is missing

### Re-verified against the beats RTL (2026-09-25) -- THE CITED SIGNAL IS GONE

This entry asks to "re-verify against the beats module". Done, and the result is
that the code it describes no longer exists:

- `error_axi_timeout` -- **0 occurrences** anywhere under `rapids/rtl/`.
- `timeout_detect` -- 0 occurrences.
- `snk_data_path_beats.sv` (280 lines) contains no timeout signalling and no
  `error_*` assigns at all.
- The pre-beats `sink_data_path.sv` the placeholder was filed against is retired
  and absent from the tree.

So the specific defect as written -- "only a placeholder assignment that always
returns false" -- cannot be reproduced, because the placeholder is not there.

**What IS true, stated precisely so this is not mistaken for "fixed".** The sink
data path still has no AXI timeout detection; the gap is real, the cited
implementation is not. Note the word is overloaded here exactly as it was in
STREAM: `scheduler_beats.sv:105-107` DOES carry a full scheduler timeout
(`cfg_sched_timeout_cycles` / `_limit` / `_enable`, `r_timeout_counter`), and the
four `axi_timeout` hits in rapids are all `cfg_axi_timeout_mask`, a MONITOR
packet mask (`monbus_axil_group_2in.sv:107`, `scheduler_group_array_beats.sv:925`).
Neither is sink-path AXI timeout detection. Two mechanisms sharing a word is how
STREAM's monitor timeout went untested for so long.

Needs re-filing against the beats RTL with a current location before it can be
mapped or fixed.

---

## Re-verified against the beats RTL (2026-09-25)

Checked while building the RAPIDS contracts workbook (rapids TASK-002). The original
entry was filed against the retired pre-beats `sink_data_path.sv:283`, so only
the ANCHOR was stale. **The claim itself holds, and there are actually TWO
distinct gaps here, not one.**

### Gap 1 -- NOT A GAP. Timeouts belong to the monitor, by design

**Owner's decision, 2026-09-25: "Gap1 is on purpose. The monitor code takes
care of timeouts."** This section previously called it an open defect. That was
wrong and is retracted.

`axi_write_engine_beats.sv` really does contain no timeout, watchdog or stall
counter -- the only `timeout` occurrence is a comment at `:340`, and STREAM's
byte-identical `axi_write_engine.sv` is the same. But that is the intended
split of responsibility, not an omission: AXI transaction timeouts are detected
by the monitor layer, which already does exactly what this entry's "Required
Implementation" list asks for.

Where that machinery lives:

- `rtl/amba/monitor/axi_monitor_timer.sv` -- per-transaction duration timing.
- `rtl/amba/monitor/axi_monitor_reporter_timeout.sv` -- "Timeout-packet
  detection cone (split out of axi_monitor_reporter so integrators can drop it
  with ENABLE_TIMEOUT_LOGIC=0)". It scans for unreported ERROR slots the timer
  flagged via `timeout_detected[idx]`, priority-encodes the first match, and
  emits a MonBus packet. Gated by `cfg_timeout_enable` (`:30`, `:55`).
- RAPIDS instantiates a monitor at `scheduler_group_array_beats.sv:841`
  (`u_desc_axi_monitor`, `.USE_MONITOR(USE_AXI_MONITORS == 1)` at `:840`), and
  `USE_AXI_MONITORS` defaults to 1 (`:59`, and `rapids_beats_top.sv:74`).

Read the original "Required Implementation" list against that: monitor
transaction duration, compare against a configurable threshold, assert on
exceed, report via the monitor bus. That is the monitor's job description. The
entry was asking the sink datapath to reimplement it, which would duplicate
the mechanism in two places -- and the word "timeout" is already overloaded
here (the scheduler's own `cfg_sched_timeout_*` progress timeout is a
different, third thing).

**What I checked and did NOT establish**, recorded so nobody reads more into
this than the evidence supports: the monitor instance I found in `rapids/rtl`
is on the DESCRIPTOR AXI bus. I did not locate an instance covering the sink
WRITE data bus inside `rapids/rtl`, and `rapids_beats_top.sv:1205-1216` leaves
the per-engine `cfg_rdeng_mon_*` configuration ports unconnected. The
characterization build does carry a three-level MonBus merge per half, so the
coverage may be wired at that integration level. Anyone extending monitor
coverage should start there rather than adding a counter to the engine.

### Gap 2 -- bad-B-response detection EXISTS and is thrown away (RAPIDS only) -- FIXED

This was the real defect, and it is fixed (see the APPLIED note below).

The write engine already detects bad write responses, per channel, sticky:

```systemverilog
// axi_write_engine_beats.sv:951
if (m_axi_bvalid && m_axi_bready && (m_axi_bresp != 2'b00)) begin
    ch_id = m_axi_bid[CIW-1:0];
    r_wr_error[ch_id] <= 1'b1;          // :955
...
assign sched_wr_error = r_wr_error;      // :964
```

and the port is declared `output logic [NC-1:0] sched_wr_error, // Sticky
error flag per channel (bad B response)` (`:144`).

On the SINK that signal never reaches the scheduler. The chain, all in the
shipping configuration:

1. `rapids_snk_beats.sv:596` instantiates `snk_data_path_axis_beats`, which at
   its `:253` instantiates `snk_data_path_beats`.
2. `snk_data_path_beats.sv:269` connects the engine's error to nothing:
   `.sched_wr_error     (),` under the comment "Error and Debug (unconnected
   at this level)".
3. Neither `snk_data_path_beats` nor `snk_data_path_axis_beats` declares an
   error output -- the only `output ... sched_wr_error` anywhere in RAPIDS is
   the engine's own at `axi_write_engine_beats.sv:144` -- so it cannot
   propagate even in principle.
4. `rapids_snk_beats.sv:680` then ties the scheduler's input off:
   `assign sched_wr_error = '0;  // TODO: Add when write engine supports error
   reporting`.

**That TODO's stated reason is false.** The write engine has supported error
reporting all along; see `:144`/`:951`/`:964` above.

### Consequence: two fatal-error terms are dead on the sink

`scheduler_beats.sv:978` puts `sched_wr_error` inside `w_hard_error`, and
`:944` latches `r_write_error_sticky` from it. With the input tied to `'0`,
both terms are provably inert on the sink: a SLVERR or DECERR on a write
response can never drive the channel to `CH_ERROR` (`:380`). The transfer
completes "successfully" with corrupt or undelivered data.

### STREAM does not have this defect

`stream_core.sv:669` declares `sched_wr_error`, connects it at `:1047` and
`:1409`, has no tie-off and no TODO, and surfaces it for observability --
`obs_flags[11] = sched_wr_error[w_obs_ch]` (`:2130`), commented "live engine
error -> scheduler" (`:2101`). The RAPIDS source path is also correct:
`src_data_path_beats.sv:79` declares `output ... sched_rd_error` and `:203`
connects it. The gap is sink-only.

### Candidate fix for gap 2

Add a `sched_wr_error` output to `snk_data_path_beats` and
`snk_data_path_axis_beats`, connect `:269`, and replace the `:680` tie-off
with it -- mirroring what the source path already does for `sched_rd_error`
and what STREAM does for both. Gap 1 (an actual timeout) is a separate,
larger piece of work in a file shared with STREAM.

**APPLIED 2026-09-25.** Gap 2 is fixed: `snk_data_path_beats` and
`snk_data_path_axis_beats` each gained a `sched_wr_error` output, the discard
at `snk_data_path_beats.sv` is now a real connection, and the
`rapids_snk_beats.sv` tie-off (with its false TODO) is deleted. The engine's
sticky bad-B-response flag now reaches `scheduler_beats`, so `w_hard_error`'s
`sched_wr_error` term and `r_write_error_sticky` are live on the sink and a
SLVERR/DECERR can drive the channel to `CH_ERROR` as it always could on the
source half. Verilator lint is clean and warning-for-warning identical to the
pre-change baseline.

Gap 1 is NOT fixed -- there is still no AXI transaction timeout in
`axi_write_engine_beats`, and because that file is byte-identical with
STREAM's, implementing one belongs in both. This entry stays ACTIVE for that.

Worth noting for whoever does gap 1: a SLVERR arrives WITH a B response, so it
produces a commit strobe (`axi_write_engine_beats.sv:898` gates on
`m_axi_bvalid && m_axi_bready && BID` with no `bresp` test) and therefore
RESETS the scheduler's timeout counter (`scheduler_beats.sv:920`). Before this
fix, errored traffic was invisible to the error path AND to the timeout path
at once. With gap 2 fixed the error path now catches it, but a silently
dropped burst that never returns a B is still only a timeout's job.

### Mapped in the contracts workbook (2026-09-25)

Gap 2 is now a computed K-map in `projects/components/dmas/rapids/docs/rapids_signal_contracts.xlsx`,
sheets "Contracts snk errors" and "K-maps snk errors" (rapids TASK-002 item 1).

Map 1 mirrors `w_hard_error` on the SINK instance and inverts the usual
reading of a don't-care: **28 of 32 cells are X**, not because those states
cannot physically occur but because the instantiation ties inputs to
constants. `sched_rd_error` and `r_read_error_sticky` are carried as one axis
and excluded LEGITIMATELY (no AXI read engine on the sink); `sched_wr_error`
and `r_write_error_sticky` are carried as separate axes and excluded BY THE
DEFECT -- kept apart so the two kinds of tie-off are not blurred. Of the 4
surviving cells 3 are green, spanned by `descriptor_error` and `ctrl_err`
alone, so for a DATA descriptor `w_hard_error` reduces to `descriptor_error`.

Map 2 (`CH_ERROR` entry) surfaced a consequence not recorded above: a SLVERR
arrives WITH a B response, so it counts as write progress and RESETS the
timeout counter (`scheduler_beats.sv:920`). Errored traffic therefore looks
healthy to the error path and the timeout path at the same time -- the
timeout cannot serve as a backstop for the missing error wiring.

The workbook also carries a stage-by-stage table of where the error is lost,
from the engine's detection through to the dead scheduler terms.
