---
title: Sizing invariants
summary: Shared-resource capacity math lives in ONE place, never a comment.
---

# Sizing invariants

- A shared resource serving N clients must be sized against
  N x per-client-limit, not the per-client limit. The monitor wedge shipped
  exactly this way: MAX_TRANSACTIONS(16) compared against per-channel
  AR_MAX_OUTSTANDING(8) on a SHARED master (real bound 64) - "passive"
  claimed in a comment, datapath throttled from 2 channels up.
- Invariants live in ONE place as a parameter or package function, derived
  by every consumer. `ocelus_common_pkg::cmd_entry_reserve` replaced two
  hand-synced localparams whose KEEP-IN-SYNC comment was the whole
  enforcement. A comment-encoded invariant is how that wedge shipped.
- Where feasible, assert the invariant at elaboration or under
  `ifdef FORMAL ([[formal]]) - a comment tests nothing.
- Recovery must be designed, not hoped: any occupancy gate needs its reopen
  threshold STRICTLY past its fill point, or saturation parks exactly at
  the threshold and latches (the block_ready lesson).
- **A ternary elaborates BOTH arms, so it cannot select between two widths.**
  `x = COND ? narrow[S-1:0] : wide[S-1:0]` is range-checked on both sides even
  when `COND` is a constant that makes one side dead, so the dead arm's
  out-of-range select is a hard error. Use a generate `if`, where only the live
  arm exists. *Case (2026-09-30): `rs_encoder` / `rs_decoder` map the core's
  per-symbol keep onto `tstrb` at 8-bit symbols and onto `tuser` otherwise. The
  mapping was written as a ternary; at the normal 8-bit configuration `tuser`
  is 1 bit wide, and Verilator rejected `in_tuser[3:0]` even though that arm
  can never be taken. A standalone lint of the module passed, because the
  module's DEFAULT parameters give `DATA_WIDTH == SYMBOL_WIDTH`, so one symbol
  per beat, so the select was `[0:0]` and in range. The error appeared only
  when a test elaborated it at `DATA_WIDTH = 32`. The lesson is narrower than
  "lint must elaborate": lint elaborates DEFAULTS, and a width-dependent
  select that is only wrong at non-default parameters is invisible until
  something instantiates the real configuration. Lint the module at the
  parameter sets it will actually be used with.*
- **A shift amount built from a product of narrow operands TRUNCATES, and the
  symptom points away from the shift.** `acc >> (count * HW'(WIDTH))` evaluates
  the product in HW bits, because a shift amount is self-determined. Four
  symbols times eight bits is 32, which in a 4-bit HW is 0 -- so the shift
  silently becomes a no-op. Multiply by the plain `int` localparam, or compute
  the bit count into an explicitly wide signal.
  *Case (2026-09-30): `rs_beat_packer`, which accumulates symbols and emits
  full beats. With the shift stuck at zero the accumulator never drained and
  each accepted beat was OR-ed on top of the one still in the low lanes. What
  made it slow to find is that every CONTROL output stayed correct -- the beat
  count, the keep pattern, and `out_last` placement are all computed from the
  symbol count, which was fine -- so the beat-count and contract assertions
  passed and only the data was wrong, from the second beat onward. A failure
  where the flags agree and the payload does not is worth suspecting a width
  before suspecting the algorithm.*

- **A tracking FIFO that is pushed unconditionally must be sized to the
  worst-case product of the limits that feed it, or gate the push.** A queue
  that records each issued request so a later phase can follow it (AW ->
  W-phase, AR -> R reorder) is often pushed "on handshake" with no `wr_ready`
  check, on the assumption it can never fill. That assumption is a product:
  channels x per-channel outstanding limit. It holds at the configuration it
  was written for and silently breaks when either factor grows. Gate the
  issue on FIFO room (a free entry at capture stays free until the push if
  only one request is held), or assert the product against the depth at
  elaboration.
  *Case (2026-10-17): RAPIDS `axi_write_engine` pushed its W-phase FIFO
  (depth 64) on every AW handshake. 8 channels x AW_MAX_OUTSTANDING 8 = 64,
  exactly the depth, so the 8-channel design could never overflow it; the
  16-channel build (128) dropped entries, those bursts' W data was never sent,
  and the sink hung waiting for B responses with every channel in
  XFER_DATA. The tell was in the bus counts, not the engine: 128 AWs
  (1024 beats) against 776 W beats. STREAM's and RAPIDS Beats' write engines
  carried the same ungated push; all three are gated now.*

- **A field packed with a literal-width cast does not grow with the parameter
  it holds.** `3'(channel)` (or `{28'b0, x[35:32]}`) is correct while the
  value fits and silently drops the high bit once it doesn't. Size the field
  from the parameter, e.g. `CHID_W = max(3, CHANNEL_WIDTH)`, keeping the old
  minimum so existing software layouts stay the same at the old
  configuration. When a design gains a larger configuration, grep the
  per-channel paths for literal-width casts and fixed slices, not just for
  parameters.
  *Case (2026-10-17): STREAM `perf_profiler` packed the FIFO entry as
  `{event, 3'(channel), timestamp}`. At 16 channels, channel 13 read back as 5,
  and because software parsed the event from bit [3], an END on channel 0 read
  as a START on channel 8. The full 16-channel regression was green, because no
  top test pulled a profiler entry for a channel above 7. A fub cell that walks
  every channel and checks the (channel, event) sequence caught it at once.*

- **A modular difference needs its own wire before it is widened.**
  `32'(r_now - r_ts)` with 16-bit stamps is not "the 16-bit difference,
  zero-extended": the cast is a context, and the operands may be extended to
  32 bits before the subtraction, so a wrapped stamp gives 0xFFFFxxxx. The
  simulator and the synthesizer need not agree on which reading they take.
  Declare `logic [15:0] w_d = a - b;` and widen `w_d`.
  *Case (2026-10-19): the bridge stress master's LAT_SUM was right in
  Verilator and saturated at 0xFFFFFFFF on the Genesys 2 from the first board
  run -- mean latency 21,474,836 cycles. A mean <= max check now runs in the
  pair test; it cannot catch the synthesis-only reading, the board can.*
