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
  by every consumer. `monitor_common_pkg::cmd_entry_reserve` replaced two
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

