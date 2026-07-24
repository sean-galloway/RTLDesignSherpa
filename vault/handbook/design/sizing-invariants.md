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
