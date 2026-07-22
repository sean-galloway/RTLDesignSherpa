---
title: Priority logic depth
summary: Serialized scans synthesize to chains; write parallel selects.
---

# Priority logic depth

A loop with an early-exit flag
(`for(r) for(i) if (!found && ...) begin ... found=1; end`)
is functionally fine and synthesizes to a PRIORITY CHAIN: every iteration
in series. Real case: pick_oldest in axi_monitor_trans_mgr - N=36 gave
242 logic levels, ~125 ns data path, WNS -120 ns; sim passed, formal (BMC
at N=2..4) passed, first synthesis run died.

Rules:
- Any selection over a MAX_*-sized structure is written as a PARALLEL
  reduction: `win[i] = cand[i] && !(exists j: better(j,i))` - O(N^2) area,
  O(log N) depth, each output independent.
- Check logic depth for looped code before calling it done; synthesis is a
  separate gate no sim/formal result covers ([[formal]] states this too).
- Ties break by index to keep behavior bit-exact with the scan it replaces.
Fix reference: commit 08f6c18e.
