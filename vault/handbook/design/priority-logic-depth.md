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

## Second case: a running max is a chain too (bridge_cam, 2026-09-11)

`for (n) if (match[n] && count[n] > max) max = count[n];` -- no early-exit
flag, but every iteration's compare depends on the previous max, so it is
the same serial chain. In `bridge_cam` Mode 2 that scan over 16 entries hung
off the crossbar's arbitrated ARID: 40 LUT levels, 32 ns data path, WNS
-22 ns at 10 ns on an Artix-7 -1, the whole generated bridge capped at ~31
MHz. Every functional test passed; the first out-of-context synthesis run
(HAS 6.4) found it in minutes.

The fix was not a tree-max. The counts of one tag are always `0..k-1`, so
the max is `popcount(match) - 1` -- an adder tree, a few levels. Likewise
"the matching entry with count 0" is one-hot by construction, so its index
and its data are OR-reductions, not a last-match-wins priority chain.

- **Before writing a reduction, ask what invariant the structure keeps.**
  A max, a search, a priority pick often collapses to a popcount or a
  one-hot OR once the invariant is named -- shallower than any tree and
  cheaper than the O(N^2) parallel select.
- **Any block with a for-loop feeding a flop goes through synthesis before
  it is called done.** `projects/components/bridge/fpga/` runs a whole
  bridge out of context in minutes; a component without such a flow has no
  timing gate at all.

## Third case, same week: the author of the second case wrote a fourth chain

`axi_monitor_lite` (TASK-098, 2026-09-25) needed "the oldest entry whose ID
matches". The first draft was `for (i) if (match[i] && age[i] > best) best =
age[i]` -- a running max, written the day after the bridge_cam entry above
was added to this note. It simulated, proved, and synthesized to **89 LUT
levels and -51 ns** at sixteen slots. The tournament rewrite (pair up
neighbours span 1, 2, 4, 8; each level independent of the last) is log2(N)
compares deep and identical in function.

Knowing the rule is not the check. The check is the synthesis run, and
`projects/components/bridge/fpga` makes one cost minutes: anything with a
`for` whose body reads what an earlier iteration wrote goes through it
before it is called done -- the comment in the RTL now says so at the
function that had the chain.

The tournament was not the end of it either. The same block went through
three more synthesis passes (per-slot arithmetic, then a subtract in front
of every compare, then the whole event tail in the attribution cycle) before
the ordering compare disappeared altogether: same-ID entries keep a linked
list, and "the oldest with this ID" is the one flagged as that list's head.
The cheapest max is the one you never compute -- see
[[area-measure-by-hierarchy]] for how the reports steered each pass.
