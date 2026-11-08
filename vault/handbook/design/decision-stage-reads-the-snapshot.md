---
title: A pipelined lookup's decision stage reads only its snapshot; the live port belongs to the next capture
summary: When a lookup pipeline captures a request in the same cycle its occupant advances (pipe_room = empty | advancing), the array's read port serves the INCOMING request's snapshot in that cycle. Every consumer of the occupant's decision -- hit way, victim state, victim tag -- must read the registered snapshot, never the live port, or the address mux is pulled two ways and one request snapshots the wrong set. jet v3, 2026-11-07: a same-tag line in the occupant's set classified as a hit and the read served zeros.
---

# A pipelined lookup's decision stage reads only its snapshot

**Rule:** in a capture/classify lookup pipeline over a single-read-port array,
the classify stage consumes exactly one thing: the **registered snapshot** the
capture took (and the dirty-replay refreshed). The live read port is owned by
the capture that can land in the classify cycle. If any classify-side term
reads the live port, the port's address mux has two masters in the advance
cycle and one of them loses silently.

The invariant that makes the snapshot sufficient: a tag write to the captured
set marks the snapshot dirty and replays the read before the classify may
advance, so whenever `w_cls_advance` is true the snapshot **equals** the array.
There is no information in the live read that the snapshot does not already
hold.

## The failure that taught it (jet v3 lookup pipeline, 2026-11-07)

`jet_control` v3 captures a request when `lkup_valid & tag_gnt & pipe_room`,
with `pipe_room = ~r_lk_valid | w_cls_advance` -- a new request may land in the
cycle the occupant retires. The port-A address was

```
tag_a_set_o = r_init_busy ? r_init_cnt : r_lk_valid ? w_req_set : w_live_set;
```

i.e. the OCCUPANT's set whenever the pipe was occupied, including the advance
cycle. The occupant needed it: the alloc path read the victim's state and tag
from the live port (`tag_a_tag_state_i[repl_victim_way_i]`). But the incoming
request's snapshot `r_lk_tagstate <= tag_a_tag_state_i` loaded in that same
cycle, so it captured the **occupant's set**.

Trace (jet_core func, SEED 46262): cycle 1901 the pipe holds line 0x44 (set 4)
and advances; line 0x66 (set 6, tag 0x6) is captured in the same cycle; the
snapshot is set 4's tags, where line 0x64 (tag 0x6) is resident in way 0; 0x66
classifies as a HIT in way 0; the serve reads data set 6 way 0 and deposits
zeros. Gate never saw it (requests are spaced); func hit it in the first
random soak, and jet_parity's "hit/miss parity" cells were the same bug seen
through the cache_sim oracle. A/B against the pre-FPGA-rework `jet_control`
failed identically -- the bug predates the rework, and the earlier triage that
filed it as "TB model debt" was wrong (see the memory note).

## The fix

Both halves, in `jet_control.sv`:

- the victim's state and tag read the snapshot:
  `w_victim_state = r_lk_tagstate[repl_victim_way_i][2:0]` (and the tag);
- the address mux follows the capture:
  `tag_a_set_o = r_init_busy ? r_init_cnt : (r_lk_valid & ~w_cls_advance) ? w_req_set : w_live_set`.

`w_cls_advance` depends on registered state and on MSHR/repl lookups keyed by
`r_lk_addr`, never on `tag_a_tag_state_i`, so the mux is loop-free. Afterwards
the jet_core func cell that failed passes with 7,098 checks and 0 mismatches.

## How to apply

- Grep the classify stage for the live read-port signal. Every hit outside the
  snapshot register's load is a second consumer; move it onto the snapshot.
- The dirty-replay rule is what licenses this: if your pipeline lacks one, you
  cannot use the snapshot for the victim either, and you must not allow a
  capture in the advance cycle (throughput cost) -- pick one, document it.
- Write the TB so a false hit is caught at the response, not the tag: a
  snapshot taken FROM the RTL agrees with the RTL by construction (the TB's
  way came from `r_lk_tagstate` and said "way 0" too). The data compare
  against the memory model was the only independent check. Trace rings keyed
  by set (`JET_TRACE=1` in jet_core_tb) found it in one run.

Related: [[plane-boundary-registered-snapshots]] (the same principle at a plane
boundary), [[valid-ready-contracts]], [[never-dismiss-failures-as-flaky]].
