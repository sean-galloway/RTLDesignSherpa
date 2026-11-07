---
title: A token or credit counter adds every event in the cycle, it never ORs them
summary: Two release tokens matured in one cycle were ORed into one; the lost token left a command in the FIFO with no token and every later command left only when the next one arrived (pumice BUG-033).
---

# A token or credit counter adds every event in the cycle, it never ORs them

**Rule:** when a counter stands for things that must balance -- tokens
against FIFO entries, credits against outstanding requests, grants against
returns -- every source of an increment in a cycle is ADDED, as a count, even
when the designer believes two sources cannot fire together. An `||` between
two increment sources is an off-by-one waiting for the one cycle the belief
is wrong, and a balance error in a token counter does not fail loudly: it
shifts the pairing by one and stays shifted.

## The failure that taught it (pumice BUG-033, 2026-11-07)

`mc_scheduler_plane` releases each command from its output FIFO CMD_DELAY
cycles after the arbiter fires it (so write data leads its command), or
immediately under the fast read release when the line is idle. Both paths
produce a TOKEN: the delay shift's output, or the fast push itself; the FIFO
head is released while tokens are pending. The two sources were combined as

```systemverilog
assign w_tok_mature = r_tok_shift[CMD_DELAY-1] || (w_cmd_push && w_fast_now);
r_tok_cnt <= r_tok_cnt + (w_tok_mature ? 1 : 0) - (w_cmd_pop ? 1 : 0);
```

with the comment that in fast mode the shift is empty, so they never
coincide. They coincided once per failing run: `r_fast` sets on a registered
`r_idle >= r_smax`, so a push landing in the exact cycle the idle count
crosses the threshold is a slow push whose token enters the shift, and fast
mode is on one cycle later with that token in flight; six cycles on it
matures beside a fast push and one token is lost. From then on the FIFO holds
one command more than it has tokens, every command leaves only when the next
command is pushed, and a REF with nothing behind it waits for the ACT the
arbiter had correctly spaced tRFC later -- the two reach the DRAM one cycle
apart. Bandwidth never moved, the arbiter's own JEDEC checker saw nothing
(it binds at the fire), and the board failed one run in three for a month.

What found it was an ILA with the counter itself probed: `r_tok_cnt` read 0
at every sample of a failing run and 1 during bursts of a healthy one. Two
earlier, plausible fixes (an arbiter tRFC seam, an 8-deep CDC FIFO) were
real hazards and did not touch the failure rate; the counter did.

## The rules

- **Add, do not OR.** `cnt <= cnt + src_a + src_b - pop`, with the sum wide
  enough. If two sources truly cannot coincide, the add costs nothing and the
  belief is not load-bearing.
- **Make the invariant checkable.** Tokens pending (counter plus shift
  population) must equal FIFO occupancy whenever the line is quiet; a sim
  or ILA probe of that difference turns a silent shift into a number.
- **Enter a mode on the state the mode assumes.** Fast mode assumed an
  empty shift; it is now entered only on an idle cycle (`&& w_line_empty`),
  so the assumption is enforced by the condition that sets it, not by an
  argument about the cycles before.

See also [[global-windows-revalidate-at-issue]] (the arbiter seam closed on the
way) and [[cdc]] (the FIFO depth closed on the way); both were correct
findings about the wrong stage, and the tracker records why each was
believed.
