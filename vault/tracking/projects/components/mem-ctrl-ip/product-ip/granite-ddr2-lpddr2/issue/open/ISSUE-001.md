# ISSUE-001: same-id write B responses can leave out of AXI order across banks

> Source: granite TASK-006 addendum (2026-11-03), the one-id write-merge work.
> Found by reading `mc_bank_fifo_store`, not by a failing test.

**Priority:** P2 -- an AXI ordering rule, invisible to any master that only counts
OKAY Bs, but a producer/consumer master that reads after its B can see stale data.
**Status:** OPEN 2026-11-03, not reproduced.
**Owner:** TBD

## What the code does

AXI requires write responses with the same ID to return in the order the writes
were issued. In granite a write's B is produced when its slot DRAINS
(`mc_bank_fifo_store`: `wr_done_*` at the drain's last beat, into the intake's B
FIFO), and slots drain in the order the scheduler COMMITS them (the drain queue
is fed from `wr_commit_*`). The commit order is the pick's: FR-FCFS over per-bank
queues (`mc_bank_pick`), which keeps order WITHIN a bank queue but chooses freely
ACROSS banks (page hits, aged class, direction batching). Nothing in the store or
the pick compares ids, so two writes with one id to different banks can commit,
drain and B in the reverse of their AW order.

The merged-B work (TASK-006) does not add to it: a merged B always leaves right
behind its target's own, and the target is the youngest live write of its id.

## What would show it

A same-id write pair W1 (bank A, row miss or behind other traffic) then W2 (bank
B, page hit), one master, and a B-order check in the TB: the AXI4 slave monitor's
per-id order check, or an explicit expected-order queue per id. The granite core
TB's DFI model plus the BFM's write path is enough; the open question is whether
the BFM checks same-id B order or just counts.

## How it could resolve

- **Bug, fixed in the store:** hold a write out of the commit set while an older
  same-id write is uncommitted (a per-slot "older same-id pending" bit, the
  mirror of TASK-006's `r_wr_yng`), or reorder Bs per id at the output.
- **Bug, fixed in the pick:** same rule as a mask on the pick's write candidates.
- **No action:** if granite's contract is documented as "masters use distinct ids
  for writes that may reorder" -- not the case today; the HAS says nothing.
