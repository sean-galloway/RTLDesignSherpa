# TASK-007: close amber's CPU-side paths on Artix-7 (xc7a100t-1)

**Priority:** P4
**Status:** open (filed 2026-11-25; owner: "File an amber task"), not scheduled
**Owner:** TBD (filed from riscv-ip/peregrine-rv32im TASK-001 stage 7)

## Why

peregrine kept amber's 1-cycle hit (TASK-005) and lowered its clock
instead (peregrine PRD P14, owner 2026-11-25: 18.5 ns, 54.1 MHz). Every
path group that limits `peregrine_top` there runs through amber; every
peregrine-only group has 3.5 ns or more of slack. This task holds what was
measured, so the work is ready if peregrine (or another Artix client)
needs a faster clock.

## Measured (peregrine TASK-001 stage 7, OOC, 0.2 ns setup uncertainty)

- `amber_top` alone (`MAINT_EN=1`, no monitor) at 10 ns on xc7a100t-1:
  WNS -4.046 ns, its control state into its data RAM's B address. The same
  build on xc7k325t-2 had +0.357.
- Inside `peregrine_top` at 17.0 ns (the best closing point), the three
  tightest groups:
  - amber internal: control state -> data RAM B address, 20 levels, +0.331;
  - core -> amber: request valid -> the accept-cycle tag LUTRAM address
    mux -> compare -> `state_d` -> data RAM address, +0.495 (about 11.7 ns
    of cone at 10 ns);
  - amber -> core: `cpu_rsp_rd_data` (way select behind the LRU / victim
    state) arrives 10.4-11.1 ns after the edge, +0.637.
- 17.5 ns failed by 0.051 where 17.0 ns passed: near the edge, placement
  noise exceeds the 0.2 ns budget.

## What (a direction, not decided)

Without giving up the 1-cycle hit if possible:
- take `state_d` out of the data RAM address: address the data RAM from
  the arriving `{set, beat}` keyed off the request valid alone, reading
  every way, and select after the compare;
- shorten the response way select (a one-hot hit vector straight from the
  compare, not through the victim / LRU state).

If the 1-cycle hit cannot close a target, the jet-prime delta 04 shape (a
registered tag read, a 2-cycle hit) is the fallback; that changes
peregrine's CPI (+10.7 to +12.8% on its kernels, measured as option (b) in
peregrine TASK-001 stage 7) and needs the owner.

## Done when

- `amber_top` (`MAINT_EN=1`) meets a target period agreed with the owner
  on xc7a100t-1 with 0.2 ns of uncertainty, in more than one placement.
- TASK-005's latency test still reports read hit 1 / 1, write hit 1 / 2,
  or the owner has accepted the change.
- amber FULL, common-ip FULL, jet / jet-prime / onyx gates and amber's
  formal are green; peregrine FULL is green and its OOC is re-measured.
