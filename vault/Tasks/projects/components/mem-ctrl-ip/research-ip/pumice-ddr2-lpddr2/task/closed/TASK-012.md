# TASK-012: REF_STATS_REF free-runs, so axis 3 is estimated rather than measured

**Status:** CLOSED 2026-09-25 — measured via REF_STATS_REF_BUSY (refreshes with work pending). **Priority:** P2 — characterization accuracy, not
a functional defect; nothing on the board misbehaves because of it

Split out of [[TASK-001]] when that umbrella closed. It was gap 2 of the three
[[TASK-002]]'s first board campaign reported back; gaps 1 (RBL epoch default)
and 3 (config-table confounds) are fixed, this one is not.

## The problem

`REF_STATS_REF` counts refreshes since reset and never stops, so a host-
bracketed delta measures the HOST's UART round trips, not the workload window.
Measured: a 186 us window returned a raw delta of 61446 — 479 ms implied,
**2584x** the window.

The command counters do not have this problem, because nothing issues DRAM
commands while the host is idle. Refresh is the exception precisely because it
is autonomous.

## Current state

Worked around host-side in 71c4fb030: `pumice_char` reports
`window_cycles / tREFI` alongside the raw delta and flags contamination, and
`refs_are_wall_clock()` tells a caller when the number is untrustworthy. That
is enough to stop a wrong number being quoted; it is not enough to measure
axis 3.

## What a fix looks like

A windowed or clearable refresh counter: either a second counter with a
host-writable clear, or a snapshot pair the host can difference atomically.
The other `*_STATS` counters are free-running by design and should stay that
way — this is specifically about the one counter that advances with no
workload.

Until then, **axis 3 (refresh) numbers are estimates.** Any table quoting them
should say so.

Related: [[TASK-002]] (the campaign that found it), [[TASK-001]] (closed
umbrella).


## 2026-09-25 — FIXED. The counter is measured, not estimated.

**Not a window register.** Every arming/clearing/snapshot design needs a host
WRITE, and `RegisterMap.walk()` writes every reachable register — so any of
them could be fired by a routine register walk. They also all leave the
arm-to-workload-start gap contaminated.

**What landed instead: count refreshes that fired WITH WORK PENDING.**

    if (w_is_ref) begin
        stat_ref_o <= stat_ref_o + 32'h1;
        if (demand_i) stat_ref_busy_o <= stat_ref_busy_o + 32'h1;
    end

`demand_i` is `(|rd_sch_valid_i || |wr_sch_valid_i)` — a signal the scheduler
already computed for the refresh controller, so nothing new was invented.

Three properties, in the order that decided the design:

1. **Contamination-free by construction.** The CAMs are empty while the host is
   idle between reads, so UART round-trip time cannot be counted. No arming, no
   window, no snapshot pair, no second read.
2. **No write trigger**, so `RegisterMap.walk()` cannot fire it.
3. **It is the number axis 3 wants.** A refresh during idle costs the workload
   nothing; one during traffic costs bandwidth. "Refreshes that took a command
   slot from pending work" is more meaningful than "refreshes per unit time" —
   which is all the tREFI estimate could ever have been.

New CSR `REF_STATS_REF_BUSY @ 0x17C`. `REF_STATS_REF` keeps its free-running
semantics for absolute accounting, with its description corrected to say so.

**Host:** `PageStats.refs_busy`; `refs_in_window()` returns the MEASURED value
when present and falls back to the tREFI estimate for older bitstreams, and
`refs_are_wall_clock()` returns False for a measured count (it cannot include
host idle time). Both paths verified.

**Mutation-proven non-vacuous**, which is the part that matters — a counter
that reads zero and a counter that is stuck read the same in a passing test.
`refresh_bubbles` is the one place refreshes fire under live traffic, so the
assertion lives there:

    normal              refresh_bubbles passes; ref_busy > 0, ref_busy <= ref_all
    demand_i forced 0   FAILS: "27 refreshes issued under a saturating write
                        stream but REF_STATS_REF_BUSY counted ZERO with work
                        pending. The demand gate is stuck low, so every
                        refresh-cost number derived from it would read as free."

Verified: component gate COMP_RC=0, 0 FAILED, 188 passed at BOTH geometries;
char board gate CHAR_RC=0, 216 passed 2 xfailed; check_rdl_regen.py rc=0.

**Board note:** this is a new CSR, so silicon cannot read it until the next
bitstream. Against the current bitstream the host falls back to the tREFI
estimate — correct, but TASK-002's refresh axis stays ESTIMATED until a rebuild.

**Self-inflicted, recorded because it is the third instance tonight:** adding
`stat_ref_busy_o` to `pumice_core` broke the core TB with PINMISSING and failed
the gate at 18 tests. Adding a port breaks every instantiator; the fix is to
enumerate them all, not to patch the one that failed. (`pumice_top_geared` was
safe — it instantiates `pumice_top`, which binds the counter internally.)
