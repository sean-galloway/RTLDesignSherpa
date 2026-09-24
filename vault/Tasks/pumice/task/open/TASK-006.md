# TASK-006: no stall-cause attribution, so the overhead breakdown cannot be published
> **Was `PUMICE-035` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** open 2026-09-14  **Priority:** P2 — blocks a documented reporting gap

The bus meters classify every cycle into productive / backpressure / starvation
/ idle. That says the controller did not accept a beat; it does not say **why**.
So the natural and most useful line of a characterization report -- the missing
percent split into refresh, activate/precharge, bus turnaround and
first-transaction latency -- cannot be produced from anything the design
currently exposes.

`docs/DDR2_BANDWIDTH_MEASUREMENT.md` §5 states this explicitly and leaves the
table out rather than printing a plausible split. That is the right call for
now and a poor permanent answer: every reader of a bandwidth number wants to
know where the rest went.

**What would close it:** a small set of counters in the scheduler attributing
each stalled cycle to the timing constraint that caused it -- tRCD, tRP, tRFC,
tWTR/tRTW, or "no command ready". Four or five counters and a CSR window. The
existing meters already prove the window discipline works; this is the same
pattern one level deeper.

**Why it is P2 and not P1:** the direction is already recoverable from the
buckets we have (backpressure means DRAM-bound, starvation means
requester-bound), which is enough to choose what to fix. The attribution makes
the report complete, not the debugging possible.

---


## 2026-09-24 — IMPLEMENTED; the breakdown exists

Seven counters in `pumice_cmd_arbiter`, plumbed scheduler -> core -> top, read
through new CSRs at 0x160-0x178, surfaced in `summarize()` and the CHAR_DUMP.

**The design point that makes it checkable: the buckets are EXCLUSIVE.** Every
stalled cycle lands in exactly one, so the seven sum to the stalled-cycle count.
That is deliberate -- a cause the RTL forgot to classify inflates a neighbour
instead of vanishing, so the total is a cross-check on the attribution itself
rather than a convenience. Priority is causal:

    bp          a command was picked and the DFI refused it  (not a scheduling stall)
    refresh     refresh pending/draining owns the bus        (outranks timers it resets)
    noreq       both CAMs empty                              (claimed ONLY when truly empty,
                                                              so it cannot absorb a timer stall)
    turnaround  tWTR / tRTW
    tccd        column-to-column spacing
    actlimit    tFAW / tRRD                                  (global, outranks per-bank)
    banktimer   tRCD / tRP / tRAS on the target bank

Free-running like the PAGE/SCHED/REF counters -- no clear bit, read as a
before/after delta. `StallStats` in pumice_char carries `.split()`,
`.dram_bound` and `.total`.

**Measured in sim at board geometry (paging_grade, 8 points):**

```
RD stalls: total=34669 noreq=99.5% refresh=0.4% turnaround=0.1% \
           banktimer=0.0% actlimit=0.0% bp=0.0% tccd=0.0%   dram_bound=0.5%
```

Physically sensible and immediately useful: at sim's small transaction counts
the engines idle between bursts, so `noreq` dominates at 98-99.5% and
`dram_bound` is 0.4-1.7%. That is the char suite's existing
"observation-latency-dominated at this run size" caveat, now QUANTIFIED rather
than asserted. The one real differentiation across configs is close-page
showing `turnaround=1.3%` against open-page's `0.1%`, which is the direction
the policies predict.

**Not yet on silicon.** The counters are new RTL, so the 2026-09-21 bitstream
reads them as zero -- and the host correctly prints nothing rather than a row
of 0.0% that would read as "no stalls". A board breakdown needs a rebuild;
until then the numbers above are sim-only, where `noreq` will dominate for the
reason given and the interesting split will only appear under a saturating
board workload.

**Gates:** pumice component 188 passed at BOTH geometries; char board gate green.

**What would still improve it:** `banktimer` lumps tRCD/tRP/tRAS together. The
per-bank ready signals are already in the arbiter, so splitting them is three
more counters and no new plumbing -- worth doing if a board run shows that
bucket is large.
