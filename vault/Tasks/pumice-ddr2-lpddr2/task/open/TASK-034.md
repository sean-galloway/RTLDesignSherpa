# TASK-034: every JEDEC window is enforced one MC cycle longer than programmed

**Priority:** P3 — it is CONSERVATIVE, so nothing is at risk; it costs bandwidth,
and the cost is unmeasured.
**Status:** open 2026-09-28 — **narrowed the same day: the documentation half is
DONE (option 1 below), and all that remains is the board experiment for option
2.** Nothing in this item can progress without board time.
**Owner:** TBD
**Found by:** `formal/pumice/{bank_timer,global_timers}` — measured, not inferred.
**Related:** [[ISSUE-018]] (the other readiness off-by-one in the same block,
fixed), [[ISSUE-019]] (the arbiter checks tFAW/tRRD two stages before the fire --
independent of this, and it is the reason the empirical guards are what they are)

## The measurement

A window programmed to N is enforced as **N+1** MC cycles of spacing. The counter
is loaded with N and the gate opens the cycle after it would reach zero.

Proved for all ten enforced windows, in both timing blocks:

| Block | Windows | Bound |
|---|---|---|
| `bank_timer` | tRC, tRP, tRCD, tRAS, tRTP, tWR | N+1 |
| `global_timers` | tRRD, tCCD, tWTR, tRTW | N+1 |

It is exactly N+1 and tight: the same assertions with `+ 2` FAIL on every window,
and cover statements reach the gate opening at exactly N+1
(`c_trc_tight`, `c_tras_tight`, `c_trrd_tight`, `c_tccd_tight`). The bound
assertions are now permanent (`a_*_bound_n1`) so the convention cannot change
silently in either direction.

## Why it reaches silicon as a real extra cycle

Nothing compensates for it at any level:

* **The RDL says nothing.** The field descriptions are bare — `desc = "tRRD"`,
  `desc = "tCCD"` — with no units and no statement of whether the value is
  blocking cycles or command spacing.
* **The host writes raw JEDEC-derived cycle counts**, with no `-1`.
  `build-perf/host/pumice_device.py` computes e.g. `tCCD=ck(DDR2_CK_MIN["tCCD"])`,
  `tRRD=ns_or_ck("tRRD")`, `tRCD=ns(part["tRCD"])`.

So on the board every one of those ten windows is one MC cycle (13.3 ns at
75 MHz) longer than JEDEC requires.

## The decision

Three options, and the third is the trap.

1. **Document and keep it.** ~~Say in the RDL and the MAS that the field is
   BLOCKING CYCLES, enforced as N+1 spacing.~~ **DONE 2026-09-28**, in four
   places that previously said nothing about units at all:

   * `rtl/macro/pumice_csr.rdl` -- all ten enforced fields now read
     "MC cycles to block; spacing enforced is N+1", and the register holding the
     core windows carries the convention in full. Regenerated through
     `bin/peakrdl_generate.py` (both invocations); only the generated DOCS
     changed, so the regblock RTL and the regmap are byte-identical and no
     simulation behaviour moved.
   * `docs/pumice_mas/ch04_apb_config/03_runtime_overrides.md` -- a section
     saying what a timing value means, with the instruction a programmer needs:
     write the JEDEC value from the datasheet, do NOT subtract one.
   * `docs/pumice_has/ch06_integration/03_csr_map.md` -- units on the field rows.
   * both formal wrappers -- `a_*_bound_n1` properties, so the convention is
     executable and cannot drift silently in either direction.
2. **Recover the cycle in the RTL.** `ok_nxt = event ? (reload <= 1) : (c <= 2)`
   makes N mean exactly N. One cycle back on all ten windows. This is the
   interesting option and it needs the experiment below.
3. **Compensate in the host** (`ck(x) - 1`). Do NOT. The CSR would stop reading
   as the JEDEC value, nine host scripts and every sequence would need to agree,
   and the next reader of a register dump is misled.

## What makes option 2 a board experiment, not a code change

**The empirical guards were tuned WITH this extra cycle present**, so removing it
eats margin that was bought with measurements.

`pumice_device.py` derives `tRTW = max(ck(cl + half_bl + 2 - wl), rd_window_mc)`
where `rd_window_mc` includes `rtw_guard`, and its comment says outright:

> `rtw_guard` is EMPIRICAL, covering the arbiter's registered turnaround ok. It
> is 6, NOT 4. 4 (tRTW=18) clears gaps 13 and 15 but leaves an INTERMITTENT 2-6
> beat residue at gap 14 — 5 of 6 reps, and 8 of 10 in a separate run.

Two things follow. First, part of that guard was covering the very
stale-readiness hazard that [[ISSUE-018]] has now fixed, so the guard may already
be larger than needed — a separate, independent reason to re-measure. Second, an
intermittent failure at 20% reproduction rate is invisible to a single-pass
sweep, which is how an earlier "0 of 192 clean" result was mistaken for closure.

**The experiment, and it must be run in this order:**

1. With the tree as it stands (ISSUE-018 fixed, N+1 enforcement), re-run the
   bank/gap matrix and re-derive the minimum safe `rtw_guard`. **Six reps per
   point minimum** — a point that is clean 20% of the time passes a one-rep sweep
   one time in five. Expect the guard to come down; that alone is bandwidth.
2. Only then change the enforcement to exact-N and repeat, including gap 14
   specifically.
3. Report measured MB/s against the 600 MB/s theoretical peak for both, read and
   write, so the gain is stated rather than assumed.

If step 1 already recovers the cycle's worth of bandwidth through a smaller
guard, step 2 may not be worth its risk at all.

---

## Board campaign 2026-09-29 -- the prize is measured; the safety case is NOT

Nexys A7 (serial 210292BFA3EE) programmed with the ISSUE-018-fixed bitstream
(post-physopt WNS +0.031). `init` PASS, geometry confirmed from the hardware:
`dfi_rate=2 gear=1 bl=4 row=13 bank=6 axi=64b beat=32b dev=16b clk=75.00MHz`.
Workload: the 1+1 concurrent read+write point on disjoint banks, FAM_INCREMENTAL,
2000 x 64 B bursts per engine -- the point TASK-034 named, because it has the
LEAST overlap and is the one that historically failed.

### Step 1 as written: no failures anywhere from guard 6 down to 2

90 points, six reps each, gaps 13/14/15, `rtw_guard` 6 -> 2 (tRTW 20 -> 16):
**0 mismatched beats everywhere**, and the throughput did not move by more than
0.1 MB/s across the whole range (gap 14: 123.2 MB/s at every guard).

Taken at face value that says "drop the guard". **It does not, and the reason is
the control.**

### The negative control FAILED, so step 1 is unanswered

tRTW = 8 -- the value the OLD buggy formula derived, which the RTL comment
records as failing gaps 13 and 15 "exactly as they had before the fix" -- is
**0/6 clean at all three gaps**. The historical failure does not reproduce.

Pushed further: tRTW = **3**, physically impossible for a CL=3 / BL=4 DDR2 part
(a read owns DQ far longer than three MC cycles), is **also 0/6 clean**.

So this stimulus cannot detect a read-to-write turnaround violation AT ALL. The
clean sweep above is therefore evidence about the workload, not about safety, and
**the guard must not be lowered on the strength of it**. A sweep that passes at a
setting that cannot possibly be safe has demonstrated only that it is not looking
at the thing it is named after.

Why it is blind is worth recording: writers and readers start on disjoint banks
and the reader gap is 13-15 cycles, so genuine back-to-back RD->WR on the shared
DQ bus is rare in this pattern. The historical failure needed an interleaving
this point does not produce.

### What the campaign DID establish: the prize, and it is large

Sweeping tRTW down at gap 14 finds a CLIFF, not a curve:

| tRTW | MB/s | % of 600 MB/s peak |
|---:|---:|---:|
| 20 (shipping) | 123.2 | 20.5% |
| 16 | 123.2 | 20.5% |
| 13 | 123.2 | 20.5% |
| 12 | 123.2 | 20.5% |
| **11** | **217.1** | **36.2%** |
| 10 | 217.8 | 36.3% |
| 9 | 217.7 | 36.3% |
| 8 | 217.4 | 36.2% |
| 3 | 217.9 | 36.3% |

One cycle -- 12 to 11 -- nearly doubles this workload's throughput (+76%), and
nothing below 11 buys anything more. That is a quantization boundary, not a
gradual cost, and it is worth understanding on its own: something takes an extra
slot at tRTW >= 12 and fits at <= 11.

Shipping tRTW is 20, so this workload is leaving ~76% on the table IF 11 is safe.
That is a far bigger prize than the one cycle this task was filed about, and it
raises the value of doing the experiment properly rather than lowering the case
for it.

### What a valid experiment needs (this is now the task)

1. **A stimulus that actually stresses RD->WR turnaround** -- interleaved reads
   and writes to the SAME bank, or a pattern that forces bus turnaround every few
   commands, rather than disjoint banks with a 13-15 cycle gap.
2. **Validated by a negative control before any conclusion is drawn**: it must
   FAIL at tRTW = 3. If it does not, it is not measuring the turnaround and no
   result from it means anything. That check costs one run and it is what this
   campaign was missing.
3. Only then sweep the guard down, six reps per point, and find the minimum that
   is clean.
4. Then, separately, the N+1 question this task was filed about -- which is a
   much smaller effect than the tRTW cliff and should be measured after it.

The `rtw_guard` stays at 6. Nothing about the shipping configuration changed, and
the board was restored to tRTW = 20 after the campaign.
