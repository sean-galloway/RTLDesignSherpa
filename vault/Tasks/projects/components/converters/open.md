<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# converters — Open (accepted, not started)

---

## CONV-001 — axi_data_dnsize burst-tracking LAST: early LAST on TRACK_BURSTS
**Status:** RESOLVED as a test fault 2026-08-23 — mechanism proven correct; residual flake folded into [[CONV-003]]

**Resolution.** The TRACK_BURSTS LAST mechanism is correct.
`test_burst_len_drives_last` frames a burst and holds `wide_last` LOW, so
the counter is the only thing that can assert LAST -- it lands exactly on
`burst_len`, on all 16 configurations including DUAL. That test is asserted
and green.

Everything that looked like an RTL defect was test-side, in three layers:
the signal mapping (LAST never bound, so it read False always), the framing
units (wide beats where the RTL counts narrow), and fixed waits that let a
previous burst's tail be read as the next burst's beat 0. All fixed.

`test_burst_tracking` itself remains intermittently red on DUAL and is left
unasserted -- but the failure it shows is a DUAL-buffer symptom shared with
CONV-003, not a burst-tracking one. Tracking it there.

**Superseded detail below.**

**Status:** open 2026-08-22; narrowed 2026-08-23
**Priority:** P1 — either a broken feature or a broken test, and neither is known

**Update 2026-08-23.** Two of the three suspects are eliminated. The signal
mapping was broken (`field_last_sig` never resolved, so LAST read as 0
regardless of what the RTL did) and the framing units were wrong (wide beats
where the RTL counts narrow). Both are fixed. With LAST actually observable,
the symptom changed from "LAST never asserts" to **"LAST asserts early"** --
`Burst 2, beat 3: expected False, got True`, beat 3 being the end of the
first WIDE beat at ratio 4. That is a real behavioural question about the
counter path, not an artefact. Everything below still applies.

`test_axi_data_dnsize.py` calls the scenario without checking it:

```python
await tb.test_burst_tracking(num_bursts=15)     # return value discarded
```

`test_burst_tracking` returns False on a LAST mismatch. Nothing reads it, so
the scenario has been reporting a failure into the void. All 16 configs show
green.

**Assert it and 6 configs go red** — every `TRACK_BURSTS=1` parametrization.

### What is established

`burst_len` is **narrow beats − 1**, not wide. In TRACK_BURSTS mode
`narrow_last` is driven *only* by the counter — `wide_last` plays no part:

```systemverilog
assign narrow_last = r_wide_buffered && r_burst_active &&
                     (r_slave_beat_count + 1'b1 >= r_slave_total_beats);
```

and `r_slave_beat_count` increments on every narrow beat sent, with
`r_slave_total_beats = burst_len + 1`. The scenario frames its bursts in
*wide* beats (`start_burst(burst_len_beats - 1)`), which is a factor of
`WIDTH_RATIO` short, so LAST should fire early.

### What is NOT established

Correcting the framing to narrow beats does not fix it. With
`burst_len = 7` for an 8-narrow-beat burst, LAST is still absent on beat 7 —
the beat where `(7 + 1) >= 8` should assert it. So there is a second effect
beyond the units error, and it is unresolved. Candidates: `r_burst_active`
clearing early, or the scenario's `wide_last` interacting with the counter
path.

### Why the suite is still green in the tree

Asserting the result turns 6 configs red without diagnosing anything. The
assert is left off with a pointer to this task. **The silent discard is
itself the defect** — fix that as part of this task, not separately.

### Related, already done

The throughput measurement added alongside this
(`measure_throughput`, `measure_burst_throughput`) works and is asserted.
Simple mode sustains 0.992 beats/cycle; TRACK_BURSTS ~0.914–0.941 with
narrow-beat framing, consistent with one bubble per burst boundary.

**Work:**
- [ ] Determine whether the TRACK_BURSTS LAST path is broken or the scenario
      mis-drives it. Drive a framed burst with `wide_last` held low — LAST can
      then only come from the counter (`test_burst_len_drives_last` in the TB
      does this and is currently unwired).
- [ ] If RTL: fix, with the failing test as the gate.
- [ ] If test: fix the framing units and the expectation.
- [ ] Either way, assert the return value so it can never silently fail again.
- [ ] Sweep for the same pattern: other scenarios whose result is discarded.


---

## CONV-002 — the dnsize and upsize test files are decorative: 22/22 configs fail when asserted
**Status:** mostly resolved 2026-08-23 — root cause found, 7 of 9 scenarios now asserted and green
**Priority:** P0 — two primitives have no working verification at all

[[CONV-001]] found one scenario whose result was discarded. Sweeping for the
pattern found that **every** scenario in both width-primitive test files does
it, and that all of them are failing.

| File | Scenarios discarded | Configs |
|---|---|---|
| `test_axi_data_dnsize.py` | 5 (all) | 16 |
| `test_axi_data_upsize.py` | 4 (all) | 6 |
| `test_dnsize_quick.py` | 1 (all) | — |

**Assert the verdicts and 22 of 22 configurations fail.** They report green
today only because nothing reads the return value.

Failures seen on `axi_data_upsize` (32to256_no_sideband):

```
Transaction 0: Expected 1 wide beat, got 0
Transaction 0: Expected wide_last=1 for early termination
Continuous streaming: Expected 30 beats, got 31
```

`basic_accumulation` and `early_last` fail; `backpressure` and
`continuous_streaming` pass. On dnsize, `burst_tracking` fails (that is
CONV-001) and `basic_splitting` logs a data mismatch while still returning
true.

### Why this matters more than the individual failures

`axi_data_upsize` and `axi_data_dnsize` are the primitives underneath
`axi4_dwidth_converter_rd/wr`, which the bridge fabric instantiates. They
have had no effective verification, and the four RTL bugs already found this
round were all in paths whose tests did not check what they claimed.

Whether these are RTL defects or scenario defects is **unknown** and must be
settled one at a time -- the upsize "expected 1 wide beat, got 0" could be
either.

### Do not simply turn the asserts on

22 red configurations diagnose nothing and block everyone. Take one scenario
at a time: assert it, decide RTL-vs-test, fix, keep the assert.

**Triage RESOLVED (2026-08-23, shared-scrub session; supersedes the earlier
"not reproducible from the seed" paragraph, which was wrong):** the failures
are fully DETERMINISTIC per (RANDOM_SEED, compiled binary). Replay recipe:
grep "Seeding Python random module with N" from the failing test's captured
output, then `RANDOM_SEED=N pytest <that test>` -- reproduced dnsize
[512to128_rresp_burst_track_DUAL] identically, twice, against the sweep's own
binary (seeds 1787509080 / 1787510673, matching RNG-state fingerprints). The
earlier "same seed passed on replay" observations were all explained by
REBUILDS between fail and replay: any recompile (including a WAVES=1 toggle)
shifts Verilator codegen and with it the bad-seed set. Sweeps cluster
failures because same-second xdist launches share one time-based seed.
Full mechanics + the stacked-BFM teardown gap (four slaves driving one ready
by sub-test 4 -- RDS-DV work) recorded in
vault/handbook/dv/seeds-and-determinism.md.

**Work:**
- [ ] `axi_data_upsize`: basic_accumulation, early_last -- diagnose and fix.
- [ ] `axi_data_dnsize`: basic_splitting's silent data mismatch; burst
      tracking is CONV-001.
- [ ] Assert every scenario verdict as each one goes green.
- [ ] `bin/review/check_discarded_verdicts.py` reports this class; wire it
      into whatever gate runs the other `bin/review/check_*` scripts.
- [ ] Sweep the rest of the repo -- the tool finds 93 discards overall, most
      of them helpers rather than scenarios, but
      `dmas/stream/.../test_sram_controller_alloc.py:257`
      (`run_full_allocation_test`) is the same shape and is unexamined.


---
