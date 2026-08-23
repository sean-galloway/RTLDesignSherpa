<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# converters — Open (accepted, not started)

---

## CONV-001 — axi_data_dnsize burst-tracking LAST: early LAST on TRACK_BURSTS
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

**Triage data (2026-08-23, shared-arc regression sweep):** with the asserts
on, `test_axi_data_upsize` is INTERMITTENT, not solid-red: two full-directory
`-n16` sweeps failed different param sets (4x uart_axil_bridge, then 2x
upsize), a serial rerun of all 4 uart params passed 765s clean, and a solo
upsize loop failed on iteration 1 (seed 1787443637, "Transaction 1: Expected
1 wide beat, got 0" at 5510ns) -- then PASSED when replayed with
RANDOM_SEED=1787443637. So the failure is stimulus-order/timing dependent
and NOT reproducible from the cocotb seed alone (something in the TB or BFM
draws randomness outside the seeded stream -- worth fixing first, since
un-replayable failures make the RTL-vs-test call expensive). The TB polls
`width_ratio*8+100` clocks for the wide beat; whether the GAXI master's
randomized pacing can legitimately exceed that window is the first thing to
settle.

**Work:**
- [ ] Make a failure replayable (find the unseeded randomness) BEFORE
      diagnosing RTL-vs-test.
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

## CONV-003 — dnsize DUAL buffer drops beats under backpressure
**Status:** open 2026-08-23
**Priority:** P1 — possible RTL defect in the dual-buffer path

Split out of [[CONV-002]] once the test-side faults were cleared.

`test_backpressure` on `axi_data_dnsize` reports **40 expected, 36 received**
on DUAL configurations (`128to32_wstrb_slice_simple_DUAL` and siblings).
Single-buffer configurations pass the same scenario.

This is not a timing race. The scenario now polls for the tail
(`expected * 4 + 200` cycles) before counting, so the four beats are missing,
not late.

**Work:**
- [ ] Confirm against the RTL whether the dual-buffer path can drop a beat
      when the narrow side stalls, or whether the scenario mis-drives it.
- [ ] Any RTL defect gets a test that fails before the fix, per the standing
      rule.
- [ ] Assert the verdict once green (currently gated with a pointer here).
