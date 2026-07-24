---
title: Escape analysis
summary: The RTL defects that got past a green test suite, and the specific test-gap that let each one through.
---

# Escape analysis

Every bug below existed in `rtl/` while its own test suite was green. The point
of this note is not the bugs - they are fixed - it is the **shape of the gap**
that let each one through, because those shapes recur.

All of these were surfaced by *documentation* review ([[kimi-review-rounds]]),
not by testing. That is itself the headline: a reviewer forced to reconcile the
doc against the RTL line by line found what the testbench could not.

## The defects, and what let each one through

### 1. `arbiter_round_robin_simple` - rotated the wrong way, starved half its clients

Rotating the request vector LEFT by `last+1` maps rotated bit j to agent
`(j - s) mod N`. That is a **reflection**, not a rotation - and a reflection
composed with itself is the identity, so the pointer oscillated between two
positions. N=4, all four requesting: grants went `0,3,0,3,...` forever. Two of
four agents were never served. Measured before/after under Verilator:
`10/0/0/10` -> `5/5/5/5`.

**Four independent escapes, any one of which would have caught it:**

- **The threshold was set so loose it passed the bug.** `min_fairness_threshold
  = 0.3` on a 4-client arbiter. Jain's index for k of n clients served equally
  is k/n, so 0.3 passes with **two clients completely starved** (index 0.5).
  The test printed `fairness: 0.500` and PASSED. A threshold that cannot fail
  the defect it names is decoration.
- **The stimulus never reached the stressing corner.** No `ArbiterMaster`
  profile asserts all clients continuously - even `fast` leaves a 1-3 cycle
  gap. The arbiter was therefore never forced to walk its rotation, and the
  *request pattern* decided who got served rather than the arbiter. See
  [[randomization]]: randomized traffic does not prove fairness.
- **The checker whose name promised this exact catch is a stub.**
  `ArbiterCompliance.analyze_round_robin_compliance()` returns a hardcoded
  `rr_efficiency: 1.0` regardless of the observed grant sequence. A clean report
  from it is not evidence of anything.
- **No downstream pressure.** The module has zero instantiators in the repo, so
  no integration test would trip over it. It is a library module someone could
  have picked up - which is exactly how it survived.

### 2. `clock_pulse.sv` - counter as wide as the period

`r_counter` was declared `[WIDTH-1:0]`, but WIDTH is the pulse PERIOD. The
doc's own 1 Hz heartbeat example (`WIDTH=100_000_000`) would infer ~100 million
flip-flops and not synthesize.

**Escape:** *functionally correct in simulation.* An over-wide counter counts
perfectly well. Only synthesis or an area/resource check catches this class, and
the flow gates on behaviour, not on inferred resources. Nothing in the test path
has an opinion about flop count.

### 3. `clock_gate_ctrl.sv` - port list forward-references a body localparam

The ANSI port list used `[N-1:0]` where `N` is a localparam declared *after* the
port list. Strict-LRM tools reject it.

**Escape:** *one simulator's tolerance became the spec.* Verilator accepted it,
and Verilator is what the repo runs. Nothing checks LRM strictness, so
"compiles here" silently stood in for "is legal SystemVerilog".

### 4. `pwm.sv` - emitted N+1 periods for `repeat_count = N`

`w_all_repeats_done` compared `r_repeat_value` against `local_repeat` while that
register increments on the same period-boundary cycle. `repeat=1` ("single
pulse") produced two.

**Escape:** recorded plainly at fix time - *the test waits for `done` but never
counts periods.* It asserted that the thing **finished**, not that it did the
**right amount**. This is the most repeatable gap on the list.

### 5. Four RTL header comments that described a different module

- `sort.sv` claimed ascending / smallest at LSB; the compare-swap sorts
  DESCENDING with the largest at the LSB.
- `sync_pulse.sv` advertised a toggle-synchronized-back-to-source ready path
  with **no port and no logic**, plus two inconsistent min-spacing figures.
- `fifo_sync.sv` / `fifo_async.sv` advertised sim-only overflow/underflow
  `$display` checks the bodies never contained.

**Escape:** *comments do not execute.* Nothing in any flow reads them, so they
drift from the code the moment either changes, and only a human (or a reviewer
model) reading RTL and doc side by side will notice.

## The recurring shapes

Worth checking any new test against directly:

| Shape | Ask |
|---|---|
| Asserts completion, not quantity | Does it count, or just wait for `done`? |
| Threshold looser than the defect | Can this threshold fail the bug it names? Compute the metric for the broken case. |
| Stimulus never reaches the corner | Does any profile actually saturate / back-pressure / fill? |
| The checker is a stub | Has anyone read the checker's body, or just its name? |
| Simulation-only signoff | What classes (area, LRM strictness, CDC) does simulation structurally not see? |
| No instantiators | Who would notice if this library module were wrong? |
| Comments | Nothing executes them. |

## What is still unexamined

The common area is integrated. Across the un-integrated units there remain
**38 CONFIRMED findings that cite `rtl/*.sv`** and are therefore candidate RTL
defects, not doc drift:

| Unit | CONFIRMED citing RTL |
|---|---|
| shared_part_02 | 7 |
| monitor_part_01 (round_3) | 8 |
| apb | 6 |
| math_part_01/02/03 | 4 / 5 / 4 |
| axi4_part_01/02 | 4 / 2 |
| cdc_part_01 | 3 |
| axis4 | 1 |

Tracked as DOCREV-001. Triage doc-fix vs RTL-fix per finding - the headline
lies in both directions.

Related: [[kimi-review-rounds]], [[randomization]], [[running-regressions]],
[[coverage]].
