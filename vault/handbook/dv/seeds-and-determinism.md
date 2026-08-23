---
title: Seeds and determinism
summary: Random seed per run, recorded and overridable. There is no such thing as a failing seed - a varying failure count is new traffic finding real bugs.
---

# Seeds and determinism

**Run a fresh random seed every time. Record it. Never pin it** - except where
the test's output is a committed artifact.

    'SEED': os.environ.get('SEED', str(random.randint(0, 100000)))   # wrapper
    self.SEED = self.convert_to_int(os.environ.get('SEED', '12345')) # TB
    random.seed(self.SEED); self.log.info(f"... seed: {self.SEED}")

New traffic every run is the point: it is what finds defects that a frozen
trajectory never reaches. The seed is logged and honored from the environment
so any failure replays with `SEED=<n>`, which is all reproducibility requires.

## There is no such thing as a failing seed (Sean, 2026-07-31)

This note previously said the opposite, and the reasoning was wrong in a way
worth keeping visible.

*The case: a monitor suite failed "3 of 12" on one run and "6 of 12" on the
next. That was read as flakiness - unreproducible noise that made good fixes
look like regressions - and the conclusion drawn was to pin a default seed, and
to lock every seed that had ever failed into a `FAILING_SEEDS` corpus that runs
forever after.*

**The failures were real monitor bugs.** The random seeds were generating new
traffic, the new traffic was reaching real defects, and the varying count was
the exploration working - more bugs exposed on the second run than the first.
Pinning the seed would have made the failures stop appearing without fixing
anything, which is the worst possible outcome: it converts a bug detector into
a silent pass.

So a varying failure count across runs is **signal, not noise**. The response
is to fix what the traffic found, never to freeze the traffic.

**And a locked seed is not regression coverage.** A seed reproduces a scenario
only against an unchanged everything-else - same RTL, same BFM, same test, same
delay profiles. Any change to any of those and the "known-failing" seed is
simply a fresh random draw that no longer reaches the condition it was locked
for, and nothing announces that it stopped. The corpus keeps passing and means
nothing.

**What to do instead when random traffic finds a bug:** extract the SCENARIO -
the interleaving, the outstanding-count, the back-pressure shape that actually
triggered it - and write it as a directed test that reproduces the condition by
construction. That is coverage a code change cannot silently void. Then keep
drawing fresh seeds to find the next one. See [[randomization]] for why
randomized traffic alone proves nothing about fairness or arbitration, which is
the same argument from the other side.

## The cocotb seed, xdist clustering, and the binary (CONV-002, 2026-08-23)

The repo's `SEED` convention above is the WRAPPER's seed. cocotb has its own:
it seeds Python's global `random` at sim start with `RANDOM_SEED` from the
environment, or `int(time.time())` when unset — and the GAXI BFM randomizers
draw from that global stream. Three mechanics follow, each measured while
running down the converters' "intermittent" failures:

- **Same-second launches share a seed.** Under `pytest -n 16`, every test
  spawned in the same wall-clock second gets the identical time seed. One bad
  seed then fails four+ configs in one sweep (all four dnsize failures in one
  run shared seed 1787502707), while a solo retry loop draws a fresh seed per
  second and can go hundreds of runs green. That asymmetry is exactly what
  "fails in CI, passes on my machine" looks like — it is still deterministic.
- **Replay = `RANDOM_SEED=<n>` from the failing log's "Seeding Python random
  module with n" line** — but only against the SAME compiled binary. The
  everything-else that a seed replay requires unchanged INCLUDES the Verilator
  codegen: any rebuild, including toggling `WAVES=1`, reorders evaluation
  enough to shift which seeds reach the condition. A failure that "goes away
  with waves on" has not gone away; you rebuilt the binary.
- **Kill your BFMs between sub-tests.** Each cocotb sub-test that constructs
  a fresh GAXI master/slave pair on the same DUT leaves the previous pair's
  cocotb-bus BusMonitor coroutines RUNNING — by the fourth sub-test, four
  slaves drive the same ready signal with independent randomizers,
  last-deposit-wins. That is both a stimulus corruption and the reason
  outcomes become sensitive to evaluation order at all. Framework-level
  teardown is RDS-DV work; until it exists, reuse one component set across
  sub-tests instead of stacking.

## Pin only a committed artifact

Wavedrom generators produce the wave JSON the docs embed. A random seed there
means the committed diagram churns for no reason, so their default is pinned
(still overridable with `SEED=`). That is the whole exemption list.

## What "SEED recorded" actually audits

The checklist item is meaningless for a test that does not randomize, and the
real defect has two shapes:

- a TB that calls `random.randint` with nothing ever calling `random.seed` -
  the failing pattern dies with the process (`dataint_ecc_hamming_secded_tb`,
  `glitch_free_n_dff_arn_tb`, both fixed 2026-07-31);
- **a wrapper that passes a SEED nobody consumes**, which is worse because it
  reads as compliant. Grep for `random.seed(` in the TB chain, not for `SEED`
  in the wrapper.

Measured for val/common (2026-07-31): 36 of 48 randomize and seed correctly, 2
randomized unseeded, 5 have no randomness at all (nothing to seed - do not
"fix" these), 4 are wavedrom, and `test_shifter_lfsr.py` has a literal
`seed = 0x01` that is an RTL LFSR seed value, not a PRNG seed. Half of what a
naive grep flags is not a finding.

## Outstanding cleanup

`val/amba/test_axi_monitor_trans_mgr.py` still implements the corpus model this
note used to prescribe: `DEFAULT_SEED`, a `FAILING_SEEDS` table of six seeds
harvested 2026-07-21, and `MONITOR_SEED_SWEEP`. The stream tests carry the same
"a sweep that discards the failing seed is worth nothing" line. Both want
rewriting to random-by-default, with the completion-count scenario those seeds
were locked for turned into a directed test. Tracked for the amba pass.

Companion rule, unaffected: phase-boundary drain windows must out-wait the
BFM's max ready delay AND check the bus idle - a 30-cycle window racing a
30-cycle ready delay produces its own "3 or 5 completions, expected 4" class
that is genuinely a test bug. Do not let that pattern be used to explain away a
real one; tell them apart by fixing the window and seeing whether the failures
survive.
