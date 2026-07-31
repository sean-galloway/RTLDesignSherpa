---
title: Seeds and determinism
summary: Pin seeds always; explore deliberately; lock every failing seed.
---

# Seeds and determinism

cocotb self-seeds RANDOM_SEED from the clock when unset - results become
unreproducible, failures look like noise, and good fixes nearly get
reverted (this happened: a monitor suite failed "3 of 12" then "6 of 12"
on consecutive runs; a real RTL fix was almost blamed).

Pattern (reference: val/amba/test_axi_monitor_trans_mgr.py, stream's
STREAM_SEED/STREAM_SEED_COUNT):
- Default runs pin RANDOM_SEED + COCOTB_RANDOM_SEED (deterministic corpus).
- Every seed that EVER failed gets locked into a FAILING_SEEDS corpus and
  runs forever after (regression can't silently lose it).
- Exploration is a deliberate mode (MONITOR_SEED_RANDOM=k /
  STREAM_SEED_COUNT=n): fresh derived seeds, seed visible in the test ID so
  any failure is reproducible with SEED=<n>.
- A sweep that discards its failing seed is worth nothing.

Companion rule: phase-boundary drain windows must out-wait the BFM's max
ready delay AND check the bus idle - the "3 or 5 completions, expected 4"
class was a 30-cycle window racing a 30-cycle ready delay, not RTL.

## Random per run, recorded, overridable (Sean, 2026-07-31)

**"None of the tests except for wavedrom should have a fixed seed."** That
reads as the opposite of the pinned-corpus pattern above, and it is not - the
two settle on the same mechanism, from different directions:

    'SEED': os.environ.get('SEED', str(random.randint(0, 100000)))   # wrapper
    self.SEED = self.convert_to_int(os.environ.get('SEED', '12345')) # TB
    random.seed(self.SEED); self.log.info(f"... seed: {self.SEED}")

The default is a NEW seed each run, so the suite keeps exploring instead of
re-running one corpus forever. The seed is recorded in the log and honored
from the environment, so any failure replays with `SEED=<n>` - which is the
property the monitor-suite failure above actually needed. Pinning is for a
FAILING-seed corpus (a seed that ever failed runs forever after) and for
tests whose output is a committed artifact, not for the default run.

**Wavedrom generators pin.** Their output is the wave JSON the docs embed, so
a random seed per run means the committed diagram churns for no reason.

**What "SEED recorded" actually audits.** The checklist item is meaningless
for a test that does not randomize, and the real defect has two shapes:

- a TB that calls `random.randint` with nothing ever calling `random.seed` -
  the failing pattern dies with the process (`dataint_ecc_hamming_secded_tb`,
  `glitch_free_n_dff_arn_tb`, both fixed 2026-07-31);
- **a wrapper that passes a SEED nobody consumes**, which is worse because it
  reads as compliant. Grep for `random.seed(` in the TB chain, not for `SEED`
  in the wrapper.

Measured for val/common at the time: 36 of 48 randomize and seed correctly,
2 randomized unseeded, 5 have no randomness at all (nothing to seed - do not
"fix" these), 4 are wavedrom, and 1 (`test_shifter_lfsr.py`) has a literal
`seed = 0x01` that is an RTL LFSR seed value, not a PRNG seed. Three of those
last six look like findings to a naive grep and are not.
