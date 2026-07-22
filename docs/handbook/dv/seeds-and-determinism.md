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
