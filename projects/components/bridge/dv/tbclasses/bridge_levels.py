# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""Bridge test levels: the REG_LEVEL grid and the TEST_LEVEL depth, in one place.

HAND-WRITTEN (not generated). Shared by every generated bridge test, the
generated monitor tests, and the hand-written AMBA5 sign-off tests, so the
three levels mean the same thing across the whole suite.

The two knobs are different (handbook: test-runner):

* ``REG_LEVEL`` (GATE|FUNC|FULL, from make/tests.mk) selects the GRID -- how
  many ``test_level`` cells each pytest wrapper expands to. Each wrapper file
  carries its own ``generate_bridge_levels`` (GATE 1 / FUNC 2 / FULL 3), the
  per-file form val/common uses and the level checker verifies.
* ``TEST_LEVEL`` (gate|func|full) sets the DEPTH of one cell -- how many
  offsets, probes, transactions, and whether the slaves push back. The wrapper
  exports it in ``extra_env``; the TB reads it through ``current_level`` and
  scales its work with ``PROFILE``.

Before this module existed neither knob reached the bridge suite: the jinja
template never read REG_LEVEL, never exported TEST_LEVEL, and no TB read it,
so ``make run-all-gate`` and ``make run-all-full`` ran the identical 72 tests
(BRIDGE-007 audit, 2026-09-09).

SEED rides the same path. The repo-root conftest pins ``SEED`` per test node
so a rerun replays the same run; the wrapper forwards it in ``extra_env`` and
``seeded_rng`` turns it into the one ``random.Random`` a TB uses.
"""

import os
import random

LEVELS = ('gate', 'func', 'full')

# Depth profile per level. Every number here is a knob a TB or test reads;
# nothing else in the suite hardcodes a count.
PROFILE = {
    'gate': dict(
        connectivity_offsets=1,   # writes/reads per (master, slave) pair
        probe_pages='boundary',   # slave_probe_pages() mode
        in_page_probes=1,         # of [low, mid, high]
        slave_delay=0,            # response-delay cycles on every slave
        arb_per_master=4,         # concurrent txns per master (arbitration)
        mon_count=128,            # monitor stress reads per phase: the monbus
                                  # err FIFO is 64 deep and the ERR_BP phase
                                  # asserts it SATURATES; at exactly 64 reads
                                  # that is a race against the drain pump
                                  # (11 variants hit 64, mix_d peaked at 58).
                                  # 2x depth makes saturation certain.
        sideband_beats=3,         # AMBA5 sideband/atomic sign-off rounds
        overflow_per_master=20,   # BRIDGE-011: > FIFO_DEPTH in total
        latency_samples=1,
    ),
    'func': dict(
        connectivity_offsets=4,
        probe_pages='boundary',
        in_page_probes=3,
        slave_delay=0,
        arb_per_master=8,
        mon_count=256,
        sideband_beats=8,
        overflow_per_master=40,
        latency_samples=3,
    ),
    'full': dict(
        connectivity_offsets=16,
        probe_pages='seeded',     # boundary pages + every seeded page
        in_page_probes=3,
        slave_delay=24,           # slaves push back: depth builds in the fabric
        arb_per_master=24,
        mon_count=512,
        sideband_beats=24,
        overflow_per_master=64,
        latency_samples=8,
    ),
}


def current_level():
    """The depth this cocotb process runs at, from TEST_LEVEL (default gate)."""
    lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
    return lvl if lvl in LEVELS else 'gate'


def seeded_rng(log=None):
    """One RNG per TB, seeded from SEED, and logged so a failure is reproducible."""
    seed = int(os.environ.get('SEED', '0'))
    if log is not None:
        log.info(f"SEED={seed}  (reproduce with: SEED={seed} pytest <this test>)")
    return seed, random.Random(seed)
