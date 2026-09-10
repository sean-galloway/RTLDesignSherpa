# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""Bridge test-level DEPTH profile.

The grid (which cells a REG_LEVEL expands to) and the per-cell environment
live in ``TBClasses.shared.test_levels`` -- one implementation for every area,
and the one place that guarantees a wrapper's TEST_LEVEL beats a conftest
stamp (see that module for why cocotb_test makes that necessary). This file
holds only what is specific to the bridge: how much work each depth does.

Every count the suite uses is read from ``PROFILE``; nothing else hardcodes
one. ``current_level()`` and ``seeded_rng()`` are re-exported so a TB has one
import.
"""

import os
import random

from TBClasses.shared.test_levels import LEVELS, current_level, level_env, reg_level_grid  # noqa: F401


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


def seeded_rng(log=None):
    """One RNG per TB, seeded from SEED, and logged so a failure is reproducible."""
    seed = int(os.environ.get('SEED', '0'))
    if log is not None:
        log.info(f"SEED={seed}  (reproduce with: SEED={seed} pytest <this test>)")
    return seed, random.Random(seed)
