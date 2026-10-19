# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_tile_intake_model
# Purpose: Validate the pencilled-in tagged, indexed tile intake against an
#          interleaving, reordering fabric (rapids TASK-033); pure Python, no RTL
#
# Subsystem: rapids
# Author: sean galloway
# Created: 2026-10-19

import os
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'models'))

from tile_intake_model import Cfg, run  # noqa: E402

LATS = {'near': (2, 10), 'far': (8, 40), 'multipath': (4, 120)}


def _show(tag, r):
    print(f"{tag}: {r['cycles']} cycles, {r['data_flits']} payload flits, "
          f"payload {r['link_util']:.2f} flits/cycle (link peak 1), {len(r['errors'])} errors")
    for e in r['errors'][:5]:
        print(f"  {e}")


@pytest.mark.parametrize("seed", [1, 2, 3])
@pytest.mark.parametrize("lat", list(LATS))
@pytest.mark.parametrize("land", [16, 8])
def test_indexed_intake(seed, lat, land):
    """The mechanism: strap-only cells, tagged flits, indexed landing.
    Every class delivered exactly once, in send order, straps whole."""
    r = run(Cfg(seed=seed, lat=LATS[lat], land=land))
    _show(f"indexed {lat} land {land} seed {seed}", r)
    assert not r['errors']


@pytest.mark.parametrize("seed", [1, 2])
def test_waitall_on_todays_landing(seed):
    """The interim rule (one data packet in flight per cell) is correct on
    today's arrival-order landing."""
    r = run(Cfg(seed=seed, lat=LATS['multipath'], send_rule='waitall', landing='arrival'))
    _show(f"waitall/arrival seed {seed}", r)
    assert not r['errors']


@pytest.mark.parametrize("rule", ['strap', 'oneflit'])
def test_todays_landing_breaks(rule):
    """Control: today's landing with more than one packet in flight per cell
    corrupts under interleaving; this is why the retired one-flit rule went."""
    r = run(Cfg(seed=1, lat=LATS['multipath'], send_rule=rule, landing='arrival', max_cycles=60_000))
    _show(f"{rule}/arrival", r)
    assert r['errors'], "today's landing survived interleaving: the fabric model is not interleaving"


@pytest.mark.parametrize("mutation", ['drain_any', 'pos_excl_header'])
def test_mutations_caught(mutation):
    """Each load-bearing piece of the mechanism, removed, is caught."""
    cfg = Cfg(seed=1, lat=LATS['multipath'], max_cycles=60_000)
    if mutation == 'drain_any':
        cfg.drain = 'any'
    else:
        cfg.pos_excl_header = True
    r = run(cfg)
    _show(mutation, r)
    assert r['errors'], f"mutation {mutation} went unseen"


@pytest.mark.parametrize("cells", [1, 2, 4, 16])
@pytest.mark.parametrize("lat", ['near', 'far'])
def test_throughput(cells, lat):
    """Data flits per cycle on RAPIDS's link: strap-only + indexed vs the
    wait-all rule. Reported, and indexed must never be slower."""
    common = dict(seed=7, lat=LATS[lat], cells=cells, nodes=0, cores=0, mons=0)
    a = run(Cfg(**common))
    b = run(Cfg(send_rule='waitall', landing='arrival', **common))
    _show(f"indexed {cells} cells {lat}", a)
    _show(f"waitall {cells} cells {lat}", b)
    assert not a['errors'] and not b['errors']
    assert a['link_util'] >= b['link_util'] * 0.98
