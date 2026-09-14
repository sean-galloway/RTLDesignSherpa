#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less proof of bank_gap_sweep's structure and arithmetic.

The sweep itself cannot run without hardware, but almost everything that can be
WRONG about it is decidable here: which bank each engine lands on, whether the
two directions are launched together, whether one seed reaches every engine,
whether the prefill covers the device exactly, and whether the curve analysis
reports a bend where a bend actually is.

That last one matters most. The knee is the number the sweep exists to produce,
and a knee computed by an off-by-one would still look plausible on a board --
it would just quietly move the answer. Here it is checked against curves whose
bend is known by construction.

    source env_python && pytest bin/tests/test_bank_gap_sweep.py -q
"""
import importlib
import io
import os
import sys
import types
import contextlib

import pytest

_BIN = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_FLOW = os.path.dirname(_BIN)
sys.path.insert(0, _BIN)
sys.path.insert(0, os.path.join(_FLOW, "host"))

if not os.environ.get("REPO_ROOT"):
    pytest.skip("REPO_ROOT not set (source env_python)", allow_module_level=True)


class _MockDrv:
    """Records what would have been programmed, and fakes a plausible clock.

    The cycle model is min(controller rate, generator rate): a burst costs
    `beats/util` cycles at the controller and `beats+gap` at the generator,
    whichever is slower. That is enough shape for the knee to be real.
    """

    UTIL = {"incremental": 0.95, "row_major": 0.80, "col_major": 0.35}

    def __init__(self):
        self.wr, self.rd, self.launches = [], [], []
        self._gap, self._txn, self._beats, self._util = 0, 1, 8, 0.95

    def sync_gen_config(self):
        return {"num_wr_gen": 4, "num_rd_gen": 4, "num_banks": 8}

    def program_wr_engine(self, **kw):
        self.wr.append(kw)
        self._gap, self._txn, self._beats = kw["gap"], kw["txn_count"], kw["burst_len"]

    def program_rd_engine(self, **kw):
        self.rd.append(kw)

    def go(self, wr_mask=0, rd_mask=0):
        self.launches.append((wr_mask, rd_mask))

    def start_both(self, wr_mask=0, rd_mask=0):
        self.go(wr_mask=wr_mask, rd_mask=rd_mask)

    def perf_hist_dump(self, *a, **k):
        return [], self._txn * self._n_gen

    def beats_mismatched(self):
        return 0

    def set_controller_cfg(self, **kw):
        return dict(kw)

    def timer(self):
        cyc = int(self._txn * self._period())
        return types.SimpleNamespace(w_first=0, w_last=cyc, r_first=0, r_last=cyc)

    def _period(self):
        """Cycles per burst: whichever side is slower."""
        return max(self._beats / self._util, self._beats + self._gap)

    def perf_meters(self):
        """Four buckets consistent with the cycle model above.

        Productive is the beats actually moved. Whatever the GAP adds on top
        of the controller's own rate is STARVATION -- the generator withheld
        it. Whatever the controller's rate costs above the raw beats is
        BACKPRESSURE -- it would not accept.
        """
        total = int(self._txn * self._period())
        prod = int(self._txn * self._beats)
        gen_excess = max(0.0, (self._beats + self._gap) - self._beats / self._util)
        starv = int(self._txn * gen_excess)
        bp = max(0, total - prod - starv)
        m = types.SimpleNamespace(prod=prod, bp=bp, starv=starv, idle=0)
        return {"wr": m, "rd": m}

    def __getattr__(self, _n):
        return lambda *a, **k: {}


def _load(gens="4,3,2,1", gaps=None, txn="2000"):
    """Import bank_gap_sweep fresh with the env it reads at module scope."""
    import ddr2_char as dc
    import pumice_char as pc

    drv = _MockDrv()
    dc.autodetect_port = lambda *a, **k: "/dev/null"
    dc.DDR2CharDriver = lambda **k: drv
    pc.wait_engine = lambda *a, **k: True
    real_strides = getattr(pc, "_real_strides_for", pc.strides_for)
    pc._real_strides_for = real_strides

    def strides(sc, geom):
        drv._util = _MockDrv.UTIL[sc.family]
        return real_strides(sc, geom)

    pc.strides_for = strides
    sys.modules["pumice_master"] = types.SimpleNamespace(
        SimpleTest=lambda *a, **k: types.SimpleNamespace(init=lambda **kk: None))

    os.environ["GENS"] = gens
    os.environ["TXN"] = txn
    if gaps is not None:
        os.environ["GAPS"] = gaps
    else:
        os.environ.pop("GAPS", None)
    sys.modules.pop("bank_gap_sweep", None)
    mod = importlib.import_module("bank_gap_sweep")
    drv._n_gen = max(int(x) for x in gens.split(","))
    return mod, drv


def _run(mod, drv):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = mod.main()
    return rc, buf.getvalue()


# ---------------------------------------------------------------------------
# Bank assignment -- the correctness requirement, not tidiness
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("n_gen", [1, 2, 3, 4])
def test_writer_and_reader_banks_are_disjoint(n_gen):
    """A reader sampling an address a writer is mid-burst on reports a
    mismatch that is a race in the test, not a defect in the controller."""
    mod, _ = _load()
    import pumice_char as pc
    wr, rd = mod._banks(pc.DEFAULT_GEOM, n_gen)
    assert len(wr) == len(rd) == n_gen
    assert not (set(wr) & set(rd)), f"overlap at n={n_gen}: {wr} vs {rd}"
    assert len(set(wr) | set(rd)) == 2 * n_gen, "two engines share a bank"
    assert max(wr + rd) < (1 << pc.DEFAULT_GEOM.bank_width)


def test_banks_interleave_rather_than_cluster():
    """Writers and readers alternate, so the directions contend the way a real
    mix would instead of sitting at opposite ends of the device."""
    mod, _ = _load()
    import pumice_char as pc
    wr, rd = mod._banks(pc.DEFAULT_GEOM, 4)
    assert wr == [0, 2, 4, 6] and rd == [1, 3, 5, 7]


# ---------------------------------------------------------------------------
# Seed and launch discipline
# ---------------------------------------------------------------------------
def test_one_seed_reaches_prefill_and_every_engine():
    """A per-point seed would invalidate the prefill the moment the first
    reader started -- the expected data is a function of address AND seed."""
    mod, drv = _load(gens="4,2", gaps="0,7")
    _run(mod, drv)
    seeds = {p["hash_seed0"] for p in drv.wr} | {p["hash_seed0"] for p in drv.rd}
    assert seeds == {mod.SEED}, f"more than one seed in play: {seeds}"


def test_both_directions_launch_together():
    mod, drv = _load(gens="4,2", gaps="0,7")
    _run(mod, drv)
    points = [(w, r) for (w, r) in drv.launches if r]   # prefill is write-only
    assert points, "no concurrent launch recorded"
    for w, r in points:
        assert w == r, f"asymmetric launch {w:#x}/{r:#x} -- not concurrent"


def test_prefill_runs_before_any_read():
    mod, drv = _load(gens="4", gaps="0")
    _run(mod, drv)
    assert drv.launches[0][1] == 0, "first launch was not the write-only prefill"
    assert drv.wr, "no prefill programmed"


# ---------------------------------------------------------------------------
# Prefill arithmetic -- an overrun writes past the device and every later read
# of that region reports a mismatch that is this, not the DRAM
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("n_gen", [1, 2, 4])
def test_prefill_covers_the_device_exactly(n_gen):
    mod, _ = _load()
    import pumice_char as pc
    geom = pc.DEFAULT_GEOM
    per = geom.device_bytes // n_gen
    total = per // mod.FILL_BYTES
    passes = -(-total // pc.TXN_MAX)
    base, extra = divmod(total, passes)
    covered = sum(base + (1 if p < extra else 0) for p in range(passes))
    assert covered == total, "passes do not cover the share exactly"
    assert base + (1 if extra else 0) <= pc.TXN_MAX, "a pass exceeds txn_count"
    assert total * mod.FILL_BYTES * n_gen == geom.device_bytes, "device not covered"


# ---------------------------------------------------------------------------
# Gap range -- the field is four bits
# ---------------------------------------------------------------------------
def test_default_gaps_fit_the_four_bit_field():
    mod, _ = _load()
    assert mod.GAPS == list(range(16))
    assert max(mod.GAPS) <= 15, "gap 16 would program 0 and re-measure gap 0"


# ---------------------------------------------------------------------------
# Curve analysis -- the number the sweep exists to produce
# ---------------------------------------------------------------------------
def test_knee_is_where_the_bend_is():
    mod, _ = _load()
    gaps = list(range(16))
    # Flat through gap 5, then falling.
    vals = [100.0] * 6 + [100.0 - 8 * (g - 5) for g in range(6, 16)]
    assert mod._knee(gaps, vals) == 5


def test_knee_is_zero_when_every_clock_of_idle_costs():
    mod, _ = _load()
    gaps = list(range(16))
    vals = [100.0 - 10 * g for g in gaps]
    assert mod._knee(gaps, vals) == 0


def test_knee_is_the_last_gap_when_the_curve_never_bends():
    mod, _ = _load()
    gaps = list(range(16))
    assert mod._knee(gaps, [100.0] * 16) == 15


def test_knee_tolerates_only_small_wobble():
    """2% of noise must not read as a bend; 10% must."""
    mod, _ = _load()
    gaps = [0, 1, 2]
    assert mod._knee(gaps, [100.0, 98.0, 98.0]) == 2
    assert mod._knee(gaps, [100.0, 90.0, 90.0]) == 0


def test_sparkline_tracks_the_data():
    mod, _ = _load()
    rising = mod._spark([0, 1, 2, 3, 4], 0, 4)
    assert rising[0] == mod.SPARK[0] and rising[-1] == mod.SPARK[-1]
    # Monotone in RAMP POSITION, not in codepoint: the ramp " .:-=+*#@" is
    # chosen for how it reads, and its characters are not in ASCII order.
    levels = [mod.SPARK.index(c) for c in rising]
    assert levels == sorted(levels), f"sparkline not monotone on rising data: {levels}"
    assert mod._spark([5, 5, 5], 5, 5) == mod.SPARK[-1] * 3, "flat data must not divide by zero"


# ---------------------------------------------------------------------------
# End to end against the mock physics: the knee must ORDER by family speed
# ---------------------------------------------------------------------------
def test_slower_families_have_more_slack():
    """The controller absorbs more injected idle the slower the access family
    is, so the knee must rise from cacheline to row-major to col-major. If it
    does not, either the sweep or the controller is not doing what it claims."""
    mod, drv = _load(gens="4")
    rc, out = _run(mod, drv)
    assert rc == 0, out
    knees = {}
    for line in out.splitlines():
        for name, _ in mod.ORDERS:
            if line.strip().startswith(f"{name} bus"):
                knees[name] = int(line.split()[-1])
    assert set(knees) == {n for n, _ in mod.ORDERS}, f"missing curves: {knees}"
    assert knees["cacheline"] <= knees["row_major"] <= knees["col_major"], knees


# ---------------------------------------------------------------------------
# The record is what outlives the run -- the plots and any later comparison
# read it, not the scrollback. Check it carries what they need.
# ---------------------------------------------------------------------------
def test_record_carries_coordinates_rates_ceiling_and_buckets(tmp_path):
    out = tmp_path / "sweep.json"
    mod, drv = _load(gens="4,2", gaps="0,7")
    os.environ["JSON_OUT"] = str(out)
    mod = importlib.reload(mod)
    _run(mod, drv)
    import json
    rows = json.loads(out.read_text())
    assert rows, "no records written"
    r = rows[0]
    for k in ("order", "n_gen", "gap", "txn", "beats",          # coordinates
              "wr", "rd", "bus",                                 # rates
              "wr_cycles", "rd_cycles", "window_cycles",         # both windows
              "peak_mb_s",                                       # the ceiling
              "mism", "ok", "rd_txn", "want_txn", "buckets"):
        assert k in r, f"record is missing {k!r}"
    for d in ("wr", "rd"):
        b = r["buckets"][d]
        # Raw counts AND fractions, so nothing downstream re-derives a ratio.
        # `total` is the denominator and carries no fraction of its own.
        assert isinstance(b["total"], int), f"{d}.total missing/not an int"
        for k in ("productive", "backpressure", "starvation", "idle"):
            assert k in b and isinstance(b[k], int), f"{d}.{k} missing/not an int"
            assert f"{k}_frac" in b, f"{d}.{k}_frac missing"
        assert abs(sum(b[f"{k}_frac"] for k in
                       ("productive", "backpressure", "starvation", "idle"))
                   - 1.0) < 1e-6, "bucket fractions do not sum to 1"


def test_named_gap_sweeps_resolve_and_typos_raise():
    """A sweep you cannot name is a sweep you cannot repeat -- and a typo must
    not silently measure a different curve than the one that was asked for."""
    mod, _ = _load()
    assert mod.resolve_gaps("full") == list(range(16))
    assert mod.resolve_gaps("ends") == [0, 15]
    assert mod.resolve_gaps("0,4,8") == [0, 4, 8]
    with pytest.raises(SystemExit):
        mod.resolve_gaps("kneee")
