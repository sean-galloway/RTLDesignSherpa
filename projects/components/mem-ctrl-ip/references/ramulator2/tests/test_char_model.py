"""char_model.py builds the board's request streams: check it against the board
host's own stride table and the trace contract the frontend enforces.

Run from the repo root: `pytest projects/components/mem-ctrl-ip/references/ramulator2/tests -q`
"""
import importlib.util
import os
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.abspath(os.path.join(HERE, *[".."] * 6))
HOST = os.path.join(REPO_ROOT, "projects", "fpga-systems", "NexysA7", "mem-ctrl-ip-ddr2", "build-perf", "host")


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod          # dataclasses resolve annotations through sys.modules
    spec.loader.exec_module(mod)
    return mod


cm = _load("char_model", os.path.join(HERE, "..", "bin", "char_model.py"))


@pytest.fixture(scope="module")
def pumice_char():
    if HOST not in sys.path:
        sys.path.insert(0, HOST)
    return pytest.importorskip("pumice_char")


def test_geometry_matches_the_board_host(pumice_char):
    g = pumice_char.DEFAULT_GEOM
    assert (cm.GEOM.page_bytes, cm.GEOM.bank_stride, cm.GEOM.row_stride_same_bank, cm.GEOM.device_bytes) == (
        g.page_bytes, g.bank_stride, g.row_stride_same_bank, g.device_bytes)


@pytest.mark.parametrize("family", ["incremental", "row_major", "col_major", "col_major_interleaved"])
@pytest.mark.parametrize("bl", [4, 8, 16])
def test_stride_families_reproduce_strides_for(pumice_char, family, bl):
    sc_host = pumice_char.Scenario(f"{family}_bl{bl}", family, burst_len=bl, txn_count=300)
    stride, wrap = pumice_char.strides_for(sc_host, pumice_char.DEFAULT_GEOM)
    expect = [(i * stride) & wrap if wrap else i * stride for i in range(300)]
    walks, rwalks = cm.injector_walks(cm.Scenario(sc_host.name, family, burst_len=bl, txn_count=300))
    assert walks == [expect] and rwalks is walks


def test_row_thrash_alternates_two_rows_of_one_bank_per_injector():
    sc = cm.Scenario("row_thrash_bl8", "row_thrash", burst_len=8, txn_count=64, threads=4)
    walks, _ = cm.injector_walks(sc)
    assert len(walks) == 4
    for g, w in enumerate(walks):
        rows = {(a // cm.GEOM.row_stride_same_bank) for a in w}
        banks = {(a // cm.GEOM.bank_stride) % 8 for a in w}
        assert rows == {cm.ROW_THRASH_ROW, cm.ROW_THRASH_ROW + 1}
        assert banks == {g}
        # consecutive bursts land on different rows (a PRE + ACT per burst)
        assert all((w[i] // cm.GEOM.row_stride_same_bank) != (w[i + 1] // cm.GEOM.row_stride_same_bank)
                   for i in range(len(w) - 1))


def test_random_stays_in_its_two_row_region_and_touches_every_bank():
    sc = cm.Scenario("random_bl8", "random", burst_len=8, txn_count=4000, threads=4)
    walks, _ = cm.injector_walks(sc)
    region = cm.RANDOM_ROWS * cm.GEOM.row_stride_same_bank
    for g, w in enumerate(walks):
        assert all(g * region <= a < (g + 1) * region for a in w)
        assert len({(a // cm.GEOM.bank_stride) % 8 for a in w}) == 8
        assert all(a % sc.burst_bytes == 0 for a in w)


def test_lfsr16_is_maximal():
    lf = cm._lfsr16(0xACE1)
    seen = set()
    for _ in range(65535):
        seen.add(next(lf))
    assert len(seen) == 65535


def test_mixed_places_writers_and_readers_rows_apart_in_shared_banks():
    sc = cm.Scenario("mixed_bl8", "mixed", burst_len=8, txn_count=100, threads=4)
    w, r = cm.injector_walks(sc)
    assert len(w) == 4 and len(r) == 4
    for ww, rr in zip(w, r):
        wb, rb = (ww[0] // cm.GEOM.bank_stride) % 8, (rr[0] // cm.GEOM.bank_stride) % 8
        assert wb == rb
        assert rr[0] // cm.GEOM.row_stride_same_bank - ww[0] // cm.GEOM.row_stride_same_bank == cm.REGION_ROWS


def test_trace_is_one_beat_per_tick_and_expands_every_burst(tmp_path):
    sc = cm.Scenario("row_thrash_bl8", "row_thrash", burst_len=8, txn_count=16, threads=4)
    w, _ = cm.injector_walks(sc)
    path = tmp_path / "t.trace"
    n = cm.write_trace(str(path), [cm.interleave_bursts(w, 8, "ST")])
    lines = [ln.split() for ln in path.read_text().splitlines()]
    assert n == len(lines) == 4 * 16 * 8
    assert [int(ln[0]) for ln in lines] == list(range(n))
    assert all(ln[1] == "ST" for ln in lines)
    # the first burst's eight beats are contiguous 8-byte steps, then the next injector's burst
    first = [int(ln[2]) for ln in lines[:8]]
    assert first == [w[0][0] + 8 * i for i in range(8)]
    assert int(lines[8][2]) == w[1][0]


def test_mixed_trace_interleaves_the_two_directions_beat_by_beat(tmp_path):
    sc = cm.Scenario("mixed_bl8", "mixed", burst_len=8, txn_count=4, threads=2)
    w, r = cm.injector_walks(sc)
    path = tmp_path / "m.trace"
    cm.write_trace(str(path), [cm.interleave_bursts(w, 8, "ST"), cm.interleave_bursts(r, 8, "LD")])
    ops = [ln.split()[1] for ln in path.read_text().splitlines()]
    assert ops[:4] == ["ST", "LD", "ST", "LD"] and len(ops) == 2 * 2 * 4 * 8


def test_bandwidth_is_the_board_definition():
    # bytes over cycles times the MC clock in MHz == MB/s
    assert cm._bw(4194240, 543066) == pytest.approx(772.33, abs=0.01)
