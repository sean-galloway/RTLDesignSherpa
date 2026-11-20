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


# ---- MC-013: the policy axes and the captured-trace path ---------------------

def test_mc013_configs_carry_their_axes():
    assert cm.CONFIGS["open32_wm05_25"].wr_low_wm == 0.05 and cm.CONFIGS["open32_wm05_25"].wr_high_wm == 0.25
    assert cm.CONFIGS["open8_wm70_95"].read_buffer == 8
    assert cm.CONFIGS["open32_scatter"].scatter_interval == 195
    assert cm.CONFIGS["open32_bankrr"].scheduler == "BankFIFO-RR" and not cm.CONFIGS["open32_bankrr"].column_first
    assert cm.CONFIGS["open32_bankrr_col"].column_first
    assert cm.CONFIGS["open32_bankrr_col"].peek_depth == 1          # the strict FIFO, MC-013's column
    # MC-016: the two-head store, the four-deep peek and the whole-queue bound, each with column_first
    assert cm.CONFIGS["open32_bankrr_2h"].peek_depth == 2 and cm.CONFIGS["open32_bankrr_2h"].column_first
    assert cm.CONFIGS["open8_bankrr_4h"].peek_depth == 4 and cm.CONFIGS["open8_bankrr_4h"].read_buffer == 8
    assert cm.CONFIGS["open16_bankrr_allh"].peek_depth == 16 and cm.CONFIGS["open16_bankrr_allh"].write_buffer == 16
    assert cm.CONFIGS["open16_rowhit"].scheduler == "FRFCFS-RowHit" and cm.CONFIGS["open16_rowhit"].read_buffer == 16
    for name, c in cm.CONFIGS.items():
        assert c.name == name and c.note, name


def test_wm_naming_is_percent_pairs():
    assert cm._wm("open32", 0.4, 0.9).name == "open32_wm40_90"
    assert cm._wm("open8", 0.03, 0.97).name == "open8_wm03_97"


def test_trace_bytes_counts_one_transaction_per_line(tmp_path):
    p = tmp_path / "t.trace"
    p.write_text("0 ST 0\n1 ST 8\n2 LD 16\n\n# not a line\n")
    assert cm.trace_bytes(str(p)) == (2 * cm.TX_BYTES, 1 * cm.TX_BYTES)


def test_run_trace_files_needs_both_or_a_pair():
    with pytest.raises(ValueError):
        cm.run_trace_files(cm.CONFIGS["open32"], "x", wr="only_one.trace")


def test_axi_trace_exporter_writes_the_frontend_contract(tmp_path):
    """perf_axi_trace.py (the cocotb side) emits what TimedLoadStoreTrace reads: a beat per line,
    ticks consecutive in acceptance order, ST / LD, byte addresses stepping by 1 << AxSIZE."""
    cocotb = pytest.importorskip("cocotb")  # noqa: F841  (the exporter imports its trigger)
    pat = _load("perf_axi_trace", os.path.join(
        REPO_ROOT, "projects", "fpga-systems", "NexysA7", "mem-ctrl-ip-ddr2", "ddr2_char_framework",
        "dv", "tests", "perf_axi_trace.py"))
    exp = pat.AxiTraceExporter(None, awvalid=None, awready=None, awaddr=None, awlen=None, awsize=None,
                               arvalid=None, arready=None, araddr=None, arlen=None, arsize=None)
    path = str(tmp_path / "fam_wr.trace")
    assert exp._burst("ST", 0x1000, 7, 3) is None and exp.end() == {}     # no bracket: nothing captured
    exp.begin(path)
    exp._cycle = 100
    exp._burst("ST", 0x1000, 7, 3)
    exp._cycle = 109
    exp._burst("LD", 0x2000, 1, 3)
    info = exp.end()
    lines = [ln.split() for ln in open(path).read().splitlines()]
    assert [int(l[0]) for l in lines] == list(range(10))
    assert [l[1] for l in lines] == ["ST"] * 8 + ["LD"] * 2
    assert [int(l[2]) for l in lines[:8]] == [0x1000 + 8 * i for i in range(8)]
    assert int(lines[8][2]) == 0x2000 and int(lines[9][2]) == 0x2008
    assert info["st_beats"] == 8 and info["ld_beats"] == 2 and info["st_bursts"] == 1 and info["ld_bursts"] == 1
    assert info["first_cycle"] == 100 and info["last_cycle"] == 109
    assert cm.trace_bytes(path) == (8 * cm.TX_BYTES, 2 * cm.TX_BYTES)
    assert os.path.exists(path + ".meta.json")


# ---- MC-018: the SKU configuration, its timing preset, the address maps and the new patterns ----

def test_sku_preset_is_the_host_mc_cycle_derivation(pumice_char):
    """Every constraint of DDR2_GRANITE_SKU100, measured between two main-slot commands (even CK), must
    round to the host's MC-cycle count at 100 MHz (pumice_device.ddr2_timings_mc_cycles, row_phase 1)."""
    import math
    import ramulator
    pd = pytest.importorskip("pumice_device")
    host = pd.ddr2_timings_mc_cycles(100e6, cl=3, row_phase=1)
    _, t = ramulator.dram.DDR2(org_preset="DDR2_1Gb_x16", timing_preset="DDR2_GRANITE_SKU100").resolve()
    mc = lambda ck: math.ceil(ck / 2)                                           # noqa: E731
    assert mc(t["nRCD"]) == host["tRCD"] and mc(t["nRP"]) == host["tRP"]
    assert mc(t["nRAS"]) == host["tRAS"] and mc(t["nRC"]) == host["tRC"]
    assert mc(t["nRRD"]) == host["tRRD"] and mc(t["nFAW"]) == host["tFAW"] and mc(t["nRFC"]) == host["tRFC"]
    assert mc(t["nCCD"]) == host["tCCD"] and t["nREFI"] // 2 == host["tREFI"]
    assert mc(t["nBL"] + t["nRTP"] - 2) == host["tRTP"]                          # RD -> PRE
    assert mc(t["nCWL"] + t["nBL"] + t["nWR"]) == host["tWR"]                    # WR -> PRE
    assert mc(t["nCWL"] + t["nBL"] + t["nWTR"]) == host["tWTR"]                  # WR -> RD
    assert mc(t["nRTW"]) == host["tRTW"]                                         # RD -> WR (the PHY window)
    # the RTL sequences WRA -> ACT as tWR then tRP; the model's sum must round to the same count
    assert mc(t["nCWL"] + t["nBL"] + t["nWR"] + t["nRP"]) == host["tWR"] + host["tRP"]
    assert mc(t["nBL"] + t["nRTP"] - 2 + t["nRP"]) == host["tRTP"] + host["tRP"]


def test_sku_config_is_the_shipped_point():
    c = cm.CONFIGS["granite_sku100"]
    assert (c.controller, c.timing_preset) == ("GraniteSKU", "DDR2_GRANITE_SKU100")
    assert (c.read_buffer, c.write_buffer, c.bank_cap_mixed, c.dir_batch_max, c.dir_hold_idle) == (16, 16, 6, 255, 8)
    assert c.dir_owns_rows and c.lane == 3 and c.close_on_drain and c.slot_ticks == 2 and not c.page_close
    # ISSUE-004: the decode's request is bank-timed and the rank-level terms hold the fire; the mixed cap is checked
    # at every push; an accepted beat is a head record three MC cycles later (push -> bank FIFO -> head record; the
    # fourth cycle ISSUE-004 measured to the request is the pick pipeline's request register, MC-021)
    assert c.req_bank_timing and c.cap_per_beat and c.admit_lag == 3
    # MC-021: the pick pipeline as measured -- lookahead / hint reach 2 slots, the ACT's rank ok registered one slot,
    # the two RTL questions (arming the same-row ACT after an auto-precharge, masking the closed column's pair) off
    assert (c.pick_la, c.rank_ok_lag, c.ap_act_la, c.ap_stale) == (2, 0, False, False)
    # MC-021 step 4: the record's hit flag -- a bank's heads read as row hits two slots after its ACT (the registered
    # row image, the record, the request register), so the column request shows at ACT + 3, the hinted column at + 2
    assert c.hit_lag == 2 and c.ap_fire_stale   # the step-4 RTL: the fired auto-precharging column's pair masked the slot after
    # MC-021 step 6: the store's write record waits for the entry's fill and the fill-done register (two slots a read's does not)
    assert c.wr_fill_lag == 2
    # every variant changes ONE term against the SKU
    from dataclasses import fields
    for name in cm.SKU_VARIANTS:
        v = cm.CONFIGS[name]
        diff = [f.name for f in fields(v) if f.name not in ("name", "note") and getattr(v, f.name) != getattr(c, f.name)]
        if name in ("sku_peek16_pool32",):
            assert sorted(diff) == ["peek_depth", "read_buffer", "write_buffer"], (name, diff)
        elif name.startswith("sku_pool"):
            assert sorted(diff) == ["read_buffer", "write_buffer"], (name, diff)
        elif name == "sku_ideal16":
            assert sorted(diff) == ["controller", "scheduler"], (name, diff)
        else:
            assert len(diff) == 1, (name, diff)


def test_hit_lag_is_the_record_path_not_the_live_row_image():
    """MC-021 step 4: a bank's heads read as row hits two slots after its ACT (the registered row image, the record's
    hit flag, the request register), so a column whose hint a hold discarded lands at ACT + 5 as the proxy measured,
    not at ACT + 3; under the four-bank close-page interleave that costs the bank its tRC slot (the proxy's 2.17
    cycles per beat against the 2.0 floor the live-read model settled into). The term is on by default. It binds
    only where a hold discards the hint, which the step-4 RTL change (ap_fire_stale) removes on this cell, so the
    test runs the RTL the lag was measured on (ap_fire_stale off)."""
    import tempfile
    from dataclasses import replace
    sc = replace([s for s in cm.SUITES["all"] if s.name == "col_major_bl4"][0], txn_count=4096)
    bw = {}
    for hl in (1, 2):
        cfg = replace(cm.CONFIGS["granite_sku100_bi"], name=f"hl{hl}", hit_lag=hl, ap_fire_stale=False)
        with tempfile.TemporaryDirectory() as t:
            r = cm.run_scenario(cfg, sc, t)
        bw[hl] = (float(r["wr_bw_mb_s"]), float(r["rd_bw_mb_s"]))
    assert cm.CONFIGS["granite_sku100_bi"].hit_lag == 2
    # the read side pays most (0.91 at the board's counts: 389 -> 355 against the board's 351); the write side's
    # recovery hop already hid the lag (283 -> 258, the board's 258). The shipped write side is the board's 258 with
    # or without the step-6 fill lag; the hit_lag-1 counterfactual's write side is 283 without it and 321 with it
    # (the fill lag spaces the write ACTs the live-read model then exploits), so the write band is the wider one.
    assert 0.85 < bw[2][1] / bw[1][1] < 0.97, bw
    assert 0.78 < bw[2][0] / bw[1][0] < 0.97, bw


def test_wr_fill_lag_is_the_write_records_fill_gate():
    """MC-021 step 6: the store's write head record is `has0 && r_wr_fdone` -- the entry's data fill and the fill-done
    register ahead of the record -- where the read record is `has0` alone, so a write beat entering an EMPTY bank
    queue is the pick's request three cycles after it lands and a read beat one (the proxy's probe, both passes of
    the close-page interleaved cell). Under close page every burst's first beat enters an empty queue, and the two
    slots set the new bank's phase against the banks already cycling: in phase, its ACT and theirs collide under
    tRRD, the hold discards the next-op hint and the column lands at ACT + 5. The write side of close_page
    col_major_interleaved_bl8 / bl16 fell from 287 / 208 to 251 / 172 against the board's 250 / 171; the read side
    does not move (the term is the write record's)."""
    import tempfile
    from dataclasses import replace
    sc = replace([s for s in cm.SUITES["all"] if s.name == "col_major_interleaved_bl8"][0], txn_count=4096)
    bw = {}
    for lag in (0, 2):
        cfg = replace(cm.CONFIGS["granite_sku100_close"], name=f"wf{lag}", wr_fill_lag=lag)
        with tempfile.TemporaryDirectory() as t:
            r = cm.run_scenario(cfg, sc, t)
        bw[lag] = (float(r["wr_bw_mb_s"]), float(r["rd_bw_mb_s"]))
    assert cm.CONFIGS["granite_sku100_close"].wr_fill_lag == 2
    assert 0.78 < bw[2][0] / bw[0][0] < 0.95, bw     # the write side pays (0.87 at the board's counts)
    assert 0.98 < bw[2][1] / bw[0][1] < 1.02, bw     # the read record has no fill gate


def test_board_presets_are_what_the_host_programs(pumice_char):
    """The model's `_bi` / `_close` configs stand for the host's ControllerConfig presets, page policy included.
    The board's `bank_interleave` is SCHEME_BANK_INTERLEAVE with PAGE_POLICY_CLOSE; until 2026-11-17 the model ran
    it open page and ISSUE-002's factor of three was that error (memory-controllers ISSUE-002)."""
    dc = pumice_char.dc
    bi, close = pumice_char.CONFIGS["bank_interleave"], pumice_char.CONFIGS["close_page"]
    assert (bi.scheme, bi.page_policy) == (dc.SCHEME_BANK_INTERLEAVE, dc.PAGE_POLICY_CLOSE)
    assert (close.scheme, close.page_policy) == (dc.SCHEME_ROW_MAJOR, dc.PAGE_POLICY_CLOSE)
    m_bi, m_close = cm.CONFIGS["granite_sku100_bi"], cm.CONFIGS["granite_sku100_close"]
    assert (m_bi.addr_map, m_bi.page_close) == ("bank_interleave", True)
    assert (m_close.addr_map, m_close.page_close) == ("row_major", True)
    assert cm.BOARD_PRESET_OF["granite_sku100_bi"] == ("bank_interleave",)


def test_bank_interleave_remap_is_the_rtl_map(pumice_char):
    """bank_lsb 2 in device words: [col_lo(2) | bank(3) | col_hi(8) | row(13)]; consecutive 8-byte beats
    land in consecutive banks of the same row, and the map is a bijection on the device."""
    g = cm.GEOM
    beats = [cm.remap_bank_interleave(i * 8) for i in range(16)]
    banks = [(a // g.bank_stride) % 8 for a in beats]
    rows = [a // g.row_stride_same_bank for a in beats]
    assert banks == [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
    assert rows == [0] * 16
    # the ninth beat is the second burst of bank 0: column 4 (one BL4 burst on)
    assert (beats[8] % g.bank_stride) // 8 == 1
    # bijection on a sample, and byte-in-word preserved
    sample = [i * 8 for i in range(0, 1 << 16, 7)]
    out = {cm.remap_bank_interleave(a) for a in sample}
    assert len(out) == len(sample)
    assert cm.remap_bank_interleave(5) % 2 == 1


def test_rw_mix_stream_has_the_requested_write_fraction():
    sc = cm.Scenario("rw70_bl8", "rw_mix", burst_len=8, txn_count=2000, threads=4, param=0.7)
    w, _ = cm.injector_walks(sc)
    ops = [op for op, _ in cm.interleave_mixed_bursts(w, 8, 0.7)]
    assert len(ops) == 4 * 2000 * 8
    frac = ops.count("ST") / len(ops)
    assert 0.67 < frac < 0.73
    # a burst is all one direction
    assert all(len(set(ops[i:i + 8])) == 1 for i in range(0, len(ops), 8))


@pytest.mark.parametrize("h", [0.1, 0.5, 0.9])
def test_locality_walk_hits_at_about_the_requested_rate(h):
    sc = cm.Scenario(f"locality_h{int(h*100):02d}_bl8", "locality", burst_len=8, txn_count=4000, threads=4, param=h)
    w, _ = cm.injector_walks(sc)
    g = cm.GEOM
    for gi, walk in enumerate(w):
        assert len({(a // g.bank_stride) % 8 for a in walk}) == 1          # one bank per injector
        rows = [a // g.row_stride_same_bank for a in walk]
        assert len(set(rows)) <= cm.REGION_ROWS
        same = sum(1 for i in range(1, len(rows)) if rows[i] == rows[i - 1]) / (len(rows) - 1)
        assert abs(same - h) < 0.05, (gi, same)


def test_bank_step_touches_only_every_nth_bank():
    g = cm.GEOM
    for step in (2, 4):
        sc = cm.Scenario(f"col_ilv_s{step}_bl8", "bank_step", burst_len=8, txn_count=64, param=step)
        w, _ = cm.injector_walks(sc)
        banks = {(a // g.bank_stride) % 8 for a in w[0]}
        assert banks == set(range(0, 8, step))
        # every burst is a row miss: consecutive bursts to one bank are a row apart
        per_bank = {}
        for a in w[0]:
            per_bank.setdefault((a // g.bank_stride) % 8, []).append(a // g.row_stride_same_bank)
        assert all(r[i] != r[i + 1] for r in per_bank.values() for i in range(len(r) - 1))


def test_split_trace_stamps_the_two_streams_with_shared_ticks(tmp_path):
    sc = cm.Scenario("mixed_bl8", "mixed", burst_len=8, txn_count=2, threads=2, split=True)
    w, r = cm.injector_walks(sc)
    path = tmp_path / "m.trace"
    cm.write_trace(str(path), [cm.interleave_bursts(w, 8, "ST"), cm.interleave_bursts(r, 8, "LD")], split=True)
    lines = [ln.split() for ln in path.read_text().splitlines()]
    ticks = [int(ln[0]) for ln in lines]
    assert ticks[:4] == [0, 0, 1, 1] and ticks[-1] == 2 * 2 * 8 - 1
    assert [ln[1] for ln in lines[:4]] == ["ST", "LD", "ST", "LD"]


def test_write_trace_applies_the_address_map(tmp_path):
    path = tmp_path / "bi.trace"
    cm.write_trace(str(path), [iter([("LD", 8), ("LD", 16)])], addr_map="bank_interleave")
    addrs = [int(ln.split()[2]) for ln in path.read_text().splitlines()]
    assert addrs == [cm.remap_bank_interleave(8), cm.remap_bank_interleave(16)]
    assert (addrs[0] // cm.GEOM.bank_stride) % 8 == 1
