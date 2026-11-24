"""char_model.py builds the board's request streams: check it against the board
host's own stride table and the trace contract the frontend enforces.

Run from the repo root: `pytest projects/components/mem-ctrl-ip/references/ramulator2/tests -q`
"""
import importlib.util
import os
import sys

import re
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

# The counters the board ran under before 2026-11-22 (the one-CK phase margin, DDR2_GRANITE_SKU100). The SKU's
# default is the phase-exact set since then (MC-020); a test that reproduces a board or proxy number recorded
# before that date pins the preset the number was made at.
MARGIN = "DDR2_GRANITE_SKU100"
# ... and the self-close reloading the shared tRP, as the margin's host programmed it (MC-020 decision 2)
MARGIN_AP = dict(t_rp_ap_rd=2, t_rp_ap_wr=2)



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


def test_px_preset_is_the_phase_exact_host_derivation(pumice_char):
    """MC-020: DDR2_GRANITE_SKU100_PX is what ddr2_timings_mc_cycles(phase_exact=True) programs at 100 MHz with the
    SKU's fixed DFI phases (RD / WR on 0, row commands on 1): the worst-phase margin replaced by the phase offset."""
    import math
    import ramulator
    pd = pytest.importorskip("pumice_device")
    host = pd.ddr2_timings_mc_cycles(100e6, cl=3, rd_phase=0, wr_phase=0, row_phase=1, phase_exact=True)
    base = pd.ddr2_timings_mc_cycles(100e6, cl=3, rd_phase=0, wr_phase=0, row_phase=1)
    # (tRP_AP_RD since MC-020 decision 2: the read path's self-close reloads 1 where the margin's shared tRP is 2)
    assert {k for k in host if host[k] != base[k]} == {"tRC", "tWR", "tWTR", "tRRD", "tRFC", "tRP_AP_RD"}, (host, base)
    assert (host["tRC"], host["tWR"], host["tWTR"], host["tRRD"], host["tRFC"]) == (6, 3, 3, 1, 13)
    assert all(host[k] <= base[k] for k in host)                                 # exact is never longer
    _, t = ramulator.dram.DDR2(org_preset="DDR2_1Gb_x16", timing_preset="DDR2_GRANITE_SKU100_PX").resolve()
    mc = lambda ck: math.ceil(ck / 2)                                           # noqa: E731
    assert mc(t["nRCD"]) == host["tRCD"] and mc(t["nRP"]) == host["tRP"]
    assert mc(t["nRAS"]) == host["tRAS"] and mc(t["nRC"]) == host["tRC"]
    assert mc(t["nRRD"]) == host["tRRD"] and mc(t["nFAW"]) == host["tFAW"] and mc(t["nRFC"]) == host["tRFC"]
    assert mc(t["nBL"] + t["nRTP"] - 2) == host["tRTP"]
    # WR -> explicit PRE: the RTL's PRE sits on phase 1, so its 7 CK are 3 MC + 1; the model fires its main-slot
    # PRE on the even tick and takes 4 -- one cycle conservative on that one hop (the lane's odd-tick PRE sees 7)
    assert mc(t["nCWL"] + t["nBL"] + t["nWR"]) == host["tWR"] + 1
    assert mc(t["nCWL"] + t["nBL"] + t["nWTR"]) == host["tWTR"]
    # WRA -> ACT, the hop col_major's write chain pays: the same count in both
    assert mc(t["nCWL"] + t["nBL"] + t["nWR"] + t["nRP"]) == host["tWR"] + host["tRP"]
    # MC-020 decision 2: the self-close's own tRP per path -- the ACT on row_phase 1 after the DRAM's internal close
    # (RD + BL/2 + tRTP - 2 = 2 CK, WR + WL + BL/2 + tWR = 7 CK, or ACT + tRAS), less the counter that fired
    assert (host["tRP_AP_RD"], host["tRP_AP_WR"]) == (1, 2)
    assert (base["tRP_AP_RD"], base["tRP_AP_WR"]) == (base["tRP"], base["tRP"])      # the margin: the shared tRP
    assert 2 * (host["tRTP"] + host["tRP_AP_RD"]) + 1 >= t["nBL"] + t["nRTP"] - 2 + t["nRP"]   # RDA -> ACT legal
    assert 2 * (host["tWR"] + host["tRP_AP_WR"]) + 1 >= t["nCWL"] + t["nBL"] + t["nWR"] + t["nRP"]   # WRA -> ACT legal
    assert host["tRAS"] + host["tRP_AP_RD"] >= host["tRC"] and host["tRAS"] + host["tRP_AP_WR"] >= host["tRC"]
    # every count is a legal JEDEC distance on the SKU's phases: 2 m + (b - a) CK >= the CK minimum
    ck = {k: max(math.ceil(v / 5.0), pd.DDR2_CK_MIN.get(k, 1)) for k, v in pd.DDR2_MT47H64M16_NS.items()}
    assert 2 * host["tRCD"] - 1 >= ck["tRCD"] and 2 * host["tRP"] >= ck["tRP"] and 2 * host["tRAS"] >= ck["tRAS"]
    assert 2 * host["tRC"] >= ck["tRC"] and 2 * host["tRRD"] >= ck["tRRD"] and 2 * host["tFAW"] >= ck["tFAW"]
    assert 2 * host["tRFC"] >= ck["tRFC"] and 2 * host["tWR"] + 1 >= 2 + 2 + ck["tWR"]
    assert 2 * host["tWTR"] >= 2 + 2 + ck["tWTR"]


def test_t_rp_ap_fields_are_the_host_derivation(pumice_char):
    """MC-020 decision 2: the SKU config's t_rp_ap_rd / t_rp_ap_wr are what the host programs into TIMINGS_RP_AP at
    100 MHz on the SKU's phases, and sku_margin's are the margin host's (the shared tRP)."""
    pd = pytest.importorskip("pumice_device")
    host = pd.ddr2_timings_mc_cycles(100e6, cl=3, rd_phase=0, wr_phase=0, row_phase=1, phase_exact=True)
    c = cm.CONFIGS["granite_sku100"]
    assert (c.t_rp_ap_rd, c.t_rp_ap_wr) == (host["tRP_AP_RD"], host["tRP_AP_WR"])
    base = pd.ddr2_timings_mc_cycles(100e6, cl=3, rd_phase=0, wr_phase=0, row_phase=1)
    m = cm.CONFIGS["sku_margin"]
    assert (m.t_rp_ap_rd, m.t_rp_ap_wr) == (base["tRP_AP_RD"], base["tRP_AP_WR"]) == (base["tRP"], base["tRP"])


def test_sku_param_overrides_parse_ints_and_bools(monkeypatch):
    monkeypatch.setenv("GRANITE_SKU_PARAMS", "t_rp_ap_rd=2, t_rp_ap_wr=0x2,ap_seq=false")
    assert cm._sku_param_overrides() == {"t_rp_ap_rd": 2, "t_rp_ap_wr": 2, "ap_seq": False}
    monkeypatch.delenv("GRANITE_SKU_PARAMS")
    assert cm._sku_param_overrides() == {}


def test_sku_config_is_the_shipped_point():
    c = cm.CONFIGS["granite_sku100"]
    # MC-020: the phase-exact counters, the host's default since 2026-11-22 (the margin set is `sku_margin`)
    assert (c.controller, c.timing_preset) == ("GraniteSKU", "DDR2_GRANITE_SKU100_PX")
    assert cm.CONFIGS["sku_margin"].timing_preset == "DDR2_GRANITE_SKU100"
    assert (c.read_buffer, c.write_buffer, c.bank_cap_mixed, c.dir_batch_max, c.dir_hold_idle) == (16, 16, 6, 255, 8)
    assert c.dir_owns_rows and c.lane == 3 and c.close_on_drain and c.slot_ticks == 2 and not c.page_close
    # ISSUE-006: the page policy is the board's `defaults` -- the hybrid (mode 4) with the RDL's idle timeout 2
    assert (c.page_mode, c.tr_init) == (4, 2)
    assert cm.CONFIGS["granite_sku100_open"].page_mode == 0      # the board's open_page preset: policy_mode 0
    # ISSUE-004: the decode's request is bank-timed and the rank-level terms hold the fire; the mixed cap is checked
    # at every push; an accepted beat is a head record three MC cycles later (push -> bank FIFO -> head record; the
    # fourth cycle ISSUE-004 measured to the request is the pick pipeline's request register, MC-021)
    assert c.req_bank_timing and c.cap_per_beat
    # MC-021 step 7: the admission's three terms -- pool gate 2 + landing 1 (= the 3 ISSUE-004 measured), cap gate 1 + landing 1
    assert (c.admit_lag, c.pool_gate_lag, c.cap_gate_lag) == (1, 2, 1)
    # MC-021: the pick pipeline as measured -- lookahead / hint reach 2 slots, the ACT's rank ok registered one slot,
    # the two RTL questions (arming the same-row ACT after an auto-precharge, masking the closed column's pair) off
    assert (c.pick_la, c.rank_ok_lag, c.ap_act_la, c.ap_stale) == (2, 0, False, False)
    # MC-021 step 4: the record's hit flag -- a bank's heads read as row hits two slots after its ACT (the registered
    # row image, the record, the request register), so the column request shows at ACT + 3, the hinted column at + 2
    assert c.hit_lag == 2 and c.ap_fire_stale   # the step-4 RTL: the fired auto-precharging column's pair masked the slot after
    # MC-021 step 6: the store's write record waits for the entry's fill and the fill-done register (two slots a read's does not)
    assert c.wr_fill_lag == 2
    # MC-021 step 8: the record's hit flag on the way down -- a head whose row a PRE closed requests its ACT two slots later
    assert c.close_lag == 2
    # MC-020 decision 2: the self-close sequenced as the bank timer does, reloading the host's per-path tRP (1 / 2 at
    # 100 MHz on phases 0 / 0 / 1); sku_rpshared is the RTL before the fields, sku_margin's host programs tRP for both
    assert c.ap_seq and (c.t_rp_ap_rd, c.t_rp_ap_wr) == (1, 2)
    assert (cm.CONFIGS["sku_rpshared"].t_rp_ap_rd, cm.CONFIGS["sku_rpshared"].t_rp_ap_wr) == (2, 2)
    assert (cm.CONFIGS["sku_margin"].t_rp_ap_rd, cm.CONFIGS["sku_margin"].t_rp_ap_wr) == (2, 2)
    assert not cm.CONFIGS["sku_noapseq"].ap_seq
    # every variant changes ONE term against the SKU
    from dataclasses import fields
    for name in cm.SKU_VARIANTS:
        v = cm.CONFIGS[name]
        diff = [f.name for f in fields(v) if f.name not in ("name", "note") and getattr(v, f.name) != getattr(c, f.name)]
        if name in ("sku_peek16_pool32",):
            assert sorted(diff) == ["peek_depth", "read_buffer", "write_buffer"], (name, diff)
        elif name == "sku_admit3":
            # one term, the admission, in its three fields: the single three-slot stage of the model before step 7
            assert sorted(diff) == ["admit_lag", "cap_gate_lag", "pool_gate_lag"], (name, diff)
        elif name == "sku_margin":
            # one term, the host's derivation: the preset and the self-close field it programs as tRP (the write
            # path's 2 is the shared tRP already; sku_rpshared differs on the read path's field alone)
            assert sorted(diff) == ["t_rp_ap_rd", "timing_preset"], (name, diff)
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
    test runs the RTL the lag was measured on (ap_fire_stale off) and the counters the board ran then (the margin
    set; at the phase-exact counters the bl4 read side is 520 with either lag -- tRC 6 leaves no slot for the hold to
    cost)."""
    import tempfile
    from dataclasses import replace
    sc = replace([s for s in cm.SUITES["all"] if s.name == "col_major_bl4"][0], txn_count=4096)
    bw = {}
    for hl in (1, 2):
        cfg = replace(cm.CONFIGS["granite_sku100_bi"], name=f"hl{hl}", hit_lag=hl, ap_fire_stale=False,
                      timing_preset=MARGIN, **MARGIN_AP)
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


def test_admission_gates_decide_the_mixed_close_page_turns():
    """MC-021 step 7: under close page with four writers and four readers on two banks, the direction register turns
    every 16 columns on the RTL (the holder's other bank drains behind the in-order hold's capped request, the
    waiting direction's lane-opened row then costs the holder its idle hold) and the two directions share the
    window almost equally (the proxy 56.3 / 57.0, the board 56 / 59). The model held to the 255-column cap
    instead -- its write turn's first ACT came one slot late, the reads took the bus back -- because its one
    three-slot admission stage was the pool path's; the bank-cap path is one slot shorter (a pop shows in the
    count the cap reads one slot later, the beat lands one slot after acceptance). With the gates the model's
    windows are the proxy's within a percent; with the old single stage the read window is 0.55 of the write one.
    The proxy's windows were measured at the margin counters, so the test runs them."""
    import tempfile
    from dataclasses import replace
    sc = replace([s for s in cm.SUITES["all"] if s.name == "mixed_bl8"][0], txn_count=512)
    res = {}
    for name, kw in (("gates", {}), ("admit3", dict(admit_lag=3, pool_gate_lag=0, cap_gate_lag=0))):
        cfg = replace(cm.CONFIGS["granite_sku100_close"], name=name, timing_preset=MARGIN, **MARGIN_AP, **kw)
        with tempfile.TemporaryDirectory() as t:
            r = cm.run_scenario(cfg, sc, t)
        res[name] = (int(r["wr_cycles"]), int(r["rd_cycles"]))
    wr, rd = res["gates"]
    assert 0.95 < rd / wr < 1.05, res                  # both directions span the whole window (the proxy 232852 / 229896)
    assert abs(wr - 232852) / 232852 < 0.05, res        # the proxy's write window at these counts
    wr3, rd3 = res["admit3"]
    assert rd3 / wr3 < 0.7, res                         # the single-stage model: the reads finish first


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


def test_close_lag_gives_the_open_page_mixed_cell_its_second_mode():
    """MC-021 step 8: the board's open_page mixed_bl8 cell runs in two modes (311 / 522 three runs of five, 272 / 272
    two), the proxy reproduces both when the refresh phase at GO is swept (tREFI 770 and 773 fast, 771 / 772 / 774 /
    776 / 780 slow), and the model reproduces both when ITS GO is swept against its refresh phase (GRANITE_GO_OFFSET,
    the frontend's start_tick) -- but only with the close lag: the record's hit flag is classified against the
    registered row image on the way down too, so a head whose row a PRE just closed requests its ACT two slots
    later, and at a cap flip the holder's hinted re-ACT reaches the contested bank before the waiter's. Without it
    every phase gives the slow mode. The fast mode is the register ping-ponging on zero-column write turns until the
    reads finish; the slow mode the 255 / 255 cap alternation."""
    import os
    import tempfile
    from dataclasses import replace
    sc = replace([s for s in cm.SUITES["all"] if s.name == "mixed_bl8"][0], txn_count=512)
    # the bimodal board cell is the open_page preset's (policy_mode 0, the flat close-on-drain): granite_sku100_open
    # since ISSUE-006; the board's `defaults` (the hybrid, granite_sku100) showed the slow mode on five of five runs.
    # The modes' numbers (272 / 522 on the board) are the margin counters', so the test runs them.
    # rfc_block=False: the model this was measured on (MC-023 item 4, 2026-11-24). With the tRFC demand block
    # the margin cell reads ~307 at both phases, the intermediate mode the phase-exact open_page cell shows; the
    # close lag's two-mode claim is pinned on the model it was made with.
    base = replace(cm.CONFIGS["granite_sku100_open"], timing_preset=MARGIN, rfc_block=False, **MARGIN_AP)
    rd = {}
    try:
        for lag in (2, 0):
            for off in (0, 480):
                os.environ["GRANITE_GO_OFFSET"] = str(off)
                with tempfile.TemporaryDirectory() as t:
                    r = cm.run_scenario(replace(base, name=f"cl{lag}o{off}", close_lag=lag), sc, t)
                rd[(lag, off)] = float(r["rd_bw_mb_s"])
        os.environ["GRANITE_GO_OFFSET"] = "480"
        with tempfile.TemporaryDirectory() as t:
            hyb = float(cm.run_scenario(replace(cm.CONFIGS["granite_sku100"], name="hyb_margin", rfc_block=False,
                                                timing_preset=MARGIN, **MARGIN_AP), sc, t)["rd_bw_mb_s"])
    finally:
        os.environ.pop("GRANITE_GO_OFFSET", None)
    assert cm.CONFIGS["granite_sku100"].close_lag == 2
    assert rd[(2, 0)] < 300 < 380 < rd[(2, 480)], rd       # both modes under the shipped terms
    assert rd[(0, 0)] < 300 and rd[(0, 480)] < 300, rd       # one mode without the close lag
    assert hyb < 300, hyb                                    # the hybrid (the board's defaults) stays in the slow mode at the fast phase


def test_board_compare_reads_a_bimodal_cell_by_mode(tmp_path):
    """MC-021 close-out: the board's open_page mixed_bl8 cell has two modes (311 / 522 and 272 / 272, the refresh
    phase at GO), so one board number per cell cannot judge the model. `board-compare` groups a cell's board runs
    (`--board-also` = the reruns) into modes within the tolerance of each other; every board mode needs a model run
    (one `--model` CSV per GO phase, labelled by the `GO offset` note) within tolerance, and a model run in a mode the
    board never showed is OUT. A cell with one run each keeps the one-run row exactly, so the earlier compares read
    the same."""
    import csv

    def write(path, fields, rows):
        with open(path, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fields)
            w.writeheader()
            w.writerows(rows)
        return str(path)

    bf = ["config", "scenario", "wr_bw_mb_s", "rd_bw_mb_s", "notes"]
    mf = ["config", "scenario", "wr_bw_mb_s", "rd_bw_mb_s", "bytes_moved", "wr_cycles", "rd_cycles", "notes"]
    b_fast = dict(config="open_page", scenario="mixed_bl8", wr_bw_mb_s=311, rd_bw_mb_s=522, notes="union 622.0 MB/s over 1 cycles")
    b_slow = dict(config="open_page", scenario="mixed_bl8", wr_bw_mb_s=272, rd_bw_mb_s=272, notes="union 545.0 MB/s over 1 cycles")
    b_plain = dict(config="open_page", scenario="random_bl8", wr_bw_mb_s=728, rd_bw_mb_s=757, notes="")
    write(tmp_path / "char_granite_t_every_2026-01-01.csv", bf, [b_fast, b_plain])
    rerun_slow = write(tmp_path / "rerun1.csv", bf, [b_slow])
    rerun_fast = write(tmp_path / "rerun2.csv", bf, [b_fast])
    # the test's board rows are the open_page preset, which BOARD_PRESET_OF maps to granite_sku100_open (ISSUE-006)
    m_slow = dict(config="granite_sku100_open", scenario="mixed_bl8", wr_bw_mb_s=274, rd_bw_mb_s=274,
                  bytes_moved=8192000, wr_cycles=2994444, rd_cycles=2992711, notes="")           # union 547
    m_fast = dict(config="granite_sku100_open", scenario="mixed_bl8", wr_bw_mb_s=309, rd_bw_mb_s=568,
                  bytes_moved=8192000, wr_cycles=2652660, rd_cycles=1441000,
                  notes="GO offset 480 ticks against the refresh phase")                           # union 618
    m_plain = dict(config="granite_sku100_open", scenario="random_bl8", wr_bw_mb_s=730, rd_bw_mb_s=752,
                   bytes_moved=1, wr_cycles=1, rd_cycles=1, notes="")
    model_slow = write(tmp_path / "model_slow.csv", mf, [m_slow, m_plain])
    model_fast = write(tmp_path / "model_fast.csv", mf, [m_fast])

    def compare(models, also):
        out = tmp_path / "out.md"
        rc = cm.main(["board-compare", "--model", *models, "--measured", str(tmp_path), "--granite", "t_2026-01-01",
                      "--board-also", *also, "--out", str(out), "--strict"])
        return rc, out.read_text()

    rc, text = compare([model_slow, model_fast], [rerun_slow, rerun_fast])
    assert rc == 0 and "2 cells in tolerance, 0 out" in text, text
    mixed = [ln for ln in text.splitlines() if "| mixed_bl8 |" in ln][0]
    assert "311 / 522 (union 622) x2; 272 / 272 (union 545) x1" in mixed, mixed
    assert "309 / 568 (union 618) [GO 480]" in mixed and "(union, by mode)" in mixed and mixed.endswith("| IN |"), mixed
    plain = [ln for ln in text.splitlines() if "| random_bl8 |" in ln][0]
    assert plain == "| open_page | random_bl8 | 728 / 757 | 730 / 752 | +0.3 / -0.7 % | 5 % | IN |", plain
    rc, text = compare([model_slow], [rerun_slow, rerun_fast])                 # the board's fast mode has no model run
    assert rc == 1 and "1 cells in tolerance, 1 out" in text, text
    rc, text = compare([model_slow, model_fast], [])                           # the model's slow run is a mode the board never showed
    assert rc == 1 and "1 cells in tolerance, 1 out" in text, text


def test_hybrid_page_policy_issues_the_demand_pres_the_boards_defaults_do():
    """ISSUE-006 (2026-11-20): the board's `defaults` preset is the hybrid page policy -- the drain auto-precharge
    only on a known conflict or where the bank's history arms it, otherwise the row stays open until the idle
    timeout (tr_init 2) or the next row's demand PRE closes it. The model's one policy before was the flat
    close-on-drain (the board's open_page preset, policy_mode 0), which never issues a demand PRE; MC-019's proxy
    counted ~700 per col_ilv run under the hybrid, 424 of them on the lane. The hybrid in the model issues demand
    PREs on the lane and background closes on that cell; mode 0 issues neither."""
    import tempfile
    from dataclasses import replace
    sc = replace([s for s in cm.SUITES["all"] if s.name == "col_major_interleaved_bl8"][0], txn_count=512)
    with tempfile.TemporaryDirectory() as t:
        hyb = cm.run_scenario(cm.CONFIGS["granite_sku100"], sc, t)
        flat = cm.run_scenario(cm.CONFIGS["granite_sku100_open"], sc, t)
    assert int(hyb["lane_pre"]) > 10 and int(hyb["to_pre"]) > 0, (hyb["lane_pre"], hyb["to_pre"])   # 40 and 4 at txn 512
    assert int(flat["lane_pre"]) == 0 and int(flat["to_pre"]) == 0, (flat["lane_pre"], flat["to_pre"])
    # both are the same stream through the same store and pick: the policy moves the cell by a few percent at most
    for k in ("wr_bw_mb_s", "rd_bw_mb_s"):
        assert 0.9 < float(hyb[k]) / float(flat[k]) < 1.1, (k, hyb[k], flat[k])


def test_rfc_block_is_the_sku_default_and_moves_the_first_act_after_a_refresh():
    """MC-023 item 4 (proxy probe 2026-11-24, tREFI 779, open_page mixed): the RTL grants REF, loads its tRFC
    counter (13 at the SKU's point) the cycle after, blocks every demand request and fire while it is non-zero, and
    fires the first ACT at grant + 16. The model with rfc_block fires it there; without, at the device's tRFC
    (grant + 13). The term is the SKU default and the mixed cells are the cells it moves (defaults 309 / 571 ->
    278 / 278 at GO 0, the board's 277 / 276 on ten of ten runs)."""
    assert cm.CONFIGS["granite_sku100"].rfc_block is True
    assert cm.CONFIGS["sku_norfcblock"].rfc_block is False


def test_read_priority_register_makes_the_mixed_cell_one_mode_and_bounds_the_writes():
    """MC-024 (priced 2026-11-24): the read-priority direction register (dir_mode 1) takes the board's fast shape
    as the rule. On the mixed cell under both open-page presets it is ONE mode at two GO phases a refresh period
    apart (the symmetric register is a race the refresh phase places, ISSUE-005), the reads and the union are
    above the symmetric register's, the reads' mean latency falls, and no write head waits much past
    wr_starve. At the CSR reset 512 / 128 (decision 1): ~455 MB/s reads, union ~599 against 555 / 581."""
    import os
    import tempfile
    from dataclasses import replace
    sc = replace([s for s in cm.SUITES["all"] if s.name == "mixed_bl8"][0], txn_count=4000)
    out = {}
    try:
        for cfg in ("granite_sku100", "granite_sku100_open"):
            for mode in (0, 1):
                for off in (0, 780):
                    os.environ["GRANITE_GO_OFFSET"] = str(off)
                    with tempfile.TemporaryDirectory() as t:
                        out[(cfg, mode, off)] = cm.run_scenario(
                            replace(cm.CONFIGS[cfg], name=f"rp{mode}o{off}", dir_mode=mode), sc, t)
    finally:
        os.environ.pop("GRANITE_GO_OFFSET", None)
    for cfg in ("granite_sku100", "granite_sku100_open"):
        rp = [out[(cfg, 1, off)] for off in (0, 780)]
        sym = out[(cfg, 0, 0)]
        rds = [float(r["rd_bw_mb_s"]) for r in rp]
        assert abs(rds[0] - rds[1]) / rds[0] < 0.02, (cfg, rds)                      # one mode
        assert min(rds) > 1.2 * float(sym["rd_bw_mb_s"]), (cfg, rds, sym["rd_bw_mb_s"])
        un = lambda r: float(re.search(r"union ([0-9.]+)", r["notes"])[1])
        assert min(un(r) for r in rp) > 1.02 * un(sym), (cfg, [un(r) for r in rp], un(sym))
        assert float(rp[0]["rd_avg_latency_cyc"]) < 0.95 * float(sym["rd_avg_latency_cyc"]), cfg   # open_page 13.5 vs 14.9 with the RTL-timed flag
        assert all(float(r["wr_wait_max"]) < cm.CONFIGS[cfg].wr_starve + 128 for r in rp), cfg
    assert cm.CONFIGS["granite_sku100"].dir_mode == 0 and cm.CONFIGS["sku_rdprio"].dir_mode == 1



def test_contended_write_rate_is_measured_while_the_reads_hold_the_bus():
    """MC-024 correction (2026-11-24): wr_bw_mb_s is the write window, which under read priority includes the
    writes-only tail after the reads end (124 MB/s on mixed_rd4 at 512 / 16, of which ~23 is the share while
    the reads run). wr_bw_rd_live_mb_s counts only the writes done by the last read completion. It is the
    write window itself when the writes finish first (the symmetric register), it is the same steady value at
    reads x4 and x16, and the two knobs move it: a long write burst at a short starvation bound lifts it past
    the symmetric register's."""
    import tempfile
    from dataclasses import replace
    base = [s for s in cm.SUITES["sustained"] if s.name == "mixed_rd4_bl8"][0]
    def run(p, **kw):
        sc = replace(base, name=f"mixed_rd{p}_bl8", param=p, txn_count=2000)
        with tempfile.TemporaryDirectory() as t:
            return cm.run_scenario(replace(cm.CONFIGS["granite_sku100"], name="live", **kw), sc, t)
    sym = run(4, dir_mode=0)
    assert float(sym["wr_bw_rd_live_mb_s"]) == float(sym["wr_bw_mb_s"])            # writes finished first
    rp4, rp16 = run(4, dir_mode=1, wr_burst=16), run(16, dir_mode=1, wr_burst=16)
    live4, live16 = float(rp4["wr_bw_rd_live_mb_s"]), float(rp16["wr_bw_rd_live_mb_s"])
    assert live4 < 0.4 * float(rp4["wr_bw_mb_s"]), (live4, rp4["wr_bw_mb_s"])      # the tail inflates the window
    assert abs(live4 - live16) / live16 < 0.1 and live16 < 40, (live4, live16)      # a steady floor
    wide = run(16, dir_mode=1, wr_starve=256, wr_burst=255)
    # the CSR reset (512 / 128, MC-024 decision 1): ~140 MB/s of writes under sustained reads
    reset = run(16, dir_mode=1)
    assert (cm.CONFIGS["granite_sku100"].wr_starve, cm.CONFIGS["granite_sku100"].wr_burst) == (512, 128)
    assert 120 < float(reset["wr_bw_rd_live_mb_s"]) < 160, reset["wr_bw_rd_live_mb_s"]
    assert float(wide["wr_bw_rd_live_mb_s"]) > float(sym["wr_bw_mb_s"]), wide["wr_bw_rd_live_mb_s"]
