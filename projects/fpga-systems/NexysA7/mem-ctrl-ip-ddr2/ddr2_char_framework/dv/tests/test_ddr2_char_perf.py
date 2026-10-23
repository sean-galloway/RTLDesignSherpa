# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-free perf proxy for PUMICE (CAM storage plane + the selected pick core):
incremental / row_major / col_ilv / col_major at the BOARD clock and geometry.

Sibling of test_granite_char_perf.py, which measures granite_core (entry store).
Until 2026-10-21 there was NO board-timing perf proxy for pumice with its CAMs;
the 100 MHz plan's "pumice baseline" was in fact the granite harness. This test
closes that gap (mem-ctrl recovery plan, Phase 0).

Fidelity argument (same as the granite proxy):
  * The DUT is the real pumice controller RTL (ddr2_char_uart_tb_top ->
    ddr2_char_harness -> ddr2_char_macro -> pumice_top_geared) enforcing its
    programmed JEDEC timings, derived from the part's ns specs at 75 MHz exactly
    like the board flow (set_jedec_timings).
  * DFISlavePHY + DramStateModel: address-accurate, JEDEC-checked (soft).
  * Address streams come from pumice_char.strides_for + the board Geometry, so
    the families produce the DRAM patterns silicon measures.
  * Bandwidth is the board's own formula, (bytes_moved / cycles) * clk_mhz, from
    the on-chip per-engine first/last timer stamps.

What this test ADDS over the granite proxy:
  * The JEDEC floor beside every col_major number: rd gap floor =
    tRTP + tRP + tRCD, wr gap floor = tWR + tRP + tRCD (pumice's tWR port is
    WR cmd -> earliest PRE), so a bandwidth number is read against what the
    programmed timings allow, not against a remembered LiteDRAM figure.
  * AR->firstR mean latency (cycles) from the harness log2 histogram.
  * TEST_TIMING_OVERRIDES="tRTP=1,tRP=2": patch programmed timings AFTER the
    board derivation (like-for-like comparisons; the RTL is untouched).
  * TEST_NUM_GEN=n: n writer + n reader generators, one per bank (start
    addresses one bank stride apart) -- the multi-thread case.
  * PERF_CMD_TRACE=1: per-kind (ACT/RD/WR/PRE) fire-gap histograms from the
    scheduler plane's evt_* strobes, plus the dominant inter-row gap, which is
    the number to compare with the floor.

Knobs: TEST_TREFI (585 = board), TEST_TXN (256), TEST_GAP (0), TEST_BURST_LEN
(8), TEST_FAMILIES, TEST_NUM_GEN (1), TEST_TIMING_OVERRIDES (""), PERF_DUMP,
PERF_CMD_TRACE, PERF_PICK_TRACE (per-cycle pick-core rows, _START/_N), TEST_SCHED_CORE (1 = BANK_PICK, 0 = FRFCFS). Geometry defaults to the BOARD: rate-2 / 32b beat / x16 / BL4
(TEST_DFI_RATE, TEST_DRAM_BEAT_BYTES, TEST_DRAM_DEVICE_BYTES, TEST_DRAM_BL).
Skipped at TEST_LEVEL=GATE (a multi-minute run is not a gate check).
"""

import json
import os
import sys

import pytest
import cocotb
from cocotb._bridge import bridge
from cocotb.triggers import ClockCycles, ReadOnly, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.components.dfi.dram_state import DramStateModel, ViolationPolicy
from CocoTBFramework.components.dfi.jedec_timings import timings_from_params

_REPO = os.environ["REPO_ROOT"]
_HOST = os.path.join(_REPO, "projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
                            "build-perf/host")
_TBC = os.path.join(_REPO, "projects/fpga-systems/rtl/mem_char_framework/dv/tbclasses")
for _p in (_HOST, _TBC):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.harness import UartSimHarness      # noqa: E402
import ddr2_char as dc                                    # noqa: E402
import pumice_char as pc                                  # noqa: E402
import pumice_master as pm                                # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Only the named helpers: importing the uart test's test_* functions would make
# pytest collect them a second time from this module.
from test_ddr2_char_uart import (                         # noqa: E402
    _make_dfi_slave, CLKS_PER_BIT, ROW_W, COL_W, NUM_BANKS, DRAM_BL,
    DFI_RATE, DRAM_BEAT_BYTES, GEAR_RATIO, DRAM_DEVICE_BYTES,
)
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

# --- BOARD clock (75 MHz). The JEDEC ns->cycle derivation is clock-dependent,
# so parity with the board needs the 75 MHz period, quantized to the 8 ps grain.
FPGA_CLK_HZ = int(os.environ.get("TEST_FPGA_CLK_HZ", "75000000"))
_PS_GRAIN = 8
_CLK_PERIOD_PS = _PS_GRAIN * round(1e12 / FPGA_CLK_HZ / _PS_GRAIN)  # 13336 ps
CLK_PERIOD_NS = _CLK_PERIOD_PS / 1000.0                             # 13.336 ns
CLK_ACTUAL_HZ = round(1e12 / _CLK_PERIOD_PS)                        # 75_001_875
UART_BAUD = FPGA_CLK_HZ // CLKS_PER_BIT

_FILELIST = ("projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
             "ddr2_char_framework/dv/filelists/ddr2_char_uart_tb_top.f")

# Silicon perf gates (shared with the granite proxy; col_major's 369 is the
# JEDEC floor at the board-derived timings, tRTP 2 / tRP 2 / tRCD 2).
GATES = {"row_major": 570, "col_ilv": 354, "col_major": 369}

_FAMILIES = {
    "incremental": pc.FAM_INCREMENTAL,
    "row_major": pc.FAM_ROW_MAJOR,
    "col_ilv":   pc.FAM_COL_INTERLEAVE,
    "col_major": pc.FAM_COL_MAJOR,
}

# Instance path to the scheduler plane. Logged, not asserted: a hierarchy
# change disables the trace rather than failing the measurement.
_SCHED_PATH = ("u_dut", "u_dut", "u_ctrl", "u_core", "u_core", "u_sched_plane")


def _sched_plane(dut):
    node = dut
    for name in _SCHED_PATH:
        node = getattr(node, name)
    return node


async def _pick_probe(dut, start, n):
    """PERF_PICK_TRACE=1: log the BANK_PICK core's per-cycle state for cycles
    [start, start+n) of the run (PERF_PICK_TRACE_START / _N), the same row
    the core suite's PICK_TRACE prints: effective winner, fire / gates,
    request bits, shadow, override, sink and refresh state. Silent on the
    FRFCFS core."""
    try:
        sp = _sched_plane(dut)
        pk = sp.g_bank_pick.u_bank_pick
    except AttributeError as e:
        dut._log.info("PERF_PICK_TRACE: pick core absent (%r)", e)
        return
    cyc = 0
    while True:
        await RisingEdge(dut.aclk)
        await ReadOnly()
        cyc += 1
        if start <= cyc < start + n:
            try:
                dut._log.info(
                    "PK c%d win=(%d,%d,%d) ok=%d fire=%d spec=%d cls_ok=%d tmr_ok=%d hit=%d "
                    "req=%04x reqok=%04x hint=%d(%d,%d) sh=%04x hold=%d ovr=%d(%d) wcr=%d rdr=%d "
                    "dir=%d batch=%d rotor=%d tccd=%d refreq=%d rfc=%d topre=%d treq=%d tbank=%d prerdy=%d",
                    cyc, int(pk.w_win_vld.value), int(pk.w_win_pair.value), int(pk.w_win_cls.value),
                    int(pk.w_dmd_ok.value), int(pk.w_fire.value), int(pk.w_spec_vld.value),
                    int(pk.w_class_ok.value), int(pk.w_timer_ok.value), int(pk.w_sel_hit.value),
                    int(pk.r_req.value), int(pk.w_req_ok.value), int(pk.r_hint_vld.value),
                    int(pk.r_hint_pair.value), int(pk.r_hint_cls.value), int(pk.r_shadow.value),
                    int(pk.r_hold.value), int(pk.w_ovr_vld.value), int(pk.w_ovr_op.value),
                    int(pk.wr_commit_ready_now_i.value), int(pk.rd_issue_ready_i.value),
                    int(pk.r_dir.value), int(pk.r_dir_batch.value), int(pk.r_rotor.value),
                    int(pk.r_tccd_fwd.value), int(sp.refresh_req.value), int(pk.w_rfc_busy.value), int(pk.w_to_pre.value), int(pk.timeout_pre_req_i.value), int(pk.timeout_pre_bank_i.value), int(pk.bank_pre_ready_i.value))
            except Exception as e:  # noqa: BLE001
                dut._log.info("PK c%d probe error %r", cyc, e)
        if cyc >= start + n:
            return


async def _cmd_probe(dut, log):
    """PERF_CMD_TRACE=1: log every scheduler fire as (kind, cycle) from the
    scheduler plane's evt_* strobes (both pick cores drive them). Sampled in
    the ReadOnly phase so the combinational strobes are settled."""
    try:
        sp = _sched_plane(dut)
        s_act, s_rd, s_wr, s_pre = sp.evt_act, sp.evt_rd, sp.evt_wr, sp.evt_pre
    except AttributeError as e:
        dut._log.info("PERF_CMD_TRACE: scheduler plane probe absent (%r)", e)
        return
    cyc = 0
    while True:
        await RisingEdge(dut.aclk)
        await ReadOnly()
        cyc += 1
        try:
            if int(s_rd.value):
                log.append(("RD", cyc))
            elif int(s_wr.value):
                log.append(("WR", cyc))
            elif int(s_act.value):
                log.append(("ACT", cyc))
            elif int(s_pre.value):
                log.append(("PRE", cyc))
        except Exception:
            pass


def _gap_stats(log, kind):
    ts = [c for k, c in log if k == kind]
    if len(ts) < 2:
        return {"n": len(ts), "gaps": []}
    gaps = [b - a for a, b in zip(ts, ts[1:])]
    hist = {}
    for g in gaps:
        hist[g] = hist.get(g, 0) + 1
    # Dominant inter-row gap: the most frequent gap above 1 (1 = same-row
    # streaming). Refresh episodes show up as rare large gaps and do not win.
    inter = {g: n for g, n in hist.items() if g > 1}
    dominant = max(inter.items(), key=lambda kv: kv[1])[0] if inter else None
    return {"n": len(ts), "gaps": gaps[:64],
            "mean": round(sum(gaps) / len(gaps), 3),
            "inter_row_gap": dominant,
            "hist": dict(sorted(hist.items()))}


async def _mism_probe(dut, log, limit=4096):
    """MISM_PROBE=1: latch (beat, exp, act) for every mismatching read beat on
    the gen0 debug tap -- localizes read-stream corruption without touching
    RTL. beat = R-beat ordinal from stream start (same tap the granite proxy
    uses; the harness is shared)."""
    try:
        blk = dut.u_dut.u_dut
        sig_v, sig_m = blk.rd_dbg_valid, blk.rd_dbg_mismatch
        sig_e, sig_a = blk.rd_dbg_expected, blk.rd_dbg_actual
    except AttributeError as e:
        dut._log.info("MISM_PROBE: dbg tap absent (%r)", e)
        return
    beat = 0
    while True:
        await RisingEdge(dut.aclk)
        try:
            if int(sig_v.value):
                if int(sig_m.value) and len(log) < limit:
                    log.append({"beat": beat, "exp": hex(int(sig_e.value)),
                                "act": hex(int(sig_a.value))})
                beat += 1
        except Exception:
            pass


def _addr_hash32(addr, s0, s1, s2):
    """Mirror of f_addr_hash32 (axi4_master_wr_injector.sv / rd_crc_check.sv);
    same as bin/TBClasses/axi4/axi4_master_wr_injector_tb.py::addr_hash32."""
    m = 0xFFFFFFFF
    rotl = lambda x, k: ((x << k) | (x >> (32 - k))) & m
    x = (addr ^ s0) & m
    x = (x ^ rotl(x, 23)) & m
    x = (x ^ s1) & m
    x = (x ^ rotl(x, 21)) & m
    x = (x ^ rotl(x, 17)) & m
    x = (x ^ s2) & m
    x = (x ^ rotl(x, 7)) & m
    return x


def _hash_beat(addr, seed):
    s0, s1, s2 = seed, seed ^ 0x9E3779B9, seed ^ 0x85EBCA6B
    return _addr_hash32(addr, s0, s1, s2) | (_addr_hash32(addr + 4, s0, s1, s2) << 32)


async def _axi_r_probe(dut, log, seed, limit=600):
    """AXI_R_PROBE=1: at the controller's host AXI port record every AR
    (addr, len) and every R beat (data, last). Post-run, each R beat is
    matched against the hash of the address it SHOULD carry (AR order, beat
    order) and, on a mismatch, against the hash table of every address read
    -- so a wrong beat names the address whose data it actually holds."""
    try:
        c = dut.u_dut.u_dut.u_ctrl
        arv, arr, ara, arl = c.s_axi_arvalid, c.s_axi_arready, c.s_axi_araddr, c.s_axi_arlen
        rv, rr, rd, rl = c.s_axi_rvalid, c.s_axi_rready, c.s_axi_rdata, c.s_axi_rlast
    except AttributeError as e:
        dut._log.info("AXI_R_PROBE: port absent (%r)", e)
        return
    ars, rs = log["ar"], log["r"]
    while True:
        await RisingEdge(dut.aclk)
        await ReadOnly()
        try:
            if int(arv.value) and int(arr.value) and len(ars) < limit:
                ars.append((int(ara.value), int(arl.value)))
            if int(rv.value) and int(rr.value) and len(rs) < limit * 8:
                rs.append((int(rd.value), int(rl.value)))
        except Exception:
            pass


def _axi_r_report(log, seed, beat_bytes):
    ars, rs = log["ar"], log["r"]
    # expected beat address stream in AR order
    exp_addrs = []
    for a, ln in ars:
        exp_addrs.extend(a + beat_bytes * i for i in range(ln + 1))
    table = {_hash_beat(a, seed): a for a in exp_addrs}
    rows = []
    bad = 0
    for i, (data, last) in enumerate(rs[:len(exp_addrs)]):
        ea = exp_addrs[i]
        ok = (data & 0xFFFFFFFFFFFFFFFF) == _hash_beat(ea, seed)
        if not ok:
            bad += 1
            if len(rows) < 24:
                rows.append({"beat": i, "exp_addr": hex(ea),
                             "data_is_addr": hex(table[data]) if data in table else "unknown",
                             "last": last})
    return {"n_ar": len(ars), "n_r": len(rs), "n_exp_beats": len(exp_addrs),
            "bad": bad, "first_bad": rows}


async def _dfi_rd_trace(dut, log, limit=40):
    """DFI_RD_TRACE=1: cycle-stamped timeline of the read return path --
    RD commands on the DFI pins (per phase), the aligner's admit, enable,
    rddata_valid and capture strobes. First `limit` events of each kind, so
    the first read of a phase can be read off against the model's return."""
    try:
        cs, ras, cas, we = dut.phy_dfi_cs_n, dut.phy_dfi_ras_n, dut.phy_dfi_cas_n, dut.phy_dfi_we_n
        rdv, rde = dut.phy_dfi_rddata_valid, dut.phy_dfi_rddata_en
        al = dut.u_dut.u_dut.u_ctrl.u_core.u_core.u_dfi_plane.u_rd
        adm, en, cap, outst, cred = al.w_admit, al.w_en, al.w_cap_fire, al.r_outstanding, al.w_credit_avail
    except AttributeError as e:
        dut._log.info("DFI_RD_TRACE: probe absent (%r)", e)
        return
    rate = DFI_RATE
    cyc = 0
    counts = {}
    def put(kind, info=""):
        n = counts.get(kind, 0)
        if n < limit:
            log.append((cyc, kind, info))
        counts[kind] = n + 1
    while True:
        await RisingEdge(dut.aclk)
        await ReadOnly()
        cyc += 1
        try:
            c, r, ca, w = int(cs.value), int(ras.value), int(cas.value), int(we.value)
            for p in range(rate):
                if (c >> p) & 1:
                    continue
                key = ((r >> p) & 1, (ca >> p) & 1, (w >> p) & 1)
                if key == (1, 0, 1):
                    put("RD_pin", f"ph{p}")
                elif key == (1, 0, 0):
                    put("WR_pin", f"ph{p}")
                elif key == (0, 1, 1):
                    put("ACT_pin", f"ph{p}")
                elif key == (0, 1, 0):
                    put("PRE_pin", f"ph{p}")
            if int(adm.value):
                put("admit", f"outst={int(outst.value)}")
            if int(en.value):
                put("en", f"cred={int(cred.value)}")
            if int(rdv.value):
                put("valid", f"cred={int(cred.value)} outst={int(outst.value)}")
            if int(cap.value):
                put("capture")
        except Exception:
            pass


def _hist_mean_cycles(counts, total):
    """Mean of the harness log2 latency histogram (pumice_char semantics: bin b
    covers [2^b, 2^(b+1)), midpoint 1.5*2^b, bin 0 weight 1)."""
    if total <= 0:
        return 0.0
    acc = 0.0
    for b, cnt in enumerate(counts):
        acc += cnt * (1.0 if b == 0 else 1.5 * (1 << b))
    return acc / total


def _parse_overrides(spec):
    out = {}
    for item in [x.strip() for x in spec.split(",") if x.strip()]:
        k, v = item.split("=")
        out[k.strip()] = int(v.strip(), 0)
    return out


def _floors(timings, blen, bytes_per_col, clk_mhz):
    """JEDEC floors at the PROGRAMMED timings, in the board's bandwidth units.
    col_major: one AXI txn = `blen` columns to one row, then a same-bank row
    switch; the row period is (blen-1) same-row gaps of 1 plus the inter-row
    gap. row_major/incremental: one column per cycle."""
    row_bytes = blen * bytes_per_col
    rd_gap = timings["tRTP"] + timings["tRP"] + timings["tRCD"]
    wr_gap = timings["tWR"] + timings["tRP"] + timings["tRCD"]
    return {
        "col_major_rd_gap": rd_gap, "col_major_wr_gap": wr_gap,
        "col_major_rd_bw": round(row_bytes / (blen - 1 + rd_gap) * clk_mhz, 1),
        "col_major_wr_bw": round(row_bytes / (blen - 1 + wr_gap) * clk_mhz, 1),
        "stream_bw": round(bytes_per_col * clk_mhz, 1),
    }


# MT47H64M16HR part values (the vendored ddr2-650-mt47h64m16hr.csv), converted
# at the SIM's MC period rather than the CSV's 3.077 ns tCK. The uart suite's
# checker inherits the CSV conversion, so at 75 MHz it demands 2.2x the cycles
# JEDEC does (tRFC 42 cycles, tRAS 15, tWR 5) and reports thousands of phantom
# violations. One MC cycle = 2 CK at DFI_RATE=2, so a CK-quoted minimum (tWTR,
# tRTP, tCCD) is folded in with the same ceiling the host derivation uses.
_PART_NS = dict(tRCD_ns=15.0, tRP_ns=15.0, tRAS_min_ns=45.0, tRC_ns=60.0,
                tWR_ns=15.0, tWTR_ns=7.5, tRTP_ns=7.5, tRRD_ns=7.5,
                tFAW_ns=45.0, tREFI_ns=7800.0, tRFC_ns=127.5)


def _calibrated_checker(dut, slave):
    """Replace the BFM's violation checker with one whose cycle unit is the
    MC clock the DUT and the harness actually run. Returns the model so the
    test can read soft_violation_counts() after the run.

    CL / CWL / BL are kept at the slave's ORIGINAL values on purpose: the
    DFISlavePHY times its read return and write capture off dram.timings.CL /
    CWL (MC cycles here), and the uart suite's controller alignment
    (t_rddata_en=4 against a CL=5 return) is tuned to them. Setting CL=3 in
    the first version of this helper returned the first read's data one
    cycle before the aligner's enable window; the aligner credit-blocked it,
    and the whole stream shifted one ticket (2026-10-21, 127/128 beats
    mismatched, read engine never done). Only the JEDEC windows are rescaled.
    """
    base_t = slave.dram.timings
    t = timings_from_params(tCK_ns=CLK_PERIOD_NS, CL=int(base_t.CL),
                            CWL=int(base_t.CWL), BL=int(base_t.BL),
                            **_PART_NS)
    model = DramStateModel(timings=t, num_banks=NUM_BANKS,
                           policy=ViolationPolicy(hard=frozenset()),
                           log=dut._log)
    slave.dram = model
    return model


# RTL snapshot paths for a stalled engine (logged, never asserted).
_SNAP = [
    ("store.wr_sch_valid", _SCHED_PATH[:-1] + ("u_store_plane", "wr_sch_valid_o")),
    ("store.rd_sch_valid", _SCHED_PATH[:-1] + ("u_store_plane", "rd_sch_valid_o")),
    ("store.wr_commit_ready", _SCHED_PATH[:-1] + ("u_store_plane", "wr_commit_ready_o")),
    ("store.aw_push_ready", _SCHED_PATH[:-1] + ("u_store_plane", "aw_push_ready_o")),
    ("store.wd_ready", _SCHED_PATH[:-1] + ("u_store_plane", "wd_ready_o")),
    ("store.busy", _SCHED_PATH[:-1] + ("u_store_plane", "busy_o")),
    ("sched.refresh_req", _SCHED_PATH + ("refresh_req",)),
    ("sched.refresh_drain", _SCHED_PATH + ("refresh_drain",)),
    ("sched.a_cmd_valid", _SCHED_PATH + ("a_cmd_valid",)),
    ("sched.a_cmd_ready", _SCHED_PATH + ("a_cmd_ready",)),
    ("sched.cmd_fifo_rd_valid", _SCHED_PATH + ("w_cmd_rd_valid",)),
    ("sched.tok_cnt", _SCHED_PATH + ("r_tok_cnt",)),
    ("arb.r_pick_valid", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_pick_valid")),
    ("arb.r_do_act", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_do_act")),
    ("arb.r_do_wr", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_do_wr")),
    ("arb.r_do_pre", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_do_pre")),
    ("arb.r_bank", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_bank")),
    ("arb.w_out_safe", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_out_safe")),
    ("arb.w_out_hold", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_out_hold")),
    ("arb.bank_act_ready", _SCHED_PATH + ("g_arbiter", "u_arbiter", "bank_act_ready_i")),
    ("arb.bank_rdwr_ready", _SCHED_PATH + ("g_arbiter", "u_arbiter", "bank_rdwr_ready_i")),
    ("arb.bank_pre_ready", _SCHED_PATH + ("g_arbiter", "u_arbiter", "bank_pre_ready_i")),
    ("arb.bank_row_active", _SCHED_PATH + ("g_arbiter", "u_arbiter", "bank_row_active_i")),
    ("arb.r_ap_closing", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_ap_closing")),
    ("arb.w_rfc_busy", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_rfc_busy")),
    ("arb.r_guard0", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_guard0")),
    ("arb.r_guard1", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_guard1")),
    ("arb.wr_commit_ready", _SCHED_PATH + ("g_arbiter", "u_arbiter", "wr_commit_ready_i")),
    ("arb.cmd_ready", _SCHED_PATH + ("g_arbiter", "u_arbiter", "cmd_ready_i")),
    # refresh-episode internals (the 2026-10-21 col_major write deadlock)
    ("sched.refresh_kind", _SCHED_PATH + ("w_refresh_kind",)),
    ("sched.refresh_bank", _SCHED_PATH + ("w_refresh_bank",)),
    ("sched.refresh_grant", _SCHED_PATH + ("refresh_grant",)),
    ("arb.r_grant", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_grant")),
    ("arb.r_maint_grant", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_maint_grant")),
    ("arb.w_guarded", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_guarded")),
    ("arb.w_any_active", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_any_active")),
    ("arb.w_rfsh_pre_found", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_rfsh_pre_found")),
    ("arb.w_ref_safe", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_ref_safe")),
    ("arb.w_refpb_safe", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_refpb_safe")),
    ("arb.w_inflight_preact", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_inflight_preact")),
    ("arb.r_bank_row_active", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_bank_row_active")),
    ("arb.r_bank_pre_ready", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_bank_pre_ready")),
    ("arb.w_ref_col_block", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_ref_col_block")),
    ("arb.maint_busy", _SCHED_PATH + ("g_arbiter", "u_arbiter", "maint_busy_i")),
    ("arb.w_zq_busy", _SCHED_PATH + ("g_arbiter", "u_arbiter", "w_zq_busy")),
    ("arb.r_wr_drain", _SCHED_PATH + ("g_arbiter", "u_arbiter", "r_wr_drain")),
    # read return path (the 2026-10-21 col_major one-beat shift)
    ("ring.r_head", _SCHED_PATH[:-1] + ("u_axi_plane", "u_rd_ring", "r_head")),
    ("ring.r_tail", _SCHED_PATH[:-1] + ("u_axi_plane", "u_rd_ring", "r_tail")),
    ("ring.r_occ", _SCHED_PATH[:-1] + ("u_axi_plane", "u_rd_ring", "r_occ")),
    ("ring.iq_rd_valid", _SCHED_PATH[:-1] + ("u_axi_plane", "u_rd_ring", "w_iq_rd_valid")),
    ("aligner.r_outstanding", _SCHED_PATH[:-1] + ("u_dfi_plane", "u_rd", "r_outstanding")),
    ("aligner.r_credit", _SCHED_PATH[:-1] + ("u_dfi_plane", "u_rd", "r_credit")),
    ("aligner.r_rcnt", _SCHED_PATH[:-1] + ("u_dfi_plane", "u_rd", "r_rcnt")),
    ("aligner.dbg_captured", _SCHED_PATH[:-1] + ("u_dfi_plane", "u_rd", "dbg_captured")),
    ("aligner.dbg_blocked_pre", _SCHED_PATH[:-1] + ("u_dfi_plane", "u_rd", "dbg_blocked_pre")),
    ("aligner.dbg_first_blk_outst", _SCHED_PATH[:-1] + ("u_dfi_plane", "u_rd", "dbg_first_blk_outst")),
]


def _snapshot(dut):
    out = {}
    for name, path in _SNAP:
        node = dut
        try:
            for p in path:
                node = getattr(node, p)
            out[name] = hex(int(node.value))
        except Exception as e:  # noqa: BLE001 -- a missing probe is data
            out[name] = f"n/a ({type(e).__name__})"
    return out


async def _bringup(dut):
    """Identical to the pumice uart bringup but at the 75 MHz board period."""
    h = UartSimHarness(dut, clks_per_bit=CLKS_PER_BIT,
                       clk_period_ns=CLK_PERIOD_NS,
                       idle_inputs={"phy_dfi_init_complete": 0,
                                    "phy_dfi_ctrlupd_ack": 0,
                                    "phy_dfi_phyupd_req": 0,
                                    "phy_dfi_phyupd_type": 0})
    chan = await h.start()
    dfi_slave, memory = _make_dfi_slave(dut)
    _calibrated_checker(dut, dfi_slave)

    async def _assert_init_complete():
        await ClockCycles(dut.aclk, 20)
        dut.phy_dfi_init_complete.value = 1
    cocotb.start_soon(_assert_init_complete())

    drv = dc.DDR2CharDriver(bridge=h.make_bridge())
    return drv, chan, dfi_slave, memory


@cocotb.test(timeout_time=60000, timeout_unit="ms")
async def cocotb_test_pumice_perf(dut):
    drv, chan, _dfi, _mem = await _bringup(dut)

    t_refi = int(os.environ.get("TEST_TREFI", "585"), 0)
    txn = int(os.environ.get("TEST_TXN", "256"), 0)
    gap = int(os.environ.get("TEST_GAP", "0"), 0)
    blen = int(os.environ.get("TEST_BURST_LEN", "8"), 0)
    n_gen = int(os.environ.get("TEST_NUM_GEN", "1"), 0)
    overrides = _parse_overrides(os.environ.get("TEST_TIMING_OVERRIDES", ""))
    clk_mhz = CLK_ACTUAL_HZ / 1e6
    fam_names = [f.strip() for f in
                 os.environ.get("TEST_FAMILIES",
                                "incremental,row_major,col_ilv,col_major").split(",")]
    geom = pc.DEFAULT_GEOM
    dump_path = os.environ.get("PERF_DUMP", "")
    beat_bytes = 1 << dc.AXI_SIZE_8
    diag = {}
    # PERF_HOST_DIAG=1: record the stall attribution and page stats after EVERY
    # phase, not only a stalled one (the FR-FCFS plateau investigation,
    # 2026-10-22: a pattern-independent 307 / 354 from four threads up)
    always_diag = os.environ.get("PERF_HOST_DIAG", "0") == "1"

    def _host_diag(d):
        """What the CSRs say about a stalled engine: status bits, the
        scheduler's stall attribution, page stats. Absolute counters."""
        out = {}
        try:
            out["status"] = str(d.status())
            out["gen_done(wr,rd)"] = d.gen_done()
            out["gen_errors(wr_bresp,rd_any)"] = d.gen_errors()
        except Exception as e:  # noqa: BLE001
            out["status"] = f"n/a ({e!r})"
        st = pc._try_stalls(d)
        out["stalls"] = str(st) if st is not None else "n/a"
        ps = pc._try_page_stats(d)
        out["page_stats"] = str(ps) if ps is not None else "n/a"
        return out

    def measure_family(fam_key):
        fam = _FAMILIES[fam_key]
        stride, wrap = pc.strides_for(pc.Scenario(name=fam, family=fam,
                                                  burst_len=blen, txn_count=txn),
                                      geom)
        bytes_moved = txn * blen * beat_bytes * n_gen
        seed = 0xABCD1234

        def prog_for(g):
            # Generators one bank stride apart: each thread owns a bank for the
            # page-friendly families and the threads bank-interleave on
            # col_major -- the multi-thread case the controller should win.
            s = seed + 0x1000 * g
            return dict(start_addr=g * geom.bank_stride, burst_len=blen,
                        txn_count=txn, stride_0=stride, wrap_mask_0=wrap, gap=gap,
                        id_mode=dc.ID_MODE_FIXED, axi_size=dc.AXI_SIZE_8,
                        data_mode=True, lfsr_seed=s,
                        hash_seed0=s, hash_seed1=s ^ 0x9E3779B9,
                        hash_seed2=s ^ 0x85EBCA6B, gen=g)

        mask = (1 << n_gen) - 1

        # write phase (meters/timer frozen around programming, window = stamps)
        drv.freeze_trace(True)
        for g in range(n_gen):
            drv.program_wr_engine(**prog_for(g))
        drv.clear_stats()
        drv.timer_clear()
        drv.freeze_trace(False)
        drv.start_wr(mask)
        wr_ok = pm.wait_engine(drv, "wr", timeout_s=120, ignore_error=True)
        if not wr_ok or always_diag:
            diag["wr_" + fam_key] = _host_diag(drv)
        drv.freeze_trace(True)
        tw = drv.timer()
        wr_cycles = max(int(tw.w_last) - int(tw.w_first), 0)
        wr_util = drv.perf_meters()["wr"].prod / max(wr_cycles, 1)
        wr_hist, wr_tot = drv.perf_hist_dump(dc.HIST_BUS_WR, dc.HIST_METRIC_0)

        # read phase
        for g in range(n_gen):
            drv.program_rd_engine(**prog_for(g))
        drv.clear_stats()
        drv.timer_clear()
        drv.freeze_trace(False)
        drv.start_rd(mask)
        rd_ok = pm.wait_engine(drv, "rd", timeout_s=120, ignore_error=True)
        if not rd_ok or always_diag:
            diag["rd_" + fam_key] = _host_diag(drv)
        drv.freeze_trace(True)
        tr = drv.timer()
        rd_cycles = max(int(tr.r_last) - int(tr.r_first), 0)
        rd_util = drv.perf_meters()["rd"].prod / max(rd_cycles, 1)
        rd_hist, rd_tot = drv.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)

        mism = drv.beats_mismatched()
        return {
            "family": fam_key, "stride": stride, "wrap": wrap,
            "txn": txn, "burst_len": blen, "num_gen": n_gen,
            "bytes_moved": bytes_moved,
            "wr_ok": bool(wr_ok), "rd_ok": bool(rd_ok), "mismatched": int(mism),
            "wr_cycles": int(wr_cycles), "rd_cycles": int(rd_cycles),
            "wr_util": round(float(wr_util), 4), "rd_util": round(float(rd_util), 4),
            "wr_bw_mb_s": round(bytes_moved / wr_cycles * clk_mhz, 1) if wr_cycles else 0.0,
            "rd_bw_mb_s": round(bytes_moved / rd_cycles * clk_mhz, 1) if rd_cycles else 0.0,
            "wr_lat_cyc": round(_hist_mean_cycles(wr_hist, wr_tot), 1),
            "rd_lat_cyc": round(_hist_mean_cycles(rd_hist, rd_tot), 1),
            "clk_mhz": round(clk_mhz, 4),
        }

    def prog():
        out = {"clk_mhz": round(clk_mhz, 4), "t_refi": t_refi, "num_gen": n_gen,
               "dut": "pumice", "families": {}}
        drv.soft_reset()
        if n_gen > 1:
            cfg = drv.sync_gen_config()
            assert n_gen <= drv.num_gen, \
                f"TEST_NUM_GEN={n_gen} but the harness has {drv.num_gen} ({cfg})"
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=int(os.environ.get("TEST_T_PHY_WRLAT", "0")),
                               t_rddata_en=int(os.environ.get("TEST_T_RDDATA_EN", "4")),
                               rd_in_order=True)
        page_pol = os.environ.get("TEST_PAGE_POLICY", "")
        if page_pol:
            drv.set_page_policy(int(page_pol, 0))
            out["page_policy"] = int(page_pol, 0)
        # TEST_PAGE_MODE: PAGE_POLICY_CFG.policy_mode (1 static_open, 2
        # static_close, 3 fixed_open); TEST_TR_INIT: PAGE_TIMEOUT_CFG.tr_init
        # (0 disables the idle-timeout close). TEST_PAGE_POLICY above writes the
        # LEGACY policy field only; these two reach the page-policy engine.
        page_mode = os.environ.get("TEST_PAGE_MODE", "")
        if page_mode:
            drv.set_page_mode(int(page_mode, 0))
            out["page_mode"] = int(page_mode, 0)
        tr_init = os.environ.get("TEST_TR_INIT", "")
        if tr_init:
            drv.set_page_timeout_cfg(tr_init=int(tr_init, 0))
            out["tr_init"] = int(tr_init, 0)
        drv.set_dfi_phase(rd_phase=int(os.environ.get("TEST_RD_PHASE", "0")),
                          wr_phase=int(os.environ.get("TEST_WR_PHASE", "0")),
                          gear_ratio=GEAR_RATIO, bl=DRAM_BL)
        # Part-derived timings at the 75 MHz board clock (like the board), then
        # any like-for-like overrides on top. Both recorded.
        timings = drv.set_jedec_timings(
            float(FPGA_CLK_HZ), t_rddata_en=4, rddata_delay=0, t_phy_wrlat=0)
        if overrides:
            timings.update(drv.pumice.set_jedec_timings(overrides))
            out["timing_overrides"] = overrides
        out["timings"] = timings
        drv.set_refresh_interval(t_refi)
        # One DRAM column command moves DRAM_BL device words.
        out["floors"] = _floors(timings, blen, DRAM_BL * DRAM_DEVICE_BYTES, clk_mhz)
        for fam_key in fam_names:
            out["families"][fam_key] = measure_family(fam_key)
        out["host_diag"] = diag
        return out

    cmd_log = []
    tracing = os.environ.get("PERF_CMD_TRACE", "0") == "1"
    if tracing:
        cocotb.start_soon(_cmd_probe(dut, cmd_log))
    if os.environ.get("PERF_PICK_TRACE", "0") == "1":
        cocotb.start_soon(_pick_probe(dut, int(os.environ.get("PERF_PICK_TRACE_START", "400")),
                                      int(os.environ.get("PERF_PICK_TRACE_N", "120"))))
    mism_log = []
    if os.environ.get("MISM_PROBE", "0") == "1":
        cocotb.start_soon(_mism_probe(dut, mism_log))
    axi_log = {"ar": [], "r": []}
    if os.environ.get("AXI_R_PROBE", "0") == "1":
        cocotb.start_soon(_axi_r_probe(dut, axi_log, 0xABCD1234))
    dfi_log = []
    if os.environ.get("DFI_RD_TRACE", "0") == "1":
        cocotb.start_soon(_dfi_rd_trace(dut, dfi_log))

    r = await bridge(prog)()
    fams = r["families"]
    # The counts live on the ViolationPolicy (dram.policy), not the model --
    # MC-003 lost a whole session to the silently-empty dict this mistake
    # produces. Property or method, either way.
    _svc = getattr(_dfi.dram.policy, "soft_violation_counts", {})
    r["model_violations"] = dict(_svc() if callable(_svc) else _svc)
    # MEM_DUMP_ROWS=n: where did the col_major writes LAND? Dump the first 64 B
    # of bank 0 rows 0..n-1 from the BFM memory (device-word granular), and
    # list every bank-0 row that holds any nonzero data. Tells write-path
    # misplacement from read-path corruption without a waveform.
    n_rows = int(os.environ.get("MEM_DUMP_ROWS", "0"))
    if n_rows:
        import numpy as np
        mp = _dfi.mapping
        dump = {}
        for row in range(n_rows):
            flat = mp.tuple_to_flat(0, 0, row, 0)
            b = _mem.read(flat * DRAM_DEVICE_BYTES, 64)
            dump[f"bank0_row{row}"] = bytes(b).hex()
        # nonzero rows in bank 0: one page = num_cols device words
        ncols = mp.num_cols
        nz_rows = []
        for row in range(mp.num_rows):
            flat = mp.tuple_to_flat(0, 0, row, 0)
            a = flat * DRAM_DEVICE_BYTES
            if np.any(_mem.mem[a:a + ncols * DRAM_DEVICE_BYTES]):
                nz_rows.append(row)
                if len(nz_rows) >= 64:
                    break
        dump["bank0_nonzero_rows"] = nz_rows
        # and other banks, row 0..3, nonzero?
        for bk in range(1, NUM_BANKS):
            hit = [row for row in range(min(mp.num_rows, 64))
                   if np.any(_mem.mem[mp.tuple_to_flat(0, bk, row, 0) * DRAM_DEVICE_BYTES:
                                      mp.tuple_to_flat(0, bk, row, 0) * DRAM_DEVICE_BYTES
                                      + ncols * DRAM_DEVICE_BYTES])]
            if hit:
                dump[f"bank{bk}_nonzero_rows<64"] = hit
        r["mem_dump"] = dump
        dut._log.info("MEM_DUMP: %s", dump)
    if dfi_log:
        # Only the READ-side events after the first RD on the pins matter; the
        # write phase's ACT/WR/PRE are dropped from the printout.
        first_rd = next((c for c, k, _ in dfi_log if k == "RD_pin"), None)
        ev = sorted(e for e in dfi_log if first_rd is not None and e[0] >= first_rd - 2)
        r["dfi_rd_trace"] = ev[:120]
        dut._log.info("DFI_RD_TRACE (cycle, kind, info), first RD at %s: %s", first_rd, ev[:60])
    if axi_log["ar"]:
        # The probe sees the AR/R of every family in the run; with
        # TEST_FAMILIES=col_major and the write phase first, the AR stream is
        # the col_major read stream only (writes use AW/W).
        rep = _axi_r_report(axi_log, 0xABCD1234, beat_bytes)
        r["axi_r_report"] = rep
        dut._log.info("AXI_R_PROBE: %s", rep)
    if mism_log:
        r["mismatches"] = mism_log
        dut._log.info("MISM_PROBE: %d bad beats; first 16: %s", len(mism_log), mism_log[:16])
    stalled = [k for k, f in fams.items() if not (f["wr_ok"] and f["rd_ok"])]
    if stalled:
        r["rtl_snapshot"] = _snapshot(dut)
        dut._log.info("STALLED %s -- host diag: %s", stalled, r["host_diag"])
        dut._log.info("STALLED %s -- RTL snapshot: %s", stalled, r["rtl_snapshot"])
    dut._log.info("DRAM model soft violations (MC-cycle calibrated): %s",
                  r["model_violations"])
    if dump_path:
        with open(dump_path, "w") as fh:
            json.dump(r, fh, indent=2)

    if tracing and cmd_log:
        gaps = {k: _gap_stats(cmd_log, k) for k in ("RD", "WR", "ACT", "PRE")}
        dut._log.info("cmd-gap stats: %s",
                      {k: {kk: vv for kk, vv in v.items() if kk != "gaps"}
                       for k, v in gaps.items()})
        if dump_path:
            with open(dump_path + ".gaps.json", "w") as fh:
                json.dump(gaps, fh, indent=2)
    dut._log.info("pumice perf proxy @ %.4f MHz tREFI=%d gens=%d timings=%s",
                  r["clk_mhz"], r["t_refi"], n_gen, r["timings"])
    dut._log.info("JEDEC floors at these timings: %s", r["floors"])
    hdr = (f"{'family':<10} {'mism':>5} {'wr_cyc':>7} {'wr_bw':>7} {'wr_util':>7}"
           f" {'wr_lat':>6} {'rd_cyc':>7} {'rd_bw':>7} {'rd_util':>7} {'rd_lat':>6}  gate")
    dut._log.info("%s", hdr)
    for fk in fam_names:
        f = fams[fk]
        gate = GATES.get(fk)
        dut._log.info("%-10s %5d %7d %7.1f %7.3f %6.1f %7d %7.1f %7.3f %6.1f  %s",
                      fk, f["mismatched"], f["wr_cycles"], f["wr_bw_mb_s"],
                      f["wr_util"], f["wr_lat_cyc"], f["rd_cycles"], f["rd_bw_mb_s"],
                      f["rd_util"], f["rd_lat_cyc"], (f">={gate}" if gate else "-"))

    # Integrity must hold for the perf number to be trustworthy.
    for fk in fam_names:
        f = fams[fk]
        assert f["wr_ok"], f"{fk}: write engine did not complete"
        assert f["rd_ok"], f"{fk}: read engine did not complete"
        assert f["mismatched"] == 0, f"{fk}: {f['mismatched']} beats mismatched"
        assert f["rd_cycles"] > 0 and f["wr_cycles"] > 0, f"{fk}: no cycles counted"


# =============================================================================
# pytest wrapper
# =============================================================================
def test_ddr2_char_perf(request):
    if os.environ.get("TEST_LEVEL", "FUNC").upper() == "GATE":
        pytest.skip("perf proxy is a multi-minute run; FUNC/FULL only")
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_uart_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)

    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # BOARD geometry by default (CLAUDE.md trap #1: the uart suite's default is
    # a 64b beat with device == beat, which is NOT the board). The same values
    # ride extra_env so the cocotb-side import of test_ddr2_char_uart sizes the
    # BFM identically.
    dfi_rate = int(os.environ.get("TEST_DFI_RATE", "2"))
    beat_bytes = int(os.environ.get("TEST_DRAM_BEAT_BYTES", "4"))
    dev_bytes = int(os.environ.get("TEST_DRAM_DEVICE_BYTES", "2"))
    dram_bl = int(os.environ.get("TEST_DRAM_BL", "4"))

    extra_env = {
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
        "PERF_DUMP": os.environ.get(
            "PERF_DUMP", os.path.join(log_dir, f"perf_dump_{tag}.json")),
        "PERF_CMD_TRACE": os.environ.get("PERF_CMD_TRACE", "0"),
        "MISM_PROBE": os.environ.get("MISM_PROBE", "0"),
        "MEM_DUMP_ROWS": os.environ.get("MEM_DUMP_ROWS", "0"),
        "AXI_R_PROBE": os.environ.get("AXI_R_PROBE", "0"),
        "DFI_RD_TRACE": os.environ.get("DFI_RD_TRACE", "0"),
        "TEST_PAGE_POLICY": os.environ.get("TEST_PAGE_POLICY", ""),
        "TEST_PAGE_MODE": os.environ.get("TEST_PAGE_MODE", ""),
        "TEST_TR_INIT": os.environ.get("TEST_TR_INIT", ""),
        "TEST_TREFI": os.environ.get("TEST_TREFI", "585"),
        "TEST_TXN": os.environ.get("TEST_TXN", "256"),
        "TEST_GAP": os.environ.get("TEST_GAP", "0"),
        "TEST_BURST_LEN": os.environ.get("TEST_BURST_LEN", "8"),
        "TEST_FAMILIES": os.environ.get("TEST_FAMILIES",
                                        "incremental,row_major,col_ilv,col_major"),
        "TEST_NUM_GEN": os.environ.get("TEST_NUM_GEN", "1"),
        "PERF_HOST_DIAG": os.environ.get("PERF_HOST_DIAG", "0"),
        # DFISlavePHY's decoded-command trace (bank / row per command), for
        # row-hit forensics on a pick core; rides extra_env like the others
        "DFI_CMD_TRACE": os.environ.get("DFI_CMD_TRACE", "0"),
        "TEST_TIMING_OVERRIDES": os.environ.get("TEST_TIMING_OVERRIDES", ""),
        "TEST_CMD_DELAY": os.environ.get("TEST_CMD_DELAY", "0"),
        "TEST_T_PHY_WRLAT": os.environ.get("TEST_T_PHY_WRLAT", "0"),
        "TEST_T_RDDATA_EN": os.environ.get("TEST_T_RDDATA_EN", "4"),
        "TEST_RD_PHASE": os.environ.get("TEST_RD_PHASE", "0"),
        "TEST_WR_PHASE": os.environ.get("TEST_WR_PHASE", "0"),
        "TEST_FPGA_CLK_HZ": str(FPGA_CLK_HZ),
        "TEST_DFI_RATE": str(dfi_rate),
        "TEST_DRAM_BL": str(dram_bl),
        "TEST_DRAM_BEAT_BYTES": str(beat_bytes),
        "TEST_DRAM_DEVICE_BYTES": str(dev_bytes),
        "TEST_STRICT_WRITE_TIMING": os.environ.get("TEST_STRICT_WRITE_TIMING", "0"),
        "TEST_WRITE_LATENCY": os.environ.get("TEST_WRITE_LATENCY", "0"),
        "TEST_STRICT_READ_TIMING": os.environ.get("TEST_STRICT_READ_TIMING", "0"),
        "TEST_READ_LATENCY": os.environ.get("TEST_READ_LATENCY", "8"),
    }
    params = {"FPGA_CLK_HZ": str(FPGA_CLK_HZ),
              # pumice pick core A/B: 1 = BANK_PICK (default), 0 = FRFCFS research core
              "SCHED_CORE": os.environ.get("TEST_SCHED_CORE", "0"),  # pumice is FR-FCFS (owner, 2026-10-22)
              # injectors per direction: the macro default (4) unless the run
              # asks for more (eight per direction is the owner's load point)
              "NUM_GEN": str(max(4, int(os.environ.get("TEST_NUM_GEN", "1"), 0))),
              "UART_BAUD": str(UART_BAUD),
              "DFI_RATE": str(dfi_rate),
              "DRAM_BL": str(dram_bl),
              "DRAM_BEAT_WIDTH": str(beat_bytes * 8),
              "DRAM_DEVICE_WIDTH": str(dev_bytes * 8)}
    compile_args = [
        "+define+USE_ASYNC_RESET",
        # expose the scheduler plane's evt_* strobes to the cmd trace probe
        "--public-flat-rw",
        FIELD_COMBO_VLT, "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-PINMISSING",
    ]
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_pumice_perf",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
