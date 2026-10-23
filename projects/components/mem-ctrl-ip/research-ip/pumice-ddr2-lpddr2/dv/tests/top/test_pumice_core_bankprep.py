"""pumice core bench: bank preparation on bank-interleaved rows (TASK-045).

The isolated-scheduler counterpart of the perf proxy's col_ilv family: the
pumice core alone (CAMs, timers, page policy, pick core, DFI plane) against
the JEDEC-timed DFI slave, driven by the AXI4 master BFMs. One AXI burst is
one 8-column row; burst k goes to bank k mod 8, so successive rows hop banks
and the next bank's ACT CAN be issued under the current bank's column run.
A core that does so spends 9 command slots per row (8 columns + the ACT,
the close riding as auto-precharge); one that waits for the run to end
spends 9 + tRCD (+ an explicit PRE + tRP when it does not close on drain).

Writes then reads, every scheduler fire logged (kind, cycle) from the
scheduler plane's evt_* strobes -- the same signal the proxy's
PERF_CMD_TRACE samples, so the two agree to the cycle. Reported per phase:
cycles per row (ACT-to-ACT), the column gap at the row switch, PRE count
(explicit closes), elapsed cycles and columns per cycle.

Knobs (environment):
  TEST_SCHED      "sched_access_pref_i=2,sched_col_sel_i=0" style list of
                  core inputs to set after bring-up (default: none)
  TEST_PAGE_MODE  page_mode_i (default 3 = fixed_open, the CSR reset)
  TEST_TR_INIT    page_tr_init_i (default 2, the CSR reset)
  TEST_ROWS       rows per phase (default 128)
  TEST_BANKS      banks to hop over (default 8; 1 = col_major shape)
  ARB_TRACE_START / ARB_TRACE_N
                  per-cycle FR-FCFS arbiter rows for that cycle window, to
                  <label>.arb.txt (same cycle counter as the fire log)
Geometry: as test_pumice_core_dfi (TEST_DRAM_BEAT / TEST_DRAM_BL /
TEST_DRAM_DEVICE_W; the board is 32 / 4 / 16), timings TEST_T_RCD / TEST_T_RP.
"""
import collections
import json
import os

import cocotb
from cocotb.triggers import ReadOnly, RisingEdge
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

import test_pumice_core_dfi as core   # noqa: E402  bring-up, address builder, BFM helpers, geometry

_LEVEL = os.environ.get("TEST_LEVEL", "func").lower()


def _sched_knobs():
    out = {}
    for item in [x.strip() for x in os.environ.get("TEST_SCHED", "").split(",") if x.strip()]:
        k, v = item.split("=")
        out[k.strip()] = int(v.strip(), 0)
    return out


async def _fire_log(dut, log):
    sp = dut.u_core.u_sched_plane
    cyc = 0
    while True:
        await RisingEdge(dut.aclk)
        await ReadOnly()
        cyc += 1
        if int(sp.evt_rd.value):
            log.append(("RD", cyc))
        elif int(sp.evt_wr.value):
            log.append(("WR", cyc))
        elif int(sp.evt_act.value):
            log.append(("ACT", cyc))
        elif int(sp.evt_pre.value):
            log.append(("PRE", cyc))


async def _arb_trace(dut, start, n, path):
    """Per-cycle FR-FCFS arbiter rows for [start, start+n): output register
    and fire, pre-pick registers per class, the chosen class, live ACT gate,
    classify masks, write-entry state and the bank image. Silent on the
    BANK_PICK core."""
    try:
        ar = dut.u_core.u_sched_plane.g_arbiter.u_arbiter
    except AttributeError as e:
        dut._log.info("ARB_TRACE: arbiter absent (%r)", e)
        return

    def v(sig):
        try:
            return int(sig.value)
        except Exception:  # noqa: BLE001
            return -1

    rows = []
    cyc = 0
    while True:
        await RisingEdge(dut.aclk)
        await ReadOnly()
        cyc += 1
        if start <= cyc < start + n:
            op = ("A" if v(ar.r_do_act) else "R" if v(ar.r_do_rd) else "W" if v(ar.r_do_wr)
                  else "P" if v(ar.r_do_pre) else "-")
            # same-(bank,row) read entries the fire-stage sibling check sees
            sibs = []
            try:
                ne = len(ar.rd_sch_valid_i.value)
                rv_, bk_, rw_, cl_ = (int(ar.rd_sch_valid_i.value), int(ar.rd_sch_bank_i.value),
                                      int(ar.rd_sch_row_i.value), int(ar.rd_sch_col_i.value))
                bkw, roww, colw = core.NUM_BANKS.bit_length() - 1, core.ROW_WIDTH, core.COL_WIDTH
                for j in range(ne):
                    if (rv_ >> j) & 1 and ((bk_ >> (j * bkw)) & ((1 << bkw) - 1)) == v(ar.r_bank) \
                            and ((rw_ >> (j * roww)) & ((1 << roww) - 1)) == v(ar.r_row):
                        sibs.append("%d:c%d%s" % (j, (cl_ >> (j * colw)) & ((1 << colw) - 1),
                                                  "*" if j == v(ar.r_issue_slot) else ""))
            except Exception as e:  # noqa: BLE001
                sibs = [repr(e)[:40]]
            rows.append("sibs=" + ",".join(sibs) + " " +
                "c%d out=%d%s b%d fire=%d safe=%d hold=%d rdy=%d cmdrdy=%d wcr=%d | "
                "pre: rc=%d(b%d) wc=%d(b%d) ra=%d(b%d) wa=%d(b%d r%d) rp=%d wp=%d cls=%d actg=%d | "
                "m: rcol=%04x wcol=%04x ract=%04x wact=%04x rpre=%04x wpre=%04x | "
                "rv=%04x wv=%04x wpend=%04x | rowact=%02x actrdy=%02x rdwrrdy=%02x prerdy=%02x "
                "actguard=%02x apclos=%02x preclos=%02x actpick=%02x prepick=%02x drainok=%02x | "
                "ap: colap=%d/%d ylast=%d/%d apout=%d apfire=%d sib=%d"
                % (cyc, v(ar.r_pick_valid), op, v(ar.r_bank), v(ar.w_fire_out), v(ar.w_out_safe),
                   v(ar.w_out_hold), v(ar.w_out_ready), v(ar.cmd_ready_i), v(ar.wr_commit_ready_i),
                   v(ar.rd_col_f), v(ar.rd_col_bank), v(ar.wr_col_f), v(ar.wr_col_bank),
                   v(ar.rd_act_f), v(ar.rd_act_bank), v(ar.wr_act_f), v(ar.wr_act_bank), v(ar.wr_act_row),
                   v(ar.rd_pre_f), v(ar.wr_pre_f), v(ar.w_pick_class), v(ar.w_act_gate_live),
                   v(ar.rd_col_m), v(ar.wr_col_m), v(ar.rd_act_m), v(ar.wr_act_m), v(ar.rd_pre_m), v(ar.wr_pre_m),
                   v(ar.rd_sch_valid_i), v(ar.wr_sch_valid_i), v(ar.wr_sch_pend_i),
                   v(ar.bank_row_active_i), v(ar.bank_act_ready_i), v(ar.bank_rdwr_ready_i),
                   v(ar.bank_pre_ready_i), v(ar.w_act_guard), v(ar.r_ap_closing), v(ar.r_pre_closing),
                   v(ar.w_act_pick), v(ar.w_pre_pick), v(ar.drain_close_ok_i),
                   v(ar.rd_col_ap), v(ar.wr_col_ap), v(ar.w_rd_ylast), v(ar.w_wr_ylast),
                   v(ar.r_ap_out), v(ar.w_ap_fire), v(ar.w_ap_sibling)))
        if cyc >= start + n:
            with open(path, "w") as fh:
                fh.write("\n".join(rows) + "\n")
            dut._log.info("ARB_TRACE: %d rows -> %s", len(rows), path)
            return


def _phase_stats(log, t0, t1, kind):
    """Per-phase shape from the fire log restricted to [t0, t1]."""
    ev = [(k, c) for k, c in log if t0 <= c <= t1]
    acts = [c for k, c in ev if k == "ACT"]
    cols = [c for k, c in ev if k == kind]
    act_gaps = collections.Counter(b - a for a, b in zip(acts, acts[1:]))
    col_gaps = collections.Counter(b - a for a, b in zip(cols, cols[1:]))
    n_pre = sum(1 for k, _ in ev if k == "PRE")
    period = act_gaps.most_common(1)[0][0] if act_gaps else 0
    switch = max((g for g, n in col_gaps.items() if n >= len(acts) // 4), default=0)
    return {
        "columns": len(cols), "acts": len(acts), "pres": n_pre,
        "cycles": (cols[-1] - cols[0] + 1) if cols else 0,
        "cycles_per_row": period,
        "act_gap_hist": dict(sorted(act_gaps.items())),
        "col_gap_hist": dict(sorted(col_gaps.items())),
        "col_gap_at_switch": switch,
        "cols_per_cycle": round(len(cols) / (cols[-1] - cols[0] + 1), 4) if len(cols) > 1 else 0.0,
    }


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_pumice_core_bankprep(dut):
    label = os.environ.get("TEST_LABEL", "bankprep")
    n_rows = int(os.environ.get("TEST_ROWS", "128"))
    n_banks = int(os.environ.get("TEST_BANKS", str(core.NUM_BANKS)))
    cols_per_row = 8
    beats = cols_per_row * core.BL_WORDS

    _memory, slave = await core._bring_up(dut)
    if 'b' not in core._BFM:
        core._masters_init(dut)
    dut.page_mode_i.value = int(os.environ.get("TEST_PAGE_MODE", "3"), 0)
    dut.page_tr_init_i.value = int(os.environ.get("TEST_TR_INIT", "2"), 0)
    sched = _sched_knobs()
    for k, v in sched.items():
        getattr(dut, k).value = v
    # Refresh far away: the shape under test is the row switch, not tREFI.
    dut.t_refi_i.value = 0x3FFF
    dut.refi_reload_i.value = 1
    await RisingEdge(dut.aclk)
    dut.refi_reload_i.value = 0

    log = []
    cocotb.start_soon(_fire_log(dut, log))
    if os.environ.get("ARB_TRACE_N"):
        cocotb.start_soon(_arb_trace(dut, int(os.environ.get("ARB_TRACE_START", "0")),
                                     int(os.environ["ARB_TRACE_N"]), f"{label}.arb.txt"))
    # Let the fire log's cycle counter start before any traffic.
    for _ in range(4):
        await RisingEdge(dut.aclk)

    def addr(k):
        return core._mkaddr(k % n_banks, 0x11 + k // n_banks, 0)

    reqs = [(addr(k), [(k * 0x9E3779B1 + b) & ((1 << core.DW) - 1) for b in range(beats)])
            for k in range(n_rows)]
    t_w0 = get_sim_time('ns')
    await core._write_many(dut, reqs)
    t_w1 = get_sim_time('ns')
    for _ in range(40):
        await RisingEdge(dut.aclk)
    t_r0 = get_sim_time('ns')
    res = await core._BFM["b"].read_many([addr(k) for k in range(n_rows)], length=beats)
    t_r1 = get_sim_time('ns')
    bad = sum(1 for (a, d), (_, exp) in zip(res, reqs) if list(d) != list(exp))

    def cyc(ns):
        return ns / core._ACLK_NS

    # Fire-log cycles count from the log start; phases are bounded by the fire
    # kinds themselves (first/last WR, first/last RD) so the two clocks need
    # no alignment.
    wr_c = [c for k, c in log if k == "WR"]
    rd_c = [c for k, c in log if k == "RD"]
    wr = _phase_stats(log, wr_c[0] - 4, wr_c[-1] + 1, "WR") if wr_c else {}
    rd = _phase_stats(log, rd_c[0] - 4, rd_c[-1] + 1, "RD") if rd_c else {}
    out = {
        "label": label, "rows": n_rows, "banks": n_banks, "cols_per_row": cols_per_row,
        "sched": sched, "page_mode": int(dut.page_mode_i.value), "tr_init": int(dut.page_tr_init_i.value),
        "geometry": {"beat": core.DRAM_BEAT, "bl": core.BL, "dev_w": core.DRAM_DEV_W,
                     "bl_words": core.BL_WORDS, "t_rcd": int(dut.t_rcd_i.value), "t_rp": int(dut.t_rp_i.value)},
        "wr": wr, "rd": rd,
        "wr_elapsed_cyc": round(cyc(t_w1 - t_w0)), "rd_elapsed_cyc": round(cyc(t_r1 - t_r0)),
        "read_mismatch_bursts": bad,
        "jedec_violations": len(getattr(slave, "jedec_violations", []) or []),
        "dfi_cmd_counts": {str(k): v for k, v in slave.cmd_counts.items() if v},
    }
    with open(f"{label}.json", "w") as fh:
        json.dump(out, fh, indent=1)
    dut._log.info("BANKPREP %s: wr %s cyc/row (switch gap %s, PRE %s) rd %s cyc/row (switch gap %s, PRE %s) "
                  "cols/cyc wr %.3f rd %.3f mism %d",
                  label, wr.get("cycles_per_row"), wr.get("col_gap_at_switch"), wr.get("pres"),
                  rd.get("cycles_per_row"), rd.get("col_gap_at_switch"), rd.get("pres"),
                  wr.get("cols_per_cycle", 0), rd.get("cols_per_cycle", 0), bad)
    assert bad == 0, f"{bad} read bursts mismatched"
    assert wr and rd, "a phase produced no column commands"


def test_pumice_core_bankprep(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_core_tb_top"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=core._FILELIST)
    tag = "bankprep_" + os.environ.get("TEST_LABEL", "bankprep")
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": str(core.NUM_BANKS), "ROW_WIDTH": str(core.ROW_WIDTH),
              "COL_WIDTH": str(core.COL_WIDTH), "DFI_RATE": str(core.DFI_RATE),
              "DRAM_BEAT_WIDTH": str(core.DRAM_BEAT), "DRAM_BL": str(core.BL),
              "DRAM_DEVICE_WIDTH": str(core.DRAM_DEV_W),
              "NUM_ENTRIES": os.environ.get("PUMICE_NUM_ENTRIES", "16"),
              "N_SRAM_SLOTS": os.environ.get("PUMICE_NUM_ENTRIES", "16"),
              "RD_RET_DEPTH": os.environ.get("PUMICE_RD_RET_DEPTH", "64"),
              "SCHED_CORE": os.environ.get("TEST_SCHED_CORE", "0"),
              **({"CLOSE_ON_DRAIN": os.environ["PUMICE_CLOSE_ON_DRAIN"]}
                 if os.environ.get("PUMICE_CLOSE_ON_DRAIN") else {})}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{tag}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
                 "TEST_LEVEL": _LEVEL}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_core_bankprep",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--public-flat-rw", "--assert"],
        waves=(os.environ.get("WAVES", "0") == "1"),
        plus_args=(["--trace"] if os.environ.get("WAVES", "0") == "1" else []),
        keep_files=True, timescale="1ns/1ps")
