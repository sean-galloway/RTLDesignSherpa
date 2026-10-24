"""LiteDRAM perf proxy: incremental / row_major / col_ilv / col_major, 1..8
generators per direction, measured through the SAME injectors and observers
as test_ddr2_char_perf (pumice) and test_granite_char_perf (granite): the
char_engine_harness of the LiteDRAM A/B flow drives LiteX's simulation core
litedram_core_sim (LiteDRAMCore + SDRAMPHYModel + VexRiscv BIOS). The host
driver is the board's LiteDRAM subclass (pumice-only CSR calls are no-ops;
the BIOS initialises the modelled DRAM and raises init_done).

Prerequisite: the sim core regenerated WITH its BIOS (flows-litedram-uart
`regen.sh --bios`); the test skips with that message if the ROM is empty.
Knobs: TEST_TREFI is recorded only (LiteDRAM's refresh is its own), TEST_TXN
(256), TEST_GAP (0), TEST_BURST_LEN (8), TEST_FAMILIES, TEST_NUM_GEN (1),
PERF_DUMP.
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
import perf_mixed_family as pmf                           # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from test_granite_char_uart import CLKS_PER_BIT           # noqa: E402,F401
_LITE = os.path.join(_REPO, "projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
                            "ddr2-characterization/flows-litedram-uart")
if os.path.join(_LITE, "host") not in sys.path:
    sys.path.insert(0, os.path.join(_LITE, "host"))
from host_litedram_char import LiteDRAMCharDriver, BUILD_ID_LITEDRAM  # noqa: E402
_SIM_GW   = os.path.join(_LITE, "gen/sim/gateware")
_SIM_CORE = os.path.join(_SIM_GW, "litedram_core_sim.v")
_SIM_INIT = [os.path.join(_SIM_GW, f)
             for f in ("litedram_core_sim_rom.init", "litedram_core_sim_sram.init")]
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

# --- BOARD clock (75 MHz). The granite uart suite runs 100 MHz; the board and
# its JEDEC ns->cycle derivation are 75 MHz, so parity needs the 75 MHz period.
FPGA_CLK_HZ = int(os.environ.get("TEST_FPGA_CLK_HZ", "75000000"))
_PS_GRAIN = 8
_CLK_PERIOD_PS = _PS_GRAIN * round(1e12 / FPGA_CLK_HZ / _PS_GRAIN)  # 13336 ps
CLK_PERIOD_NS = _CLK_PERIOD_PS / 1000.0                             # 13.336 ns
CLK_ACTUAL_HZ = round(1e12 / _CLK_PERIOD_PS)                        # 75_001_875
UART_BAUD = FPGA_CLK_HZ // CLKS_PER_BIT

_FILELIST = ("projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
             "ddr2_char_framework/dv/filelists/litedram_char_uart_tb_top.f")

# Silicon perf gates (MC-003 enablement criteria).
GATES = {"row_major": 570, "col_ilv": 354, "col_major": 369}

_FAMILIES = {
    "incremental": pc.FAM_INCREMENTAL,
    "row_major": pc.FAM_ROW_MAJOR,
    "col_ilv":   pc.FAM_COL_INTERLEAVE,
    "col_major": pc.FAM_COL_MAJOR,
}


async def _cmd_probe(dut, log):
    """PERF_CMD_TRACE=1: log every scheduler column/row command fire as
    (kind, cycle). Localizes the single-bank issue-rate bubble by the gap
    between consecutive same-kind fires."""
    try:
        core = dut.u_dut.u_dut.u_ctrl.u_core
        bs = core.u_sched_plane.g_bank_sched.u_bank_sched
    except AttributeError:
        dut._log.info("PERF_CMD_TRACE: per-bank scheduler absent (BANK_FIFO=0)")
        return
    cyc = 0
    while True:
        # Registered fire-history strobes: stable at the edge (no ReadOnly), and
        # the gap between consecutive strobes equals the gap between the fires.
        await RisingEdge(dut.aclk)
        cyc += 1
        try:
            if int(bs.r_rdfire0.value):
                log.append(("RD", cyc))
            elif int(bs.r_wrfire0.value):
                log.append(("WR", cyc))
        except Exception:
            pass


async def _gate_trace(dut, path, max_fires=40):
    """PERF_GATE_TRACE=1: bounded ReadOnly window starting at the first RD
    fire, logging every scheduler gate each cycle until max_fires RD fires.
    Pinpoints WHICH gate forces the idle cycle after a column fire."""
    try:
        bs = dut.u_dut.u_dut.u_ctrl.u_core.u_sched_plane.g_bank_sched.u_bank_sched
    except AttributeError:
        dut._log.info("gate_trace: path absent (BANK_FIFO=0)")
        return
    hdr = ("cyc fire pick fsafe selop wop0 rop0 rdwREG0 rdwLIVE0 tccd "
           "rdfire0 wrfire0 bh0_v bh2_v skid_v")
    lines = [hdr]
    fires = 0
    started = False
    cyc = 0
    while fires < max_fires and cyc < 500000:
        await ReadOnly()
        try:
            fire = int(bs.w_fire.value)
            pick = int(bs.w_pick_vld.value)
            fsafe = int(bs.w_fsafe.value)
            selop = int(bs.w_sel_op.value)
            wop0 = int(bs.w_op[0].value)
            rop0 = int(bs.r_op[0].value)
            rdw_reg = int(bs.r_rdwr_rdy[0][0].value)
            rdw_live = int(bs.bank_rdwr_ready_i[0][0].value)
            tccd = int(bs.w_tccd_fwd_ok.value)
            rdf0 = int(bs.r_rdfire0.value)
            wrf0 = int(bs.r_wrfire0.value)
            bh0v = int(bs.rd_bh_valid_i.value)
            bh2v = int(bs.rd_bh2_valid_i.value)
            skidv = int(bs.r_rs[0].vld.value)
            if rdf0 and not started:
                started = True
            if started:
                lines.append(f"{cyc} {fire} {pick} {fsafe} {selop} {wop0} {rop0} "
                             f"{rdw_reg} {rdw_live} {tccd} {rdf0} {wrf0} "
                             f"{bh0v} {bh2v} {skidv}")
            if rdf0:
                fires += 1
        except Exception as e:
            if started:
                lines.append(f"{cyc} err {e!r}")
        await RisingEdge(dut.aclk)
        cyc += 1
    with open(path, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    dut._log.info("gate_trace: %d RD fires, %d lines -> %s", fires, len(lines), path)


def _gap_stats(log, kind):
    ts = [c for k, c in log if k == kind]
    if len(ts) < 2:
        return {"n": len(ts), "gaps": []}
    gaps = [b - a for a, b in zip(ts, ts[1:])]
    hist = {}
    for g in gaps:
        hist[g] = hist.get(g, 0) + 1
    return {"n": len(ts), "gaps": gaps[:64],
            "mean": round(sum(gaps) / len(gaps), 3),
            "hist": dict(sorted(hist.items()))}


async def _mism_probe(dut, log):
    """MISM_PROBE=1: latch (beat, exp, act) for every mismatching read beat
    on the gen0 debug tap -- localizes corruption in the read stream without
    touching RTL. beat is the R-beat ordinal from stream start."""
    try:
        sig_v = dut.u_dut.u_dut.rd_dbg_valid
        sig_r = dut.u_dut.u_dut.rd_dbg_ready
        sig_m = dut.u_dut.u_dut.rd_dbg_mismatch
        sig_e = dut.u_dut.u_dut.rd_dbg_expected
        sig_a = dut.u_dut.u_dut.rd_dbg_actual
    except AttributeError:
        dut._log.info("MISM_PROBE: dbg tap absent")
        return
    beat = 0
    while True:
        await RisingEdge(dut.aclk)
        try:
            if int(sig_v.value):
                log.append({"beat": beat, "mism": int(sig_m.value),
                            "exp": int(sig_e.value),
                            "act": int(sig_a.value)})
                beat += 1
        except Exception:
            pass


async def _bringup(dut):
    """UART BFM on the harness; the sim core self-initialises (BIOS in ROM),
    nothing to model on a DFI side."""
    h = UartSimHarness(dut, clks_per_bit=CLKS_PER_BIT, clk_period_ns=CLK_PERIOD_NS)
    chan = await h.start()
    drv = LiteDRAMCharDriver(bridge=h.make_bridge())
    return drv, chan


@cocotb.test(timeout_time=600000, timeout_unit="ms")
async def cocotb_test_litedram_perf(dut):
    drv, chan = await _bringup(dut)

    t_refi = int(os.environ.get("TEST_TREFI", "585"), 0)
    txn = int(os.environ.get("TEST_TXN", "256"), 0)
    gap = int(os.environ.get("TEST_GAP", "0"), 0)
    blen = int(os.environ.get("TEST_BURST_LEN", "8"), 0)
    n_gen = int(os.environ.get("TEST_NUM_GEN", "1"), 0)
    clk_mhz = CLK_ACTUAL_HZ / 1e6
    fam_names = [f.strip() for f in
                 os.environ.get("TEST_FAMILIES",
                                "incremental,row_major,col_ilv,col_major").split(",")]
    geom = pc.DEFAULT_GEOM
    dump_path = os.environ.get("PERF_DUMP", "")

    def measure_family(fam_key):
        if fam_key == "mixed":
            return pmf.measure(drv, dc, pm, geom, n_gen=n_gen, blen=blen, txn=txn, gap=gap,
                               clk_mhz=clk_mhz, hist_mean=lambda h, t: 0.0)
        window = pmf.family_programs(fam_key, n_gen, geom, dc, blen=blen, txn=txn, gap=gap)
        if window is not None:
            fam, stride, wrap = fam_key, window[0]["stride_0"], window[0]["wrap_mask_0"]
        else:
            fam = _FAMILIES[fam_key]
            stride, wrap = pc.strides_for(pc.Scenario(name=fam, family=fam,
                                                      burst_len=blen, txn_count=txn),
                                          geom)
        beat_bytes = 1 << dc.AXI_SIZE_8
        bytes_moved = txn * blen * beat_bytes * n_gen
        def prog_for(g):
            if window is not None:
                return window[g]
            # Same placement as the pumice proxy: generators one bank stride
            # apart, so each thread owns a bank on the page-friendly families
            # and the threads bank-interleave on col_major.
            return dict(start_addr=g * geom.bank_stride, burst_len=blen,
                        txn_count=txn, stride_0=stride, wrap_mask_0=wrap, gap=gap,
                        id_mode=dc.ID_MODE_FIXED, axi_size=dc.AXI_SIZE_8,
                        data_mode=True, gen=g, **pmf.seed_fields(g))

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
        drv.freeze_trace(True)
        tw = drv.timer()
        wr_cycles = max(int(tw.w_last) - int(tw.w_first), 0)
        wr_util = drv.perf_meters()["wr"].prod / max(wr_cycles, 1)

        # read phase
        for g in range(n_gen):
            drv.program_rd_engine(**prog_for(g))
        drv.clear_stats()
        drv.timer_clear()
        drv.freeze_trace(False)
        drv.start_rd(mask)
        rd_ok = pm.wait_engine(drv, "rd", timeout_s=120, ignore_error=True)
        drv.freeze_trace(True)
        tr = drv.timer()
        rd_cycles = max(int(tr.r_last) - int(tr.r_first), 0)
        rd_util = drv.perf_meters()["rd"].prod / max(rd_cycles, 1)

        mism = drv.beats_mismatched()
        return {
            "family": fam_key, "stride": stride, "wrap": wrap,
            "seed": pmf.PERF_SEED, "gen_seeds": [prog_for(g)["lfsr_seed"] for g in range(n_gen)],
            "txn": txn, "burst_len": blen, "num_gen": n_gen,
            "bytes_moved": bytes_moved,
            "wr_ok": bool(wr_ok), "rd_ok": bool(rd_ok), "mismatched": int(mism),
            "wr_cycles": int(wr_cycles), "rd_cycles": int(rd_cycles),
            "wr_util": round(float(wr_util), 4), "rd_util": round(float(rd_util), 4),
            "wr_bw_mb_s": round(bytes_moved / wr_cycles * clk_mhz, 1) if wr_cycles else 0.0,
            "rd_bw_mb_s": round(bytes_moved / rd_cycles * clk_mhz, 1) if rd_cycles else 0.0,
            "clk_mhz": round(clk_mhz, 4),
        }

    def prog():
        out = {"clk_mhz": round(clk_mhz, 4), "t_refi": t_refi, "num_gen": n_gen,
               "dut": "litedram", "families": {}}
        bid = drv.build_id()
        assert bid == BUILD_ID_LITEDRAM, f"BUILD_ID 0x{bid:08X}: not the LiteDRAM harness"
        # the BIOS runs in the sim core; init_done is its verdict
        st = drv.wait_init(timeout_s=1800.0)
        out["init"] = {"init_done": bool(st.init_done), "init_fail": bool(st.init_fail)}
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
        # LiteDRAM programs its own timings and refresh (BIOS / generated
        # core); the pumice-era calls above are no-ops on this driver.
        out["timings"] = {"source": "litedram_hp.yml (BIOS-programmed)"}
        for fam_key in fam_names:
            out["families"][fam_key] = measure_family(fam_key)
        if dump_path:
            with open(dump_path, "w") as fh:
                json.dump(out, fh, indent=2)
        return out

    cmd_log = []
    tracing = os.environ.get("PERF_CMD_TRACE", "0") == "1"
    mism_probe = os.environ.get("MISM_PROBE", "0") == "1"
    gate_path = os.environ.get("PERF_GATE_TRACE", "")
    if tracing:
        cocotb.start_soon(_cmd_probe(dut, cmd_log))
    mism_log = []
    if mism_probe:
        cocotb.start_soon(_mism_probe(dut, mism_log))
    if gate_path:
        cocotb.start_soon(_gate_trace(dut, gate_path))

    r = await bridge(prog)()
    if mism_log:
        mism_dump = os.environ.get("MISM_DUMP", "/tmp/mc003_mism.json")
        with open(mism_dump, "w") as fh:
            json.dump(mism_log, fh, indent=2)
        dut._log.info("mism probe: %d bad beats -> %s", len(mism_log), mism_dump)
    fams = r["families"]

    if tracing and cmd_log:
        gaps = {k: _gap_stats(cmd_log, k) for k in ("RD", "WR", "ACT", "PRE")}
        dut._log.info("cmd-gap stats: %s",
                      {k: {kk: vv for kk, vv in v.items() if kk != "gaps"}
                       for k, v in gaps.items()})
        gp = os.environ.get("PERF_DUMP", "") + ".gaps.json"
        if gp:
            with open(gp, "w") as fh:
                json.dump(gaps, fh, indent=2)
    dut._log.info("perf proxy @ %.4f MHz tREFI=%d  timings=%s",
                  r["clk_mhz"], r["t_refi"], r["timings"])
    hdr = (f"{'family':<10} {'mism':>5} {'wr_cyc':>7} {'wr_bw':>7} {'wr_util':>7}"
           f" {'rd_cyc':>7} {'rd_bw':>7} {'rd_util':>7}  gate")
    dut._log.info("%s", hdr)
    for fk in fam_names:
        f = fams[fk]
        gate = GATES.get(fk)
        dut._log.info("%-10s %5d %7d %7.1f %7.3f %7d %7.1f %7.3f  %s",
                      fk, f["mismatched"], f["wr_cycles"], f["wr_bw_mb_s"],
                      f["wr_util"], f["rd_cycles"], f["rd_bw_mb_s"],
                      f["rd_util"], (f">={gate}" if gate else "-"))

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
def test_litedram_char_perf(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "litedram_char_uart_tb_top"
    if not os.path.exists(_SIM_CORE):
        pytest.skip("litedram_core_sim.v not generated: flows-litedram-uart regen.sh --bios")
    if os.path.getsize(_SIM_INIT[0]) == 0:
        pytest.skip("litedram_core_sim ROM is empty (generated without the BIOS): regen.sh --bios")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)

    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    # the core's $readmemh paths are bare file names, resolved from the sim's cwd
    import shutil
    for f in _SIM_INIT:
        shutil.copy(f, sim_build)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
        "PERF_DUMP": os.environ.get(
            "PERF_DUMP", os.path.join(log_dir, f"perf_dump_{tag}.json")),
        # trace knobs must ride extra_env to reliably reach the sim process
        "PERF_CMD_TRACE": os.environ.get("PERF_CMD_TRACE", "0"),
        "PERF_GATE_TRACE": os.environ.get("PERF_GATE_TRACE", ""),
        "MISM_PROBE": os.environ.get("MISM_PROBE", "0"),
        "MISM_DUMP": os.environ.get("MISM_DUMP", ""),
        "DFI_CMD_TRACE": os.environ.get("DFI_CMD_TRACE", "0"),
        "TEST_PAGE_POLICY": os.environ.get("TEST_PAGE_POLICY", ""),
        "TEST_TREFI": os.environ.get("TEST_TREFI", "585"),
        "TEST_TXN": os.environ.get("TEST_TXN", "256"),
        "TEST_GAP": os.environ.get("TEST_GAP", "0"),
        "TEST_BURST_LEN": os.environ.get("TEST_BURST_LEN", "8"),
        "TEST_FAMILIES": os.environ.get("TEST_FAMILIES", "incremental,row_major,col_ilv,col_major"),
        "TEST_NUM_GEN": os.environ.get("TEST_NUM_GEN", "1"),
        "TEST_CMD_DELAY": os.environ.get("TEST_CMD_DELAY", "0"),
        "TEST_T_PHY_WRLAT": os.environ.get("TEST_T_PHY_WRLAT", "0"),
        "TEST_T_RDDATA_EN": os.environ.get("TEST_T_RDDATA_EN", "4"),
        "TEST_RD_PHASE": os.environ.get("TEST_RD_PHASE", "0"),
        "TEST_WR_PHASE": os.environ.get("TEST_WR_PHASE", "0"),
        "TEST_STRICT_WRITE_TIMING": os.environ.get("TEST_STRICT_WRITE_TIMING", "0"),
        "TEST_WRITE_LATENCY": os.environ.get("TEST_WRITE_LATENCY", "0"),
        "TEST_STRICT_READ_TIMING": os.environ.get("TEST_STRICT_READ_TIMING", "0"),
        "TEST_READ_LATENCY": os.environ.get("TEST_READ_LATENCY", "8"),
    }
    params = {"FPGA_CLK_HZ": str(FPGA_CLK_HZ),
              "UART_BAUD": str(UART_BAUD),
              # at least the macro default; TEST_NUM_GEN=8 builds eight injectors
              "NUM_GEN": str(max(4, int(os.environ.get("TEST_NUM_GEN", "1"), 0)))}
    compile_args = [
        "+define+USE_ASYNC_RESET",
        # no internal probes on the LiteX core: leave Verilator free to
        # optimise (--public-flat-rw on the 15k-line core + VexRiscv ran at
        # ~5k cycles/s)
        FIELD_COMBO_VLT, "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-PINMISSING",
        "-Wno-fatal", "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND", "-Wno-UNOPTFLAT",
    ]
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_litedram_perf",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
