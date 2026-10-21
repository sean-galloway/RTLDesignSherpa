# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""MC-003 residual repro at full-harness fidelity: col_major_bl8_gap.

Runs the board's failing scenario (col-major same-bank row thrash, host BL8,
idle gap 8 between txns, refresh live) through the REAL engines + UART bridge
+ granite controller + DFISlavePHY/MemoryModel (address-accurate,
JEDEC-checked model — the loopback model in test_granite_bankfifo_gap does
not model page/refresh interactions). Knobs: TEST_TREFI (default 585 = the
board value), TEST_TXN (default 64), TEST_GAP (default 8).

A hang shows as wait_engine timeout; corruption shows in crc()/mismatches;
JEDEC violations land in the DFISlavePHY log (policy demoted to soft by the
harness, like the smoke).
"""

import os
import sys
from collections import deque

import pytest
import cocotb
from cocotb._bridge import bridge
from cocotb.triggers import RisingEdge, FallingEdge, ReadOnly
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from test_granite_char_uart import (  # noqa: E402,F401
    _bringup, CLKS_PER_BIT, UART_BAUD, ROW_W, COL_W, NUM_BANKS, DRAM_BL,
    DFI_RATE, DRAM_BEAT_BYTES, GEAR_RATIO, DRAM_DEVICE_BYTES, BEATS_PER_BURST,
)

_REPO = os.environ["REPO_ROOT"]
_HOST = os.path.join(_REPO, "projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
                            "build-perf/host")
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
import ddr2_char as dc                               # noqa: E402
import pumice_master as pm                           # noqa: E402
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

_FILELIST = ("projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
             "ddr2_char_framework/dv/filelists/granite_char_uart_tb_top.f")


async def _dfi_monitor(dut):
    """DFI-pin beat accounting (TRACE=1). For every WR/RDA command, counts
    wrdata_en phases and rddata_valid beats per (bank, col) on the PHY-side
    DFI pins -- BEFORE the controller's aligner sees them. A short/long count
    at the pins means the controller created the clip (command-side bug); a
    balanced count at the pins with corruption upstream means the slip is
    INSIDE the controller return path (aligner/ring). Logs to
    /tmp/dfi_trace.txt and prints the first WR/RD pair whose counts differ."""
    from cocotb.utils import get_sim_time
    fh = open("/tmp/dfi_trace.txt", "w")
    fh.write("# t op bank col | wr_phases rd_beats\n")
    fh.flush()
    wr_exp = {}            # (bank,col) -> wrdata_en phase count
    rd_got = {}            # (bank,col) -> rddata_valid beat count
    rd_pending = deque()   # (bank,col) of RD/RDA commands awaiting data
    wr_pending = deque()   # (bank,col) of WR/WRA commands awaiting data
    first_bad = []
    try:
        while True:
            await RisingEdge(dut.aclk)
            try:
                cs = int(dut.phy_dfi_cs_n.value)
                r = int(dut.phy_dfi_ras_n.value)
                c = int(dut.phy_dfi_cas_n.value)
                w = int(dut.phy_dfi_we_n.value)
                addr = int(dut.phy_dfi_address.value)
                bank = int(dut.phy_dfi_bank.value)
                wen = int(dut.phy_dfi_wrdata_en.value)
                rvs = int(dut.phy_dfi_rddata_valid.value)
            except Exception:
                continue
            t = get_sim_time("ns")
            for p in range(DFI_RATE):
                if (cs >> p) & 1:
                    continue
                key = ((r >> p) & 1, (c >> p) & 1, (w >> p) & 1)
                if key == (1, 0, 1):   # RD
                    rd_pending.append(((bank >> (p * 3)) & 0x7,
                                       (addr >> (p * 14)) & 0x3FF))
                elif key == (1, 0, 0):  # WR
                    wr_pending.append(((bank >> (p * 3)) & 0x7,
                                       (addr >> (p * 14)) & 0x3FF))
            for p in range(DFI_RATE):
                if (wen >> p) & 1 and wr_pending:
                    k = wr_pending[0]
                    wr_exp[k] = wr_exp.get(k, 0) + 1
            if rvs:
                if wr_pending:
                    wr_pending.popleft()      # one DFI word per phase window
                if rd_pending:
                    k = rd_pending[0]
                    rd_got[k] = rd_got.get(k, 0) + 1
                    rd_got["_cur"] = rd_got.get("_cur", 0)
            # per completed RD burst: compare counts (words per burst constant)
            if not rvs and rd_pending and rd_got.get(rd_pending[0], 0) and \
               rd_pending[0] in wr_exp:
                k = rd_pending[0]
                we_ = wr_exp.get(k, 0)
                rg_ = rd_got.get(k, 0)
                if we_ != rg_ and not first_bad:
                    first_bad.append((t, k, we_, rg_))
                    fh.write(f"PIN-COUNT-MISMATCH t={t} {k} wr_phases={we_} rd_beats={rg_}\n")
                    fh.flush()
                rd_pending.popleft()
                rd_got.pop(k, None)
                wr_exp.pop(k, None)
            if len(rd_pending) > 64:
                rd_pending.popleft()
    except Exception as e:
        fh.write(f"# monitor died: {e!r}\n")
    finally:
        fh.close()


async def _sched_trace(dut):
    """Cycle-accurate file-based trace of the per-bank scheduler state around
    the WR commit-of-freed-slot failure. Logs one line per aclk cycle at the
    ReadOnly phase (stable combinational state during the cycle)."""
    core = dut.u_dut.u_dut.u_ctrl.u_core
    try:
        bs = core.u_sched_plane.g_bank_sched.u_bank_sched
    except AttributeError:
        dut._log.info("BANK_FIFO=0: per-bank scheduler absent, trace disabled")
        return
    store = core.u_entry_store
    fh = open("/tmp/bankfifo_wr_trace.txt", "w")
    fh.write("# t_ps phase fire ovr pick fsafe selbank selop selslot "
             "wop[0..7] ws_v[0..7] ws_s[0..7] rs_v[0..7] rs_s[0..7] "
             "bh_v bh_s[0..7] bh2_v cm_v cm_s cm_rdy sv[0..7] ref_req ref_grant "
             "raw_ws[0..7] raw_rs[0..7] raw_bhslot\n")
    fh.flush()
    NB = 8
    PTRW = 3
    HEAD_MSB = 37 - 1
    SLOT_MSB = HEAD_MSB - PTRW
    hist = []
    bad_seen = False
    while True:
        # Sample at the end of the cycle (pre-edge) to capture the stable state
        # that the assertion will check at the next posedge.
        await ReadOnly()
        t = get_sim_time("ps")
        phase = "E"
        try:
            fire = int(bs.w_fire.value)
            ovr = int(bs.w_ovr_vld.value)
            pick = int(bs.w_pick_vld.value)
            fsafe = int(bs.w_fsafe.value)
            sel_bank = int(bs.w_sel_bank.value)
            sel_op = int(bs.w_sel_op.value)
            sel_slot = (int(bs.w_sel_head.value) >> SLOT_MSB) & ((1 << PTRW) - 1) \
                if hasattr(bs, "w_sel_head") else -1
            w_ops = [int(bs.w_op[i].value) for i in range(NB)]
            ws_v = [(int(bs.r_ws[i].value) >> HEAD_MSB) & 1 for i in range(NB)]
            ws_s = [(int(bs.r_ws[i].value) >> SLOT_MSB) & ((1 << PTRW) - 1) for i in range(NB)]
            rs_v = [(int(bs.r_rs[i].value) >> HEAD_MSB) & 1 for i in range(NB)]
            rs_s = [(int(bs.r_rs[i].value) >> SLOT_MSB) & ((1 << PTRW) - 1) for i in range(NB)]
            bh_v = int(bs.wr_bh_valid_i.value)
            bh_s = [(int(bs.wr_bh_slot_i.value) >> (i * PTRW)) & ((1 << PTRW) - 1)
                    for i in range(NB)]
            bh2_v = int(bs.wr_bh2_valid_i.value)
            cm_v = int(bs.wr_commit_valid_o.value)
            cm_s = int(bs.wr_commit_slot_o.value)
            cm_rdy = int(bs.wr_commit_ready_i.value)
            sv = [int(store.r_wr_valid[i].value) for i in range(NB)]
            ref_req = int(bs.refresh_req_i.value)
            ref_grant = int(bs.refresh_grant_o.value)
            raw_ws = [int(bs.r_ws[i].value) for i in range(NB)]
            raw_rs = [int(bs.r_rs[i].value) for i in range(NB)]
            raw_bhslot = int(bs.wr_bh_slot_i.value)
            line = (f"{t:>10} {phase} {fire}{ovr}{pick}{fsafe} "
                    f"bk{sel_bank} op{sel_op} sl{sel_slot} "
                    f"wop{w_ops} "
                    f"wsV{ws_v} wsS{ws_s} "
                    f"rsV{rs_v} rsS{rs_s} "
                    f"bhV{bh_v:08b} bhS{bh_s} bh2V{bh2_v:08b} "
                    f"cmV{cm_v} cmS{cm_s} cmR{cm_rdy} "
                    f"sv{sv} ref{ref_req}/{ref_grant} "
                    f"rws{raw_ws} rrs{raw_rs} rbh{raw_bhslot}")
            hist.append(line)
            if len(hist) > 70:
                hist.pop(0)
            bad = (cm_v == 1 and sv[cm_s] == 0)
            if bad and not bad_seen:
                fh.write("# BAD COMMIT DETECTED\n")
                for h in hist:
                    fh.write(h + "\n")
                fh.flush()
                bad_seen = True
            # Continuous window around the known assert timestamp.
            if 365300000 <= t <= 365450000:
                fh.write(line + "\n")
                fh.flush()
        except Exception as e:
            fh.write(f"# trace error at {t}: {e!r}\n")
            fh.flush()
        await RisingEdge(dut.aclk)
    fh.close()


async def _rd_trace(dut):
    """MC-003 read-side journal (TRACE=1): one line per return-path event,
    joining bank-sched fire -> entry-store issue -> ring push/return/drain
    with the DFI aligner's admission/capture. Localizes the first mis-framed
    beat to a stage: a PUSH without a sched FIRE, a RET burst whose last
    lands off beat 3, an ADMIT/CAP imbalance, or a ring drain that stalls."""
    core = dut.u_dut.u_dut.u_ctrl.u_core
    ring = core.u_axi_plane.u_rd_ring
    store = core.u_entry_store
    try:
        bs = core.u_sched_plane.g_bank_sched.u_bank_sched
    except AttributeError:
        bs = None
    try:
        al = core.u_dfi_plane.u_rd
    except AttributeError:
        al = None
    PTRW = 3
    fh = open("/tmp/mc003_rd_trace.txt", "w")
    fh.write("# t_ps events: ALLOC tkt | PUSH tkt | RET tkt beat last occ | "
             "DRAIN last | FIRE slot bk rdy [skid/bh/bh2/stale/ovr/ref] | "
             "ISSU slot tkt vld | ADMIT outst | CAP rcnt last outst credit\n")
    fh.flush()
    while True:
        await ReadOnly()
        t = get_sim_time("ps")
        ev = []
        try:
            if int(ring.w_alloc.value):
                ev.append(f"ALLOC {int(ring.alloc_ticket_o.value)}")
            if int(ring.issue_valid_i.value) and int(ring.w_iq_wr_ready.value):
                ev.append(f"PUSH {int(ring.issue_ticket_i.value)}")
            if int(ring.w_ret_fire.value):
                ev.append(f"RET {int(ring.w_iq_rd_ticket.value)} "
                          f"{int(ring.r_ret_beat.value)} "
                          f"{int(ring.dfi_ret_last_i.value)} "
                          f"occ{int(ring.r_occ.value)} "
                          f"wi{int(ring.w_ret_idx.value)} "
                          f"d{int(ring.dfi_ret_data_i.value):016x}")
            if int(ring.w_dr_fire.value):
                ev.append(f"DRAIN {int(ring.w_hd_blast.value)} "
                          f"wi{int(ring.w_dr_idx.value)} "
                          f"d{int(ring.drain_data_o.value):016x}")
        except Exception as e:
            ev.append(f"ringerr {e!r}")
        try:
            if int(store.w_rd_issue_fire.value):
                slot = int(store.rd_issue_slot_i.value)
                try:
                    vld = int(store.r_rd_valid[slot].value)
                except Exception:
                    vld = -1
                ev.append(f"ISSU sl{slot} v{vld}")
        except Exception as e:
            ev.append(f"storeerr {e!r}")
        if bs is not None:
            try:
                if int(bs.wr_commit_valid_o.value):
                    ev.append(
                        f"WCMD sl{int(bs.wr_commit_slot_o.value)} "
                        f"b{int(bs.cmd_bank_o.value)} "
                        f"r{int(bs.cmd_row_o.value)} "
                        f"c{int(bs.cmd_col_o.value)}")
                if int(bs.rd_issue_valid_o.value):
                    ev.append(
                        f"RCMD sl{int(bs.rd_issue_slot_o.value)} "
                        f"b{int(bs.cmd_bank_o.value)} "
                        f"r{int(bs.cmd_row_o.value)} "
                        f"c{int(bs.cmd_col_o.value)}")
            except Exception as e:
                ev.append(f"bserr {e!r}")
        if al is not None:
            try:
                if int(al.w_admit.value):
                    ev.append(f"ADMIT outst{int(al.r_outstanding.value)}")
                if int(al.w_cap_fire.value):
                    ev.append(f"CAP rc{int(al.r_rcnt.value)} "
                              f"lt{int(al.rd_last_o.value)} "
                              f"outst{int(al.r_outstanding.value)} "
                              f"cr{int(al.r_credit.value)}")
            except Exception as e:
                ev.append(f"alerr {e!r}")
        try:
            if int(store.w_aw_fire.value):
                ev.append(f"WAW sl{int(store.w_wr_free_slot.value)}")
            if int(store.w_wd_fire.value):
                ev.append(f"WFILL sl{int(store.w_fill_slot.value)} "
                          f"d{int(store.wd_data_i.value) & 0xFFFFFFFF:08x}")
            if int(store.w_wr_commit_fire.value):
                slot = int(store.wr_commit_slot_i.value)
                try:
                    row = int(store.r_wr_row[slot].value)
                    col = int(store.r_wr_col[slot].value)
                    bk = int(store.r_wr_bank[slot].value)
                except Exception:
                    row = col = bk = -1
                ev.append(f"WCMIT sl{slot} b{bk} r{row} c{col}")
            if int(store.w_fetch.value):
                ev.append(f"WFTCH sl{int(store.w_dq_rd_slot.value)} "
                          f"i{int(store.w_cm_idx.value)}")
            if int(store.w_cm_fire.value):
                ev.append(f"WDRAIN sl{int(store.w_dq_rd_slot.value)} "
                          f"d{int(store.w_hd_data.value) & 0xFFFFFFFF:08x}")
        except Exception as e:
            ev.append(f"wrerr {e!r}")
        try:
            if int(core.s_axi_rvalid.value) and int(core.s_axi_rready.value):
                ev.append(f"RBEAT lt{int(core.s_axi_rlast.value)}")
        except Exception as e:
            ev.append(f"rerr {e!r}")
        if ev:
            fh.write(f"{t:>12} " + " ".join(ev) + "\n")
            fh.flush()
        await RisingEdge(dut.aclk)


async def _pin_trace(dut):
    """MC-003 pin-level journal (TRACE=1): every WR/RD command decoded from
    the DFI pins with its data beat(s), in order. Final arbiter before the
    memory model: (bank,col,wrdata) per WR command and (bank,col,rddata) per
    RD command."""
    fh = open("/tmp/mc003_pin_trace.txt", "w")
    fh.write("# t_ps | WRCMD bk col | WRDAT d | RDCMD bk col | RDDAT d\n")
    fh.flush()
    wr_pending = 0
    rd_pending = 0
    while True:
        await RisingEdge(dut.aclk)
        try:
            cs = int(dut.phy_dfi_cs_n.value)
            r = int(dut.phy_dfi_ras_n.value)
            c = int(dut.phy_dfi_cas_n.value)
            w = int(dut.phy_dfi_we_n.value)
            addr = int(dut.phy_dfi_address.value)
            bank = int(dut.phy_dfi_bank.value)
            wen = int(dut.phy_dfi_wrdata_en.value)
            rvs = int(dut.phy_dfi_rddata_valid.value)
        except Exception:
            continue
        t = get_sim_time("ps")
        ev = []
        for p in range(DFI_RATE):
            if (cs >> p) & 1:
                continue
            key = ((r >> p) & 1, (c >> p) & 1, (w >> p) & 1)
            bk = (bank >> (p * 3)) & 0x7
            ad = (addr >> (p * 14)) & 0x3FFF
            if key == (1, 0, 0):
                ev.append(f"WRCMD b{bk} c{ad}")
                wr_pending += 1
            elif key == (1, 0, 1):
                ev.append(f"RDCMD b{bk} c{ad}")
                rd_pending += 1
            elif key == (0, 0, 1):
                ev.append(f"ACT b{bk} r{ad}")
            elif key == (0, 1, 1):
                ev.append(f"PRE b{bk}")
        if wen:
            d = int(dut.phy_dfi_wrdata.value)
            for p in range(DFI_RATE):
                if (wen >> p) & 1:
                    ev.append(f"WRDAT d{(d >> (p * 128)) & 0xFFFFFFFFFFFFFFFF:016x}")
                    wr_pending -= 1
        if rvs:
            d = int(dut.phy_dfi_rddata.value)
            for p in range(DFI_RATE):
                if (rvs >> p) & 1:
                    ev.append(f"RDDAT d{(d >> (p * 128)) & 0xFFFFFFFFFFFFFFFF:016x}")
                    rd_pending -= 1
        if ev:
            fh.write(f"{t:>12} " + " ".join(ev) + "\n")
            fh.flush()
        elif os.environ.get("TRACE", "0") == "2" and cs != 3:
            fh.write(f"{t:>12} RAW cs{cs:02b} r{r:02b} c{c:02b} w{w:02b} "
                     f"a{addr:x} b{bank:02b}\n")
            fh.flush()


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_granite_col_major_gap(dut):
    drv, chan, _dfi, _mem = await _bringup(dut)
    cocotb.start_soon(_sched_trace(dut))

    t_refi = int(os.environ.get("TEST_TREFI", "585"), 0)
    txn = int(os.environ.get("TEST_TXN", "64"), 0)
    gap = int(os.environ.get("TEST_GAP", "8"), 0)
    seed = int(os.environ.get("TEST_SEED", "0xABCD1234"), 0)
    mismatches = []
    if os.environ.get("TRACE", "0") == "1":
        cocotb.start_soon(_dfi_monitor(dut))
        cocotb.start_soon(_rd_trace(dut))
        cocotb.start_soon(_pin_trace(dut))
    elif os.environ.get("TRACE", "0") == "2":
        cocotb.start_soon(_pin_trace(dut))
    # col-major: one row in the SAME bank per txn; wrap at the device.
    stride = (1 << COL_W) * DRAM_DEVICE_BYTES          # one row, same bank
    wrap = (1 << ROW_W) * stride - 1                   # device boundary

    def prog():
        results = {}
        results["build_id"] = drv.build_id()
        drv.soft_reset()
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=int(os.environ.get("TEST_T_PHY_WRLAT", "0")),
                               t_rddata_en=int(os.environ.get("TEST_T_RDDATA_EN", "4")),
                               rd_in_order=True)
        drv.set_dfi_phase(rd_phase=0, wr_phase=0, gear_ratio=GEAR_RATIO, bl=DRAM_BL)
        # Program the REAL JEDEC timings for the model's part at this clock
        # (like every production char flow) -- the RTL reset defaults
        # (tRFC=8, tWR=2) are far tighter than DDR2-650 and the model flags
        # cmd_during_refresh / tWR violations that under-programmed timings
        # create. t_rddata_en=4 matches set_controller_cfg above; without
        # this the "corruption" is the model punishing the config, not the
        # controller.
        timings = drv.set_jedec_timings(
            100_000_000.0, t_rddata_en=4, rddata_delay=0, t_phy_wrlat=0)
        results["timings"] = timings
        drv.set_refresh_interval(t_refi)
        drv.program_wr_engine(start_addr=0x0, burst_len=8, txn_count=txn,
                              stride_0=stride, wrap_mask_0=wrap, gap=gap,
                              lfsr_seed=seed, axi_size=dc.AXI_SIZE_8)
        drv.start_wr()
        results["wr"] = pm.wait_engine(drv, "wr", timeout_s=30)
        results["wr_status"] = drv.chargen.read("WR_GEN0_STATUS")
        drv.program_rd_engine(start_addr=0x0, burst_len=8, txn_count=txn,
                              stride_0=stride, wrap_mask_0=wrap, gap=gap,
                              lfsr_seed=seed, axi_size=dc.AXI_SIZE_8)
        drv.start_rd()
        results["rd"] = pm.wait_engine(drv, "rd", timeout_s=30)
        results["rd_status"] = drv.chargen.read("RD_GEN0_STATUS")
        exp, act, match, valid = drv.crc()
        results.update(exp=exp, act=act, match=match, valid=valid,
                       mism=drv.beats_mismatched(),
                       errors=drv.chargen.read("ERRORS"),
                       # the counts live on the dram's ViolationPolicy, not the
                       # DramStateModel -- getattr on the model always fell
                       # back to {} and the dict was silently empty (the
                       # 2026-10-17 tREFI=100 debug found 1527 logged
                       # violations behind an empty viol)
                       viol=dict(_dfi.dram.policy.soft_violation_counts))
        return results

    r = await bridge(prog)()
    dut._log.info("col_major_gap results: tREFI=%d txn=%d gap=%d -> %s",
                  t_refi, txn, gap,
                  {k: v for k, v in r.items() if k != "trace"})
    assert r["wr"], f"WRITE ENGINE HANG: wr never finished ({r})"
    assert r["rd"], f"READ ENGINE HANG: rd never finished ({r})"
    assert r["valid"] and r["match"] and r["mism"] == 0, \
        f"CRC/data mismatch: mism={r['mism']} errors={r['errors']}"


def test_granite_char_col_major_gap(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_char_uart_tb_top"
    test_name = "cocotb_test_granite_col_major_gap"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module, testcase=test_name,
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name,
                   "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                   "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      "--trace", "--trace-structs",
                      "-Wno-PINMISSING", FIELD_COMBO_VLT, "-Wno-WIDTHEXPAND",
                      "-Wno-WIDTHTRUNC"],
        waves=True,
        keep_files=True, timescale="1ns/1ps")
