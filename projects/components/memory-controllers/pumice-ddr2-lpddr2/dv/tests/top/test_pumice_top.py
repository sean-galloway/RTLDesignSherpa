# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Comprehensive top-level suite for the rearchitected pumice_top.

Ported from the old APB/FSM-era suite to the new interface (pumice_core +
PeakRDL CSR). Config is programmed BY NAME through the cpuif (PumiceTopCsrTB);
host traffic is driven ONLY through the AXI4 BFMs via AXI4Sequence + the shared
pumice_sequences builders; timing variety (backtoback / burst_pause /
slow_producer / constrained) comes from the AXI randomizer profiles, never from
hand-poked signals. Reads are checked against the sequence's expected payload,
which round-trips through the strict DFISlavePHY + golden MemoryModel. That
golden end-to-end check replaces the old FSM-internal divergence trackers (which
hooked u_command_scheduler / u_data_path hierarchy that no longer exists).

Geometry: AXI data width = DRAM_BEAT_WIDTH * DFI_RATE. One AXI burst
(BL/DFI_RATE beats) == one DRAM burst (BL beats).
"""

import os
import sys
import random

import cocotb
from cocotb.triggers import ClockCycles

from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.pumice_top_csr_tb import PumiceTopCsrTB  # noqa: E402
from tbclasses.pumice_sequences import (  # noqa: E402
    build_b2b_wr_rd_sequences, build_addr_pattern_sequences,
    build_patho_addresses,
)

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "dv/tb/pumice_top_csr_tb_top.f")

# ---- geometry (from env; defaults match the wrapper's RTL params) ----------
DFI_RATE   = int(os.environ.get("DFI_RATE", "2"))
DRAM_BEAT  = int(os.environ.get("DRAM_BEAT_WIDTH", "64"))
BL         = int(os.environ.get("BL", "8"))          # DRAM beats / burst
NUM_RANKS  = int(os.environ.get("NUM_RANKS", "1"))
NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 14, 10
DW         = DRAM_BEAT * DFI_RATE                     # AXI data width
BL_WORDS   = BL // DFI_RATE                           # AXI beats / burst
BASE       = 0x10000                                 # 64 KB-aligned base


async def _bringup(dut, *, mem_type="DDR2", page_policy=2, profile="backtoback",
                   t_refi=0x0400):
    # Seed the global RNG so the AXI BFM timing randomizers are DETERMINISTIC
    # run-to-run (else "flaky" failures can't be reproduced from the SEED).
    random.seed(int(os.environ.get("SEED", "1")))
    tb = PumiceTopCsrTB(dut, dram_beat_width=DRAM_BEAT, dfi_rate=DFI_RATE,
                        dram_bl=BL, num_ranks=NUM_RANKS, num_banks=NUM_BANKS,
                        row_width=ROW_WIDTH, col_width=COL_WIDTH, mem_type=mem_type)
    await tb.reset()
    tb.init_dfi_slave()
    await tb.program_defaults(page_policy=page_policy, mem_type=mem_type, t_refi=t_refi)
    await tb.wait_for_init_done()
    dut.s_axi_bready.value = 1
    dut.s_axi_rready.value = 1
    tb.init_axi_masters()
    tb.set_axi_timing_profile(profile)
    return tb


def _mask():
    return (1 << DW) - 1


def _golden_beat(tb, byte_addr):
    return int.from_bytes(bytes(tb.peek_memory(byte_addr, DW // 8)), "little")


async def _wr_rd_check(tb, wr_seq, rd_seq, *, drain=300):
    """Drive writes then reads (all via BFMs) and check against the golden
    MemoryModel using each transaction's OWN address from the sequence / BFM
    result (authoritative — no snoop race, robust to out-of-order multi-id read
    completion and repeated-address WAW patterns).

      WRITE path: golden[addr] == the LAST write the sequence issued to addr.
      READ  path: each read result's data == golden[its own addr]."""
    bpw = DW // 8
    await tb.run_writes(wr_seq, drain_cycles=drain)

    # expected golden = last write to each byte address (in-order commit => youngest)
    exp = {}
    for b in wr_seq.bursts:
        if not getattr(b, "is_write", True):
            continue
        for ki, val in enumerate(b.data):
            exp[b.addr + ki * bpw] = val & _mask()
    for byte_addr, val in exp.items():
        g = _golden_beat(tb, byte_addr)
        assert g == val, f"WRITE path: golden @ {byte_addr:#x} = {g:#x} != wrote {val:#x}"

    # reads: each result dict carries its own address; compare data vs golden
    rd_dicts = await tb.run_sequence(rd_seq)
    for d in rd_dicts:
        assert d.get("data") is not None, f"read @ {d.get('addr'):#x} returned no data ({d})"
        for ki, val in enumerate(d["data"]):
            byte_addr = d["addr"] + ki * bpw
            g = _golden_beat(tb, byte_addr)
            assert (val & _mask()) == g, \
                f"READ path: R @ {byte_addr:#x} = {val & _mask():#x} != golden {g:#x} (id={d.get('axid')})"


# ============================================================================
# Dispatching cocotb test (TEST_TYPE env selects the scenario)
# ============================================================================
@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_top(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    mem_type = os.environ.get("MEM_TYPE", "DDR2")
    level = os.environ.get("TEST_LEVEL", "basic").lower()
    seed = int(os.environ.get("SEED", "1"))
    rng = random.Random(seed)

    # REFRESH_TUNING.page_policy_or SOFTWARE encoding: 0=build default(OPEN),
    # 1=OPEN, 2=CLOSE, 3=reserved (was HYBRID -- retired). The old values here
    # predated the fab57682 encoding fix: "CLOSE" tests were writing 1 =
    # software-OPEN and the happy test 2 = software-CLOSE. Corrected to intent.
    if test_type in ("open_page_workload", "open_page_lpddr2",
                     "adapt_time_workload"):
        page_policy = 1        # OPEN (adapt_time layers its mode on top)
    else:
        page_policy = 2        # CLOSE

    tb = await _bringup(dut, mem_type=mem_type, page_policy=page_policy)

    if test_type == "adapt_time_workload":
        # Successor of the retired HAPPY_HYBRID workload: the Happy
        # Happy adaptive-timeout policy (PAGE_POLICY_CFG.policy_mode=4),
        # short TR so closes actually happen inside this workload.
        w = tb.csr_write_field
        await w("PAGE_POLICY_CFG", "policy_mode", 4)
        await w("PAGE_TIMEOUT_CFG", "tr_init", 24)
        await w("PAGE_TIMEOUT_CFG", "tr_min", 8)
        await w("PAGE_TIMEOUT_CFG", "tr_max", 96)
        await w("PAGE_TIMEOUT_CFG", "tr_step", 8)
        await w("PAGE_ADAPT_CFG", "mc_high_thr", 2)
        await w("PAGE_ADAPT_CFG", "mc_low_thr", 1)
        await w("PAGE_ADAPT_CFG", "check_interval", 256)

    def payload(bi, ki):
        return (rng.getrandbits(DW - 1) ^ ((bi << 8) | ki)) if False else \
               (((bi & 0xFFFF) << 16) | (ki & 0xFFFF))

    # ---- GATE ----
    if test_type in ("smoke", "smoke_lpddr2"):
        idv = await tb.csr_read_field("ID", "module_id")
        assert idv == 0xD2, f"ID.module_id {idv:#x} != 0xD2"
        assert int(dut.init_done_o.value) == 1
        if mem_type == "LPDDR2":
            # Verify the JEDEC LPDDR2 init programmed the expected mode registers
            # (decoded off the CA bus by the DFI slave). MR63=Reset, MR10=ZQ Init,
            # MR1=BL8/nWR3, MR2=RL3/WL1, MR3=DS 40ohm.
            mr = tb.dfi_slave.mode_regs
            expected = {63: 0x00, 10: 0xFF, 1: 0x23, 2: 0x01, 3: 0x02}
            for idx, val in expected.items():
                assert mr.get(idx) == val, \
                    f"LPDDR2 MR{idx} = {mr.get(idx)} != {val:#x} (decoded MRs: {mr})"
            tb.log.info(f"PASS smoke_lpddr2: init programmed MRs {mr}")
        tb.log.info(f"PASS smoke ({mem_type}): init_done + ID ok")
        return

    if test_type == "configure_via_csr":
        await tb.csr_write_field("REFRESH_TUNING", "page_policy_or", 0x2)
        await tb.csr_write_field("SCHED_TUNING", "force_inorder", 0x1)
        rt = await tb.csr_read_field("REFRESH_TUNING", "page_policy_or")
        st = await tb.csr_read_field("SCHED_TUNING", "force_inorder")
        assert rt == 0x2 and st == 0x1, f"readback rt={rt} st={st}"
        tb.log.info("PASS configure_via_csr: fields program+readback by name")
        return

    # ---- single write->read roundtrip ----
    if test_type in ("axi_write_smoke", "wr_rd_roundtrip"):
        wr, rd, exp = build_b2b_wr_rd_sequences(
            n_bursts=1, burst_len=BL_WORDS, base_addr=BASE, data_width=DW)
        if test_type == "axi_write_smoke":
            await tb.run_writes(wr)
            tb.log.info("PASS axi_write_smoke: write burst accepted+drained (BFM)")
            return
        await _wr_rd_check(tb, wr, rd)
        tb.log.info("PASS wr_rd_roundtrip: BFM write->read vs golden")
        return

    # ---- back-to-back multi-burst (stresses DQ pacing) ----
    if test_type in ("wr_rd_b2b_multi", "wr2rd_forward_burst"):
        n = {"basic": 8, "medium": 24, "full": 48}.get(level, 8)
        wr, rd, exp = build_b2b_wr_rd_sequences(
            n_bursts=n, burst_len=BL_WORDS, base_addr=BASE, data_width=DW)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info(f"PASS {test_type}: {n} back-to-back bursts (BFM) vs golden")
        return

    # ---- write+read each bank ----
    if test_type == "wr_rd_bank_sweep":
        addrs = [BASE + b * 0x2000 for b in range(NUM_BANKS)]   # bank stride 8 KB
        wr, rd, exp = build_addr_pattern_sequences(
            burst_len=BL_WORDS, data_width=DW, addresses=addrs)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info(f"PASS wr_rd_bank_sweep: all {NUM_BANKS} banks (BFM)")
        return

    # ---- fresh read each bank (preload golden, read-only sequence) ----
    if test_type == "fresh_read_each_bank":
        addrs = [BASE + b * 0x2000 for b in range(NUM_BANKS)]
        bpw = DW // 8
        for bi, a in enumerate(addrs):
            for ki in range(BL_WORDS):
                tb.preload_memory(a + ki * bpw,
                                  payload(bi, ki).to_bytes(bpw, "little"))
        rd = build_addr_pattern_sequences(
            burst_len=BL_WORDS, data_width=DW, addresses=addrs)[1]
        rd_dicts = await tb.run_sequence(rd)
        for d in rd_dicts:
            assert d.get("data") is not None, f"fresh-read @ {d.get('addr'):#x} no data"
            for ki, val in enumerate(d["data"]):
                g = _golden_beat(tb, d["addr"] + ki * bpw)
                assert (val & _mask()) == g, \
                    f"fresh-read @ {d['addr'] + ki * bpw:#x} = {val & _mask():#x} != golden {g:#x}"
        tb.log.info("PASS fresh_read_each_bank: preloaded reads (BFM) vs golden")
        return

    # ---- row-hit pattern (walking columns on one row) ----
    if test_type == "row_hit_pattern":
        bank, row = 2, 9
        k = {"basic": 6, "medium": 16, "full": 32}.get(level, 6)
        row_base = BASE + row * 0x10000 + bank * 0x2000
        addrs = [row_base + c * (BL_WORDS * (DW // 8)) for c in range(k)]
        wr, rd, exp = build_addr_pattern_sequences(
            burst_len=BL_WORDS, data_width=DW, addresses=addrs)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info("PASS row_hit_pattern: walking-column hits (BFM) vs golden")
        return

    # ---- workload mix (varied banks/rows) ----
    if test_type in ("workload_mix", "workload_mix_lpddr2"):
        n = {"basic": 12, "medium": 32, "full": 64}.get(level, 12)
        seen, addrs = set(), []
        while len(addrs) < n:
            a = (BASE + rng.randint(0, 127) * 0x10000
                 + rng.randint(0, NUM_BANKS - 1) * 0x2000
                 + rng.randint(0, 31) * (BL_WORDS * (DW // 8)))
            if a in seen:
                continue
            seen.add(a)
            addrs.append(a)
        wr, rd, exp = build_addr_pattern_sequences(
            burst_len=BL_WORDS, data_width=DW, addresses=addrs)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info(f"PASS {test_type}: {n}-burst mixed workload (BFM) vs golden")
        return

    # ---- out-of-order multi-id reads ----
    if test_type == "wr_rd_ooo_multi_id":
        await tb.csr_write_field("SCHED_TUNING", "force_inorder", 0x0)
        n = 8
        addrs = [BASE + k * 0x10000 + (k % NUM_BANKS) * 0x2000 for k in range(n)]
        wr, rd, exp = build_addr_pattern_sequences(
            burst_len=BL_WORDS, data_width=DW, addresses=addrs,
            rd_axid_fn=lambda bi: bi & 0xF)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info("PASS wr_rd_ooo_multi_id: distinct-id reads (BFM) vs golden")
        return

    # ---- open/happy-page workloads (row hits + misses) ----
    if test_type in ("open_page_workload", "adapt_time_workload", "open_page_lpddr2"):
        n = {"basic": 8, "medium": 20, "full": 40}.get(level, 8)
        addrs = [BASE + (k // 2) * 0x10000 + (k % NUM_BANKS) * 0x2000
                 + (k % 4) * (BL_WORDS * (DW // 8)) for k in range(n)]
        # de-dup while preserving order
        addrs = list(dict.fromkeys(addrs))
        wr, rd, exp = build_addr_pattern_sequences(
            burst_len=BL_WORDS, data_width=DW, addresses=addrs)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info(f"PASS {test_type}: open/adaptive-page hits+misses (BFM) vs golden")
        return

    raise AssertionError(f"unknown TEST_TYPE '{test_type}'")


# ============================================================================
# engine-mirror: N back-to-back bursts (stresses DQ pacing), BFM + profiles
# ============================================================================
@cocotb.test(timeout_time=180, timeout_unit="ms")
async def cocotb_test_engine_mirror(dut):
    n = int(os.environ.get("ENG_N", "64"))
    profile = os.environ.get("ENG_PROFILE", "backtoback")
    id_mode = os.environ.get("ENG_ID_MODE", "counter")
    id_fixed = int(os.environ.get("ENG_ID_FIXED", "0"))
    seed = int(os.environ.get("SEED", "1"))
    tb = await _bringup(dut, page_policy=2, profile=profile)  # CLOSE (software encoding)

    def wid(bi):
        if id_mode == "fixed":
            return id_fixed
        if id_mode == "lfsr":
            return (seed * (bi + 1) * 2654435761) & 0xF
        return bi & 0xF

    wr, rd, exp = build_b2b_wr_rd_sequences(
        n_bursts=n, burst_len=BL_WORDS, base_addr=BASE, data_width=DW,
        wr_axid_fn=wid, rd_axid_fn=wid)
    await _wr_rd_check(tb, wr, rd, drain=400)
    tb.log.info(f"PASS engine_mirror: N={n} profile={profile} id_mode={id_mode} (BFM)")


# ============================================================================
# pathological address patterns, BFM + profiles
# ============================================================================
@cocotb.test(timeout_time=180, timeout_unit="ms")
async def cocotb_test_patho(dut):
    kind = os.environ.get("PATHO_KIND", "bank_hazard")
    profile = os.environ.get("PATHO_PROFILE", "backtoback")
    tb = await _bringup(dut, page_policy=0, profile=profile)   # OPEN
    addrs = build_patho_addresses(kind, burst_len=BL, base_addr=BASE)
    wr, rd, _ = build_addr_pattern_sequences(
        burst_len=BL_WORDS, data_width=DW, addresses=addrs,
        rd_axid_fn=lambda bi: bi & 0xF)
    await _wr_rd_check(tb, wr, rd, drain=400)
    tb.log.info(f"PASS patho {kind} profile={profile} ({len(addrs)} bursts, BFM)")


@cocotb.test(timeout_time=180, timeout_unit="ms")
async def cocotb_test_refpb(dut):
    """PUMICE-006 Axis 3: refpb_rr (REF_CTRL.mode=2, LPDDR2 per-bank refresh).

    The DFI slave's DRAM model decodes REFpb off the CA bus (Table 60
    CA3r=0) and enforces the JESD209-2 semantics: the DEVICE'S internal
    rotor picks the bank, that bank must be precharged, the other banks
    stay accessible. Observables: dram.refpb_total / refpb_rotor and the
    model's violation counters (lenient policy COUNTS instead of raising —
    the assertions below turn the counts into the oracle).

      strap: REF_CTRL.perbank_supported must read 1 on the LPDDR2 build.
      arm A (REFab red guard): mode 0 -> REFs tick, refpb_total stays 0.
      arm B (mode 2): tREFIpb-paced REFpb commands -> refpb_total advances
        through a full rotation (>= 8, strict device order by construction),
        BFM write/read traffic across banks during the refpb stream stays
        golden, and zero refresh-class violations are recorded.
      arm C (disarm): mode 0 -> refpb_total freezes, REFab resumes.
    """
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC
    tb = await _bringup(dut, mem_type="LPDDR2", page_policy=1, t_refi=0x400)
    dram = tb.dfi_slave.dram
    w = tb.csr_write_field

    cap = await tb.csr_read_field("REF_CTRL", "perbank_supported")
    assert cap == 1, "LPDDR2 build: REF_CTRL.perbank_supported strap reads 0"

    def _refs():
        return tb.dfi_slave.cmd_counts.get(_DC.REF, 0)

    # Small tREFI for the whole test. The interval counter reloads on
    # EXPIRY, so the stale bring-up period (0x400) must elapse once first.
    await w("TIMINGS_RFC_REFI", "tREFI", 200)
    await ClockCycles(dut.aclk, 0x400 + 100)

    # ---- arm A: REFab baseline (red guard) --------------------------------
    b = _refs()
    await ClockCycles(dut.aclk, 1000)            # ~5 REFab ticks
    assert _refs() - b >= 2, "REFab baseline: refresh not ticking"
    assert dram.refpb_total == 0, (
        f"{dram.refpb_total} REFpb decoded in REFab mode -- mode gate leaks")

    # ---- arm B: refpb_rr ---------------------------------------------------
    await w("REF_TIMING_PB", "trefi_pb", 64)
    await w("REF_TIMING_PB", "trfc_pb", 8)
    await w("REF_CTRL", "mode", 2)
    pb0 = dram.refpb_total
    # stale REFab interval drains once, then >= 8 tREFIpb ticks
    await ClockCycles(dut.aclk, 200 + 64 * 10 + 300)
    pb_rot = dram.refpb_total - pb0
    assert pb_rot >= 8, (
        f"refpb_rr: only {pb_rot} REFpb across ~10 tREFIpb ticks -- the "
        f"per-bank command stream is not running (full rotation needs 8)")

    # traffic THROUGH the refpb stream: every bank written+read, golden.
    addrs = [BASE + bk * 0x2000 for bk in range(NUM_BANKS)]
    wr_seq, rd_seq, _ = build_addr_pattern_sequences(
        burst_len=BL_WORDS, data_width=DW, addresses=addrs,
        rd_axid_fn=lambda bi: bi & 0xF)
    try:
        await _wr_rd_check(tb, wr_seq, rd_seq, drain=400)
    except AssertionError:
        tb.log.warning(f"DBGREFPB refpb_total={dram.refpb_total} "
                       f"rotor={dram.refpb_rotor} "
                       f"cmds={ {k.name: v for k, v in tb.dfi_slave.cmd_counts.items()} } "
                       f"soft={dict(dram.policy._soft_counts)}")
        raise

    # the model recorded no refresh-class violations while all that ran
    soft = dram.policy._soft_counts
    for k in ("refpb_with_open_row", "cmd_during_refresh",
              "ref_with_open_row"):
        assert soft.get(k, 0) == 0, (
            f"{soft.get(k, 0)}x {k} recorded during the refpb stream")

    # ---- arm C: disarm -----------------------------------------------------
    await w("REF_CTRL", "mode", 0)
    await ClockCycles(dut.aclk, 300)             # let a queued REFpb finish
    pb1 = dram.refpb_total
    b = _refs()
    await ClockCycles(dut.aclk, 1200)
    assert dram.refpb_total == pb1, "REFpb still issuing after disarm"
    assert _refs() - b >= 2, "REFab did not resume after disarm"
    tb.log.info(f"PASS refpb_rr: strap ok, {pb_rot} REFpb (full rotation), "
                f"traffic golden through the stream, zero violations, disarm ok")


# ============================================================================
# pytest wrappers
# ============================================================================
import pytest  # noqa: E402


def _run(request, testcase, extra_env=None, params_over=None):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_top_csr_tb_top"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
              "COL_WIDTH": str(COL_WIDTH), "DFI_RATE": "2",
              "DRAM_BEAT_WIDTH": "64", "BL": "8",
              "NUM_ENTRIES": "8", "N_SRAM_SLOTS": "8"}
    if params_over:
        params.update(params_over)
    # Share one compiled sim across all tests with identical RTL params (the
    # cocotb testcase is selected at runtime), so the full suite compiles ~twice
    # (nr1 + nr2) instead of once per test — the run is otherwise recompile-bound.
    #
    # PUMICE-010: sharing is only safe WITHIN one process. cocotb_test's
    # Verilator path re-runs `verilator -cc` + make UNCONDITIONALLY on every
    # run() call (no staleness check), so two processes in one sim_build
    # regenerate the sources under each other's compiles/sims and destroy the
    # artifacts (the 48/31-spurious-FAIL clean-parallel tallies). Under
    # pytest-xdist each WORKER runs its tests sequentially, so a per-worker
    # suffix keeps the compile-sharing win inside a worker while removing all
    # cross-process sharing. ccache absorbs the duplicate C++ compiles.
    _worker = os.environ.get("PYTEST_XDIST_WORKER", "")
    build_key = "nr" + params["NUM_RANKS"] + (f"_{_worker}" if _worker else "")
    sim_build = os.path.join(tests_dir, "local_sim_build", "shared_" + build_key)
    os.makedirs(sim_build, exist_ok=True)
    # PUMICE-010: echo the per-test seed. pytest shows captured stdout for
    # FAILING tests, so a one-off red is reproducible with PUMICE_SEED=<n>
    # even after logs/ are cleaned.
    seed = os.environ.get("PUMICE_SEED", str(random.randint(0, 100000)))
    print(f"[seed] {tag} PUMICE_SEED={seed}")
    env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{tag}.log"),
           "COCOTB_LOG_LEVEL": "INFO",
           "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
           "SEED": seed,
           "TEST_LEVEL": os.environ.get("TEST_LEVEL", "basic"),
           "DFI_RATE": params["DFI_RATE"], "DRAM_BEAT_WIDTH": params["DRAM_BEAT_WIDTH"],
           "BL": params["BL"], "NUM_RANKS": params["NUM_RANKS"]}
    if extra_env:
        env.update(extra_env)
    env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase=testcase, sim_build=sim_build, simulator="verilator",
        extra_env=env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--public-flat-rw",
                      "-Wno-MULTIDRIVEN"],
        waves=(os.environ.get("WAVES", "0") == "1"),
        # cocotb_test compiles --trace-fst under waves= but never passes the
        # RUNTIME --trace argv (cocotb's verilator.cpp only opens dump.fst when
        # the sim binary gets --trace), so waves alone produces no dump. Pass it
        # through plus_args (runtime argv = [binary] + plus_args).
        plus_args=(["--trace"] if os.environ.get("WAVES", "0") == "1" else []),
        keep_files=True, timescale="1ns/1ps")


# LPDDR2 traffic (reads AND writes) now works end-to-end: bit-exact JESD209-2F CA
# encoding (rtl/LPDDR2_CA_ENCODING.md) + the DFI slave now handling WRA/RDA
# (auto-precharge variants) — LPDDR2's HAPPY_HYBRID row-miss policy issues WRA, which
# the slave previously dropped as "stray data beats". No LPDDR2 xfail remains.
_FUNC = ["smoke", "configure_via_csr", "axi_write_smoke", "wr_rd_roundtrip",
         "wr_rd_b2b_multi", "wr2rd_forward_burst", "wr_rd_bank_sweep",
         "fresh_read_each_bank", "row_hit_pattern", "workload_mix",
         "wr_rd_ooo_multi_id", "open_page_workload", "adapt_time_workload",
         "smoke_lpddr2", "open_page_lpddr2", "workload_mix_lpddr2"]


@pytest.mark.parametrize("test_type", _FUNC)
def test_pumice_top(request, test_type):
    mem = "LPDDR2" if test_type.endswith("lpddr2") else "DDR2"
    _run(request, "cocotb_test_pumice_top",
         extra_env={"TEST_TYPE": test_type, "MEM_TYPE": mem})


# Sustained same-bank back-to-back traffic (engine_mirror N up to 1024, patho
# same-bank ACT/PRE/RD churn) previously failed with write beat-drops / read-0 —
# now FIXED by the FSM-free bank_timer rework: the old double-registered bank
# readiness (behind a 3-state FSM) let the arbiter and the refresh gate schedule
# into STALE bank state, which manifested as data landing wrong / a beat dropped.
# Single-stage countdown "safe" timers (bank_timer.sv) made readiness reflect the
# just-issued command with one register of latency, and the whole cluster cleared
# (incl. the refresh-vs-ACT race, repro PUMICE_SEED=7 patho hit_miss). Now hard tests.
_ENG_N = [16, 17, 18, 32, 64, 128, 1024]
_ENG_ID = [("fixed", 0), ("fixed", 5), ("fixed", 15), ("counter", 0), ("lfsr", 1), ("lfsr", 42)]
_PATHO_PROFILES = ["backtoback", "burst_pause", "slow_producer"]


@pytest.mark.parametrize("n", _ENG_N)
def test_pumice_top_engine_mirror_kbN(request, n):
    _run(request, "cocotb_test_engine_mirror",
         extra_env={"ENG_N": str(n), "ENG_PROFILE": "backtoback", "ENG_ID_MODE": "counter"})


@pytest.mark.parametrize("id_mode,id_fixed", _ENG_ID)
def test_pumice_top_engine_mirror_idmode(request, id_mode, id_fixed):
    _run(request, "cocotb_test_engine_mirror",
         extra_env={"ENG_N": "64", "ENG_PROFILE": "backtoback",
                    "ENG_ID_MODE": id_mode, "ENG_ID_FIXED": str(id_fixed)})


@pytest.mark.parametrize("profile", ["backtoback", "burst_pause", "slow_producer"])
def test_pumice_top_engine_mirror_profile(request, profile):
    _run(request, "cocotb_test_engine_mirror",
         extra_env={"ENG_N": "64", "ENG_PROFILE": profile, "ENG_ID_MODE": "counter"})


_PATHO_KINDS = ["bank_hazard", "page_miss_sustained", "page_close_boundary", "hit_miss_oscillation"]


@pytest.mark.parametrize("kind", _PATHO_KINDS)
@pytest.mark.parametrize("profile", _PATHO_PROFILES)
def test_pumice_top_patho_addr_pattern(request, kind, profile):
    _run(request, "cocotb_test_patho",
         extra_env={"PATHO_KIND": kind, "PATHO_PROFILE": profile})


def test_pumice_top_nr2(request):
    """Dual-rank build smoke + workload."""
    _run(request, "cocotb_test_pumice_top",
         extra_env={"TEST_TYPE": "workload_mix", "MEM_TYPE": "DDR2"},
         params_over={"NUM_RANKS": "2"})


def test_pumice_top_refpb(request):
    """PUMICE-006 Axis 3: LPDDR2 per-bank refresh round-robin."""
    _run(request, "cocotb_test_refpb", extra_env={"MEM_TYPE": "LPDDR2"})
