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
from cocotb.triggers import ClockCycles, RisingEdge

from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.pumice_top_csr_tb import PumiceTopCsrTB  # noqa: E402
from CocoTBFramework.components.axi4.axi4_sequence import (  # noqa: E402
    AXI4Sequence, run_axi4_sequence_engine,
)
from tbclasses.pumice_sequences import (  # noqa: E402
    build_b2b_wr_rd_sequences, build_addr_pattern_sequences,
    build_patho_addresses,
)

# REG_LEVEL SELECTS THE DEPTH. This test grades on basic / medium / full, but
# the regression speaks GATE / FUNC / FULL, and the conftest stamp used to hand
# it `gate` and `func` -- neither of which is in the depth tables, so both fell
# to the `basic` default and a FUNC run was exactly as shallow as a GATE run.
# The `medium` tier was dead code that no run ever reached. This maps the
# regression's names onto the tables so the three levels are distinct.
_LEVEL = {"GATE": "gate", "BASIC": "gate",
          "FUNC": "func", "MEDIUM": "func",
          "FULL": "full"}.get(
    (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
     or "FUNC").upper(), "func")

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "dv/tb/pumice_top_csr_tb_top.f")

# ---- geometry -------------------------------------------------------------
# Selected per TEST by the wrapper (see GEOMETRIES), not by a global env knob
# nobody sets. BL4-on-x16 is the BOARD's shape and BL8 is the historical sim
# point; both are now real pytest parameters so the board geometry actually
# runs instead of being merely "overridable" (PUMICE-028).
DFI_RATE   = int(os.environ.get("DFI_RATE", "2"))
DRAM_BEAT  = int(os.environ.get("DRAM_BEAT_WIDTH", "64"))
# Read DRAM_BL, which is what the wrapper actually exports. This used to read
# "BL" -- a name nothing ever set -- so the Python side believed BL=8 no matter
# what the RTL was built as. At the default that is harmless because both
# formulas agree; at the board point it silently computes 2 AXI beats per burst
# where the hardware has 1, which is exactly how a geometry "override" can be
# present and still never test anything. "BL" stays as a fallback for anyone
# who set it by hand.
BL         = int(os.environ.get("DRAM_BL", os.environ.get("BL", "8")))
# Device width. Defaults to the beat width (the historical sim point, where
# device == beat); the board's x16 part is 16.
DRAM_DEV_W = int(os.environ.get("DRAM_DEVICE_WIDTH", str(DRAM_BEAT)))
NUM_RANKS  = int(os.environ.get("NUM_RANKS", "1"))
NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 14, 10
DW         = DRAM_BEAT * DFI_RATE                     # AXI data width
# AXI beats per DRAM burst = (BL x device bits) / core width -- the same
# formula test_pumice_core_dfi.py uses. The old `BL // DFI_RATE` happens to
# agree when device == beat, and is wrong the moment it does not.
BL_WORDS   = max(1, (BL * DRAM_DEV_W) // DW)
BASE       = 0x10000                                 # 64 KB-aligned base

# name -> (dfi_rate, dram_beat_width, dram_device_width, dram_bl)
GEOMETRIES = {
    "bl8":   (2, 64, 64, 8),   # historical sim point: one burst = 4 AXI beats
    "bl4x16": (2, 32, 16, 4),  # the Nexys A7 board: one burst = 1 AXI beat
}


def _geom_params(name):
    """RTL parameters + matching TEST env for one named geometry."""
    rate, beat, dev, bl = GEOMETRIES[name]
    return ({"DFI_RATE": str(rate), "DRAM_BEAT_WIDTH": str(beat),
             "DRAM_BL": str(bl)},
            {"DRAM_DEVICE_WIDTH": str(dev)})


async def _bringup(dut, *, mem_type="DDR2", page_policy=2, profile="backtoback",
                   t_refi=None):
    # Seed the global RNG so the AXI BFM timing randomizers are DETERMINISTIC
    # run-to-run (else "flaky" failures can't be reproduced from the SEED).
    random.seed(int(os.environ.get("SEED", "1")))
    tb = PumiceTopCsrTB(dut, dram_beat_width=DRAM_BEAT, dfi_rate=DFI_RATE,
                        dram_bl=BL, num_ranks=NUM_RANKS, num_banks=NUM_BANKS,
                        row_width=ROW_WIDTH, col_width=COL_WIDTH, mem_type=mem_type)
    await tb.reset()
    tb.init_dfi_slave()
    # T_REFI from the environment when the caller did not pin one, so a test
    # can drive refreshes INTO its traffic instead of around it.
    if t_refi is None:
        t_refi = int(os.environ.get("T_REFI", "0x400"), 0)
    await tb.program_defaults(page_policy=page_policy, mem_type=mem_type, t_refi=t_refi)
    await tb.wait_for_init_done()
    # bready/rready are NOT tied high here: init_axi_masters() builds the
    # master BFMs, which own every signal on s_axi including the response
    # readies. Poking them first only creates a second driver (PUMICE-014).
    tb.init_axi_masters()
    tb.set_axi_timing_profile(profile)

    # PUMICE-012/013: opt-in trackers. This is the MEANINGFUL place to
    # measure AXI utilization -- the masters here are real BFMs at the
    # 'backtoback' randomizer profile (zero inter-beat delay), so a low
    # utilization number reflects the DUT, not a lazy driver. (The core
    # TB hand-drives its stimulus and starves the bus by construction --
    # 91% starvation / 0% backpressure there measures the testbench.)
    if os.environ.get("PUMICE_TRACKERS", "0") == "1":
        from tbclasses.trackers import wire_trackers, wire_axi_channels
        wire_axi_channels(dut, prefix="s_axi_", log=tb.log, clk_signal="aclk")
        wire_trackers(dut, log=tb.log, num_banks=NUM_BANKS, scope_paths={
            "sched":   "u_top.u_core.u_sched.u_arbiter",
            "btmr":    "u_top.u_core.u_sched.u_bank_timers",
            "refr":    "u_top.u_core.u_sched.u_refresh",
            "pgpol":   "u_top.u_core.u_sched.u_page_policy",
            "init":    "u_top.u_core.u_sched.u_init",
            "camrd":   "u_top.u_core.u_ifc.u_rd_cam",
            "camwr":   "u_top.u_core.u_ifc.u_wr_cam",
            "dficmd":  "u_top.u_core.u_dfi.u_cmd",
            "wrbeat":  "u_top.u_core.u_dfi.u_wr",
            "rdalign": "u_top.u_core.u_dfi.u_rd",
        })
        tb.log.info(f"PUMICE_TRACKERS=1: trackers wired (axi profile={profile})")

    return tb


def _mask():
    return (1 << DW) - 1


async def _dq_collision_monitor(dut, stop, hits):
    """Flag every cycle where the controller drives WRITE data while a READ is
    still returning.

    This is the PUMICE-037 mechanism, and the reason it never showed up in
    simulation before: DFI carries wrdata and rddata on SEPARATE buses, so the
    overlap is perfectly legal AT THE DFI BOUNDARY and only becomes destructive
    on the PHY's shared DQ pins, one layer below anything a DFI-level model
    represents. The board ILA (reports/ila_pumice037_wrdata_into_read.csv)
    caught 49 such cycles, with 80% of corrupted beats landing within 12 cycles
    of one and 51% of them reading back all-ones -- an undriven bus.

    The COLLISION cannot be simulated here. The OVERLAP can, exactly, because
    both enables are controller outputs. So this turns a defect that only
    reproduces on silicon into one a sim can fail on.

    Deliberately not an RTL assertion: this repo keeps properties out of the
    modules (they break some tools), so the check lives in the testbench.
    """
    while not stop[0]:
        await RisingEdge(dut.aclk)
        try:
            # TB-top net names, not the DUT port names: the DUT here is the
            # wrapper pumice_top_csr_tb_top, which wires pumice_top's dfi_*_o
            # ports to phy_dfi_* nets one level up.
            wen = int(dut.phy_dfi_wrdata_en.value)
            ren = int(dut.phy_dfi_rddata_en.value)
            rvl = int(dut.phy_dfi_rddata_valid.value)
        except (ValueError, AttributeError):
            continue          # X/Z during reset
        if wen and (ren or rvl):
            hits.append((cocotb.utils.get_sim_time("ns"), wen, ren, rvl))


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



# ===========================================================================
# Partial-WSTRB writes
# ===========================================================================
# A masked byte must be PRESERVED, not zeroed. That is the whole contract:
# WSTRB=0 on a lane means "do not write this byte", and pumice turns it into
# DRAM DM=1 (pumice_dfi_wr_serializer: dfi_wrdata_mask_o = ~wd_strb_i). If a
# masked lane instead lands as 0x00, a read-modify-write anywhere above the
# controller silently corrupts the neighbouring bytes -- and no full-strobe
# test can see it, because every lane is written every time.
#
# Nothing here covered that: every existing sequence writes full strobes
# (AXI4Sequence.add_write hardcodes strb = all-ones). Partial strobes reach
# pumice in two ways that are NOT the generator's doing:
#   * a narrow host write (a CPU storing one word), and
#   * the 64->128 down-gear converter, which turns ONE 64-bit host beat into
#     one 128-bit core beat with half the lanes masked.
# The second is how the ddr2-char harness produces them.

_STRB_PATTERNS = [
    ("low_half",    lambda n: (1 << (n // 2)) - 1),          # 0x00FF @16B
    ("high_half",   lambda n: ((1 << (n // 2)) - 1) << (n // 2)),
    ("first_byte",  lambda n: 0x1),
    ("last_byte",   lambda n: 1 << (n - 1)),
    ("alternating", lambda n: int("01" * (n // 2), 2)),
    ("sparse",      lambda n: (1 << (n - 1)) | 0x1),
    ("none",        lambda n: 0x0),                          # legal: writes nothing
    ("all",         lambda n: (1 << n) - 1),                 # control
]


def _apply_strb(seq, mask):
    for b in seq.bursts:
        if getattr(b, "is_write", True):
            b.strb = mask


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_top_partial_strb(dut):
    """Masked bytes must survive a partial-strobe write untouched."""
    pattern = os.environ.get("STRB_PATTERN", "low_half")
    blen    = int(os.environ.get("BURST_LEN", "1"))
    nbytes  = DW // 8
    mask    = dict(_STRB_PATTERNS)[pattern](nbytes)

    tb = await _bringup(dut, mem_type="DDR2", page_policy=2)

    # 1. Preload with a known non-zero pattern, FULL strobes. If a later masked
    #    lane comes back as 0x00 we can tell it apart from "never written".
    pre, _, _ = build_b2b_wr_rd_sequences(
        n_bursts=1, burst_len=blen, base_addr=BASE, data_width=DW,
        payload_fn=lambda bi, ki: 0xA5A5A5A5A5A5A5A5A5A5A5A5A5A5A5A5 & _mask())
    await tb.run_writes(pre, drain_cycles=300)

    before = [bytes(tb.peek_memory(BASE + k * nbytes, nbytes)) for k in range(blen)]
    for k, b in enumerate(before):
        assert any(b), f"preload beat {k} never landed ({b.hex()}) -- test setup"

    # 2. Overwrite the SAME addresses with a partial strobe.
    wr, _, _ = build_b2b_wr_rd_sequences(
        n_bursts=1, burst_len=blen, base_addr=BASE, data_width=DW,
        payload_fn=lambda bi, ki: 0x5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C & _mask())
    _apply_strb(wr, mask)
    await tb.run_writes(wr, drain_cycles=300)

    # 3. Byte-granular check: strobed lanes take the new value, masked lanes
    #    keep the old one.
    newv = (0x5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C & _mask()).to_bytes(nbytes, "little")
    bad = []
    for k in range(blen):
        got = bytes(tb.peek_memory(BASE + k * nbytes, nbytes))
        for i in range(nbytes):
            want = newv[i] if (mask >> i) & 1 else before[k][i]
            if got[i] != want:
                bad.append((k, i, got[i], want, bool((mask >> i) & 1)))
    assert not bad, (
        f"strb={pattern}({mask:#06x}) blen={blen}: {len(bad)} byte(s) wrong in "
        f"MEMORY. First 6 (beat, byte, got, want, was_strobed): {bad[:6]}. "
        f"A masked byte that came back 0x00 means the strobe was dropped and "
        f"the lane was written with zero instead of left alone.")

    # 4. Now read the SAME bytes back over AXI. Step 3 checked the write path
    #    against the memory model; this checks the READ path returns what is
    #    actually in memory -- including the half-written words a partial
    #    strobe leaves behind, which is the case the read beat-budget has to
    #    frame correctly.
    rd = AXI4Sequence(name="partial_rd", data_width=DW)
    rd.add_read(BASE, blen)
    rd_dicts = await tb.run_sequence(rd)
    assert len(rd_dicts) == 1, f"expected 1 read burst, got {len(rd_dicts)}"
    got_beats = rd_dicts[0].get("data")
    assert got_beats is not None, f"read returned no data: {rd_dicts[0]}"
    assert len(got_beats) == blen, (
        f"read {len(got_beats)} beats, asked for {blen} -- the read path is "
        f"not framing a sub-DRAM-burst read to the requested length")
    rbad = []
    for k in range(blen):
        want = int.from_bytes(bytes(tb.peek_memory(BASE + k * nbytes, nbytes)),
                              "little")
        if (got_beats[k] & _mask()) != want:
            rbad.append((k, hex(got_beats[k] & _mask()), hex(want)))
    assert not rbad, (
        f"strb={pattern} blen={blen}: AXI read disagrees with memory at "
        f"beat(s) {rbad} -- write path was correct, read path is not")

    tb.log.info("PASS partial_strb %s (%#06x) blen=%d: %d bytes verified "
                "in memory AND through the AXI read path",
                pattern, mask, blen, blen * nbytes)




@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_top_partial_rd(dut):
    """Sub-DRAM-burst READS at every length and every offset in the burst.

    A DRAM burst always returns BL_WORDS beats; the host may ask for fewer,
    and may start part-way in. pumice_rd_intake carries a per-sub beat budget
    so the surplus beats are consumed from the CAM and dropped instead of
    being pushed at the host. This is the suite for that budget: nothing else
    exercises "asked for 1, DRAM returned 4".

    Checks all three things that can go wrong independently:
      * BEAT COUNT   -- surplus beats leaking onto R (or beats going missing)
      * DATA         -- the wrong beats forwarded (an offset error)
      * COMPLETION   -- the burst framing/RLAST, caught as a hang or a
                        never-completing read
    """
    nbeats = int(os.environ.get("RD_BEATS", "1"))
    offset = int(os.environ.get("RD_OFFSET", "0"))
    nbytes = DW // 8
    # Keep the read inside ONE DRAM burst so each case is a pure partial read
    # rather than a split across two bursts (that is the burst_len sweep's job).
    if offset + nbeats > BL_WORDS:
        nbeats = BL_WORDS - offset
    if nbeats < 1:
        raise cocotb.result.TestSuccess(
            f"offset {offset} leaves no room in a {BL_WORDS}-beat burst")

    tb = await _bringup(dut, mem_type="DDR2", page_policy=2)

    # Fill one whole DRAM burst with per-beat-distinguishable data, so a beat
    # forwarded from the wrong position is caught by VALUE, not just by count.
    span = BL_WORDS
    pre, _, _ = build_b2b_wr_rd_sequences(
        n_bursts=1, burst_len=span, base_addr=BASE, data_width=DW,
        payload_fn=lambda bi, ki: (0xBEEF0000 + ki) & _mask())
    await tb.run_writes(pre, drain_cycles=300)

    # SEVERAL consecutive short reads, not one. A single short read cannot
    # detect surplus beats: the master stops collecting at RLAST, so beats the
    # DRAM returned beyond the request are simply never looked at. They leak
    # into the NEXT burst's data instead -- so the bug only becomes visible
    # once a second read follows. (Verified: with the beat budget disabled, a
    # single-burst version of this test passes clean.)
    N_RD = 4
    addr0 = BASE + offset * nbytes

    # COUNT R BEATS ON THE BUS. A data check alone cannot see surplus beats:
    # they carry the burst's own RID and arrive AFTER its RLAST, so the master
    # BFM discards them and every value still matches. The damage is a
    # PROTOCOL violation (beats past RLAST) plus R bandwidth burned fetching
    # data nobody asked for. Only a bus-level count exposes it -- verified by
    # mutation: with the beat budget disabled, the data checks all pass and
    # this counter is what fails.
    r_beats = 0

    async def _count_r():
        nonlocal r_beats
        while True:
            await RisingEdge(dut.aclk)
            try:
                if int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value):
                    r_beats += 1
            except ValueError:
                pass
    counter = cocotb.start_soon(_count_r())
    rd = AXI4Sequence(name="sub_rd", data_width=DW)
    for i in range(N_RD):
        rd.add_read(addr0, nbeats, axid=i & 0x7)
    rd_dicts = await tb.run_sequence(rd)

    assert len(rd_dicts) == N_RD, (
        f"expected {N_RD} read bursts, got {len(rd_dicts)}")
    for bi, d in enumerate(rd_dicts):
        data = d.get("data")
        assert data is not None, f"read {bi} @ {addr0:#x} no data: {d}"
        assert len(data) == nbeats, (
            f"read {bi} @ {addr0:#x} asked for {nbeats} beat(s), got "
            f"{len(data)} -- a DRAM burst is {span} beats, so surplus beats "
            f"are leaking onto R")
        for k in range(nbeats):
            want = int.from_bytes(
                bytes(tb.peek_memory(addr0 + k * nbytes, nbytes)), "little")
            assert (data[k] & _mask()) == want, (
                f"read {bi} @ {addr0:#x} beat {k} = {data[k] & _mask():#x} "
                f"!= {want:#x} -- wrong beat forwarded (offset {offset}, "
                f"len {nbeats}); a surplus beat from the previous burst "
                f"shifts every following beat")
    await ClockCycles(dut.aclk, 200)      # let any surplus beats drain out
    counter.kill()
    assert r_beats == N_RD * nbeats, (
        f"{r_beats} R beats on the bus, expected {N_RD * nbeats} "
        f"({N_RD} bursts x {nbeats}). A DRAM burst returns {span} beats; the "
        f"beats past each request must be dropped inside the controller, not "
        f"driven onto R after RLAST.")
    tb.log.info("PASS partial_rd: %d x %d beat(s) at offset %d of a %d-beat "
                "DRAM burst, %d R beats on the bus (exact)",
                N_RD, nbeats, offset, span, r_beats)


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
        await tb.csr_write_field("SCHED_POLICY", "order_mode", 0x1)
        rt = await tb.csr_read_field("REFRESH_TUNING", "page_policy_or")
        st = await tb.csr_read_field("SCHED_POLICY", "order_mode")
        assert rt == 0x2 and st == 0x1, f"readback rt={rt} st={st}"
        await tb.csr_write_field("SCHED_POLICY", "order_mode", 0x0)
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
        n = {"gate": 8, "basic": 8, "func": 24, "medium": 24, "full": 48}.get(level, 8)
        wr, rd, exp = build_b2b_wr_rd_sequences(
            n_bursts=n, burst_len=BL_WORDS, base_addr=BASE, data_width=DW)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info(f"PASS {test_type}: {n} back-to-back bursts (BFM) vs golden")
        return

    # ---- burst-length coverage: EVERY legal AxLEN must work ----
    # A DRAM burst is BL_WORDS AXI beats. A host burst may be ANY legal AxLEN,
    # including shorter than that: pumice_wr_splitter pads the write out to a
    # whole DRAM burst with zero-strobe filler beats (strb=0 -> DM=1, the device
    # writes nothing) and pumice_rd_intake forwards only the beats the host
    # actually asked for out of the full burst the DRAM returns.
    #
    # This is the end-to-end proof of that: golden-memory check on the WRITE
    # side catches a filler beat that wrongly wrote (it would clobber the
    # neighbouring words), and the READ side catches surplus/short R framing.
    # Unit tests on the splitter cannot see either failure mode.
    if test_type == "burst_len":
        blen = int(os.environ.get("BURST_LEN", "1"))
        n = {"gate": 4, "basic": 4, "func": 8, "medium": 8, "full": 16}.get(level, 4)
        wr, rd, exp = build_b2b_wr_rd_sequences(
            n_bursts=n, burst_len=blen, base_addr=BASE, data_width=DW)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info("PASS burst_len=%d: %d bursts write+read vs golden "
                    "(DRAM burst = %d beats)", blen, n, BL_WORDS)
        return

    # ---- write+read each bank ----
    # ---- concurrent read + write, reader paced (PUMICE-037) ----------------
    if test_type == "concurrent_rw":
        # Reproduce the board defect at the CONTROLLER, not through the char
        # harness: concurrent read and write with the READER pacing itself.
        #
        # On silicon, reader gap 0..7 is clean and 8..15 returns wrong data and
        # corrupts cells. The char-framework sim does not reproduce it, and the
        # leading explanation is geometry: that build is BL8 where the board is
        # BL4, so one DRAM burst is 2 AXI beats there against 1 on silicon
        # (PUMICE-028). This test lives where the geometry is an env knob, so
        # the board point is actually reachable:
        #     TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16
        #
        # Writer and reader use DISJOINT banks, which is the board's failing
        # row_major 1+1 shape -- the two never touch the same address, so a
        # mismatch cannot be a same-address race between them.
        gap = int(os.environ.get("RD_GAP", "8"))
        depth = int(os.environ.get("RD_DEPTH", "1"))   # reads in flight
        # Enough bursts that a deep group is a group and not one short batch.
        n   = max({"gate": 32, "basic": 32, "func": 64, "medium": 64,
                   "full": 128}.get(level, 32), depth * 2)
        n   = int(os.environ.get("RD_N", str(n)))
        bpw = DW // 8
        # AXI BEATS PER BURST -- the board's shape, not this test's default.
        #
        # The board generators issue AxLEN=8 bursts (8 beats x 8 B = 64 B), so
        # ONE AXI transaction becomes 8 DRAM column commands. The default here
        # is BL_WORDS, which is 1 for the board geometry (bl4x16: 4*16//64 = 1)
        # -- one column command per transaction. That is not a smaller version
        # of the board's command stream, it is a different one, and it is the
        # likeliest reason this test passes at rd_gap=15 while silicon fails.
        NB = int(os.environ.get("RD_BEATS", str(BL_WORDS)))
        WR_BANK, RD_BANK = 0, 4
        wr_base = BASE + WR_BANK * 0x2000
        # SPAN must cross pages and banks. At the old NB=1 / n=32 this moved
        # 256 B and never left a single 2048 B page, so after the first ACTIVATE
        # it generated no page management at all -- while the board marches
        # 128 KB (64 pages) and crosses a bank every bank_stride (2048 B) with a
        # writer doing the same thing concurrently. Keep the reader clear of the
        # writer's whole span so a mismatch still cannot be a same-cell race.
        span = n * NB * bpw
        rd_base = BASE + max(RD_BANK * 0x2000, span + 0x2000)

        # Preload the reader's region into the golden model AND the device, so
        # the reader has something correct to find.
        for k in range(n):
            for ki in range(NB):
                tb.preload_memory(rd_base + (k * NB + ki) * bpw,
                                  payload(RD_BANK, k * NB + ki)
                                  .to_bytes(bpw, "little"))

        wr_reqs = [(wr_base + k * NB * bpw,
                    [payload(WR_BANK, k * NB + ki)
                     for ki in range(NB)]) for k in range(n)]

        rd_results: list = []

        async def _engine(seq):
            """Engine-style: AR/AW queued back-to-back, no per-burst response
            wait. The default runner serialises a burst against its own B/R and
            leaves ~5-15 idle cycles between commands, which caps outstanding at
            one and is NOT what the board's generators do."""
            return await run_axi4_sequence_engine(
                seq, master_wr=tb.axi_master_wr, master_rd=tb.axi_master_rd,
                log=tb.log)

        async def _writer():
            wseq = AXI4Sequence(name="cc_wr", data_width=DW)
            for a, data in wr_reqs:
                wseq.add_write(a, list(data), axid=0)
            await _engine(wseq)

        async def _reader():
            # GROUPS of `depth` bursts issued back-to-back, then `gap` idle
            # clocks. This is the board's shape: its reader runs many reads
            # outstanding AND paces between them. At depth=1 the gap lands
            # with an empty pipe and nothing is ever in flight across it --
            # which is the state the first version of this test measured, and
            # why it could not have seen an in-flight hazard.
            for k0 in range(0, n, depth):
                grp = list(range(k0, min(k0 + depth, n)))
                rseq = AXI4Sequence(name=f"cc_rd{k0}", data_width=DW)
                for k in grp:
                    rseq.add_read(rd_base + k * NB * bpw,
                                  length=NB, axid=k & 0xF)
                res = await _engine(rseq)
                for k, d in zip(grp, res):
                    rd_results.append((rd_base + k * NB * bpw,
                                       list(d.get("data") or [])))
                if gap:
                    await ClockCycles(dut.aclk, gap)

        wt = cocotb.start_soon(_writer())
        rt = cocotb.start_soon(_reader())
        await wt
        await rt
        await ClockCycles(dut.aclk, 300)

        # A verdict needs a COUNT behind it. The golden model is the same
        # memory the DFI slave serves, so a read that returned NOTHING compares
        # nothing and the loop below passes vacuously -- which is how a
        # concurrent test can report clean while measuring zero beats. Assert
        # the traffic happened before asserting it was correct.
        want_beats = n * NB
        got_beats = sum(len(b) for _a, b in rd_results)
        assert len(rd_results) == n, (
            f"concurrent_rw rd_gap={gap}: {len(rd_results)} read bursts "
            f"returned, programmed {n}")
        assert got_beats == want_beats, (
            f"concurrent_rw rd_gap={gap}: compared {got_beats} read beats, "
            f"expected {want_beats} -- the check would have been vacuous")

        # 1. every READ beat matches golden -- the board's "returns bad data".
        bad_rd = []
        for a, beats in rd_results:
            for ki, val in enumerate(beats):
                ba = a + ki * bpw
                g = _golden_beat(tb, ba)
                if (val & _mask()) != g:
                    bad_rd.append((ba, val & _mask(), g))
        # 2. every WRITTEN cell holds what was written -- the board's
        #    "corrupts cells". Checked separately because on silicon the two
        #    symptoms come apart: disjoint banks gave transient bad reads with
        #    memory intact, overlapping ranges left real damage.
        bad_wr = []
        for a, data in wr_reqs:
            for ki, val in enumerate(data):
                ba = a + ki * bpw
                g = _golden_beat(tb, ba)
                if g != (val & _mask()):
                    bad_wr.append((ba, g, val & _mask()))

        assert not bad_rd, (
            f"concurrent_rw rd_gap={gap}: {len(bad_rd)} read beat(s) != golden "
            f"(first: @{bad_rd[0][0]:#x} got {bad_rd[0][1]:#x} want "
            f"{bad_rd[0][2]:#x})")
        assert not bad_wr, (
            f"concurrent_rw rd_gap={gap}: {len(bad_wr)} written cell(s) wrong "
            f"(first: @{bad_wr[0][0]:#x} holds {bad_wr[0][1]:#x} wrote "
            f"{bad_wr[0][2]:#x})")
        tb.log.info(f"PASS concurrent_rw: rd_gap={gap}, {n} bursts each way, "
                    f"BL={BL} beat={DRAM_BEAT} dev={DRAM_DEV_W} "
                    f"({NB} AXI beat(s)/burst, span {span} B = "
                    f"{span/2048:.1f} pages)")
        return

    if test_type == "gen_replica":
        # EXACT replica of the two HARDWARE generators, driven through the AXI4
        # master BFMs at the pumice_top boundary.
        #
        # The concurrent_rw shape above approximates the reader as "issue a
        # group, then idle". That is NOT what the silicon engines do, and the
        # difference is the whole defect. From
        # rtl/amba/shared/axi4_master_rd_crc_check.sv:
        #
        #     input logic [3:0] cfg_rd_gap,   // 0..15 cycles between RLAST on
        #                                     // burst N and the AR for N+1
        #     assign fub_arvalid   = (r_state == S_RUN) && ...
        #     assign w_r_consuming = (r_state == S_RUN);
        #
        #   ... else if (r_rd_gap != 4'd0) begin
        #           r_state    <= S_GAP;      // entered on EVERY rlast
        #           r_gap_left <= r_rd_gap;
        #
        # so a non-zero gap does TWO things on every RLAST: it stops issuing
        # ARs, and it DEASSERTS RREADY -- the header says it outright, "cfg_rd_
        # gap > 0 pauses both AR and R together". With reads still outstanding
        # that backpressures read data already in flight, while a concurrent
        # writer keeps running. An "issue a group then idle" model never
        # deasserts RREADY mid-return and therefore cannot produce that state,
        # which is why this test passed at rd_gap=15 while silicon failed.
        #
        # The writer is symmetric (cfg_wr_gap > 0 pauses AW and W together).
        # RREADY is driven through the BFM's documented ready_policy hook, not
        # by poking the handshake.
        gap  = int(os.environ.get("GEN_GAP", "13"))
        n    = int(os.environ.get("GEN_N", "256"))
        NB   = int(os.environ.get("GEN_BEATS", "8"))    # board AxLEN=8
        oslim = int(os.environ.get("GEN_OS", "8"))
        bpw  = DW // 8
        stride = NB * bpw                 # contiguous march == FAM_INCREMENTAL
        span = n * stride
        wr_base = BASE
        rd_base = BASE + max(4 * 0x2000, span + 0x2000)

        for k in range(n):
            for ki in range(NB):
                tb.preload_memory(rd_base + (k * NB + ki) * bpw,
                                  payload(4, k * NB + ki).to_bytes(bpw, "little"))

        r_ch = tb.axi_master_rd.r_channel
        normal_policy = getattr(r_ch, "ready_policy", "valid_first")
        rd_results: list = []
        stalls = {"n": 0}

        async def _gap_pause():
            """S_GAP: ARs stop AND RREADY drops, for `gap` cycles."""
            r_ch.ready_policy = "stall"
            stalls["n"] += 1
            await ClockCycles(dut.aclk, gap)
            r_ch.ready_policy = normal_policy

        async def _reader():
            k, pending = 0, []
            while len(rd_results) < n:
                while k < n and len(pending) < oslim:
                    # id= NOT axid=. read_transaction() reads the ID from
                    # transaction_kwargs['id']; an axid= kwarg is silently
                    # swallowed and every read goes out as ID 0. With several
                    # in flight they then share one per-ID response deque and
                    # each coroutine picks up whichever burst finished first --
                    # which showed up as reads returning a neighbouring burst's
                    # data at EVERY gap, gap 0 included. (The sequence API used
                    # by concurrent_rw does spell it axid; these are different
                    # interfaces that look alike.)
                    t = cocotb.start_soon(tb.axi_master_rd.read_transaction(
                        rd_base + k * stride, burst_len=NB, id=k & 0xF))
                    pending.append((k, t))
                    k += 1
                kk, t = pending.pop(0)
                data = await t
                rd_results.append((rd_base + kk * stride, list(data or [])))
                if gap:
                    await _gap_pause()

        async def _writer():
            # SERIALISED on purpose. AXI4 forbids W-channel interleaving, so
            # firing several write_transaction() coroutines at once makes their
            # W beats interleave -- an illegal stream the slave cannot match to
            # its AWs. That showed up as "W_Master TIMEOUT waiting for ready"
            # plus "timeout waiting for B response", and it corrupted the run so
            # thoroughly that ALL FOUR gaps failed at the same address, gap 0
            # included, which silicon passes. The hardware writer keeps W in AW
            # order too; one burst at a time is the faithful model here, and
            # write outstanding is not what this test is probing.
            for k in range(n):
                d = [payload(0, k * NB + ki) for ki in range(NB)]
                await tb.axi_master_wr.write_transaction(
                    wr_base + k * stride, d, id=0)
                if gap:
                    await ClockCycles(dut.aclk, gap)

        # GEN_NOWRITER=1 runs the reader ALONE. On the board that control is
        # what separates "concurrent hazard" from "the reader/checker is wrong":
        # reader-alone is clean at every gap there. If it is dirty HERE, the
        # fault is in this test's addressing or preload, not in the DUT.
        dq_stop, dq_hits = [False], []
        dq_mon = cocotb.start_soon(_dq_collision_monitor(dut, dq_stop, dq_hits))

        no_wr = os.environ.get("GEN_NOWRITER", "0") == "1"
        wt = None if no_wr else cocotb.start_soon(_writer())
        rt = cocotb.start_soon(_reader())
        if wt is not None:
            await wt
        await rt
        await ClockCycles(dut.aclk, 400)

        dq_stop[0] = True
        await ClockCycles(dut.aclk, 2)
        dq_mon.kill()

        # Anti-vacuity FIRST: a run that returned nothing, or never actually
        # entered the gap state, proves nothing about the gap.
        want_beats = n * NB
        got_beats = sum(len(b) for _a, b in rd_results)
        assert len(rd_results) == n, (
            f"gen_replica gap={gap}: {len(rd_results)} bursts returned of {n}")
        assert got_beats == want_beats, (
            f"gen_replica gap={gap}: {got_beats} beats compared, want "
            f"{want_beats} -- the check would have been vacuous")
        if gap:
            assert stalls["n"] >= n // 2, (
                f"gen_replica gap={gap}: only {stalls['n']} RREADY stalls for "
                f"{n} bursts -- the S_GAP backpressure this test exists to "
                f"reproduce did not happen")

        bad_rd = [(a + ki * bpw, v & _mask(), _golden_beat(tb, a + ki * bpw))
                  for a, beats in rd_results
                  for ki, v in enumerate(beats)
                  if (v & _mask()) != _golden_beat(tb, a + ki * bpw)]
        assert not bad_rd, (
            f"gen_replica gap={gap}: {len(bad_rd)} read beat(s) != golden "
            f"(first @{bad_rd[0][0]:#x} got {bad_rd[0][1]:#x} want "
            f"{bad_rd[0][2]:#x}) -- {stalls['n']} RREADY stalls applied")
        # The DQ-collision check. Reported with a COUNT so "no collisions" is a
        # measurement and not the monitor having silently failed to run.
        tb.log.info(f"gen_replica gap={gap}: DQ overlap cycles = {len(dq_hits)}")
        # OFF by default, deliberately. Measured 2026-09-15: this fires with a
        # count of 1 even at gap 0, which the BOARD passes cleanly -- so a
        # single overlap is evidently not sufficient to corrupt, and turning
        # this on now would fail a configuration that works on silicon. The
        # board's damage comes from 49 overlaps at a 42-cycle cadence (see
        # reports/ila_pumice037_wrdata_into_read.csv). Turn it on to verify a
        # fix drives the count to zero; until then the count is logged, not
        # asserted, so the number is visible without manufacturing a failure.
        if os.environ.get("GEN_DQ_STRICT", "0") == "1":
            assert not dq_hits, (
                f"gen_replica gap={gap}: {len(dq_hits)} cycle(s) drove WRITE "
                f"data while a READ was still returning -- the PUMICE-037 "
                f"mechanism (first at {dq_hits[0][0]}ns: wrdata_en={dq_hits[0][1]:#x} "
                f"rddata_en={dq_hits[0][2]:#x} rddata_valid={dq_hits[0][3]:#x}). "
                f"Legal on DFI's separate buses; destructive on the PHY's "
                f"shared DQ.")

        tb.log.info(f"PASS gen_replica: gap={gap} n={n} beats/burst={NB} "
                    f"os={oslim} span={span}B ({span/2048:.1f} pages) "
                    f"{stalls['n']} RREADY stalls")
        return

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
        k = {"gate": 6, "basic": 6, "func": 16, "medium": 16, "full": 32}.get(level, 6)
        row_base = BASE + row * 0x10000 + bank * 0x2000
        addrs = [row_base + c * (BL_WORDS * (DW // 8)) for c in range(k)]
        wr, rd, exp = build_addr_pattern_sequences(
            burst_len=BL_WORDS, data_width=DW, addresses=addrs)
        await _wr_rd_check(tb, wr, rd)
        tb.log.info("PASS row_hit_pattern: walking-column hits (BFM) vs golden")
        return

    # ---- workload mix (varied banks/rows) ----
    if test_type in ("workload_mix", "workload_mix_lpddr2"):
        n = {"gate": 12, "basic": 12, "func": 32, "medium": 32, "full": 64}.get(level, 12)
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
        await tb.csr_write_field("SCHED_POLICY", "order_mode", 0x0)   # FR-FCFS
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
        n = {"gate": 8, "basic": 8, "func": 20, "medium": 20, "full": 40}.get(level, 8)
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
              "DRAM_BEAT_WIDTH": "64", "DRAM_BL": "8",
              "NUM_ENTRIES": "8", "N_SRAM_SLOTS": "8"}
    if params_over:
        params.update(params_over)
    # Share one compiled sim across all tests with identical RTL params (the
    # cocotb testcase is selected at runtime), so the full suite compiles ~twice
    # (nr1 + nr2) instead of once per test — the run is otherwise recompile-bound.
    #
    # PUMICE-019: sharing is only safe WITHIN one process. cocotb_test's
    # Verilator path re-runs `verilator -cc` + make UNCONDITIONALLY on every
    # run() call (no staleness check), so two processes in one sim_build
    # regenerate the sources under each other's compiles/sims and destroy the
    # artifacts (the 48/31-spurious-FAIL clean-parallel tallies). Under
    # pytest-xdist each WORKER runs its tests sequentially, so a per-worker
    # suffix keeps the compile-sharing win inside a worker while removing all
    # cross-process sharing. ccache absorbs the duplicate C++ compiles.
    _worker = os.environ.get("PYTEST_XDIST_WORKER", "")
    # The build key MUST carry every RTL parameter that changes the netlist.
    # It used to be NUM_RANKS alone, which was fine while geometry was fixed --
    # but a BL4 test sharing a key with the BL8 suite recompiles the shared
    # sim_build out from under it, and the tests that ran before it silently
    # became tests of a different DUT. Geometry is a parameter now, so it goes
    # in the key.
    build_key = ("nr" + params["NUM_RANKS"]
                 + "_r" + params["DFI_RATE"]
                 + "_b" + params["DRAM_BEAT_WIDTH"]
                 + "_bl" + params["DRAM_BL"]
                 + (f"_{_worker}" if _worker else ""))
    sim_build = sim_build_path(tests_dir, "shared_" + build_key)
    os.makedirs(sim_build, exist_ok=True)
    # PUMICE-019: echo the per-test seed. pytest shows captured stdout for
    # FAILING tests, so a one-off red is reproducible with PUMICE_SEED=<n>
    # even after logs/ are cleaned.
    seed = os.environ.get("PUMICE_SEED", str(random.randint(0, 100000)))
    print(f"[seed] {tag} PUMICE_SEED={seed}")
    env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{tag}.log"),
           "COCOTB_LOG_LEVEL": "INFO",
           "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
           "SEED": seed,
           "TEST_LEVEL": _LEVEL,
           "DFI_RATE": params["DFI_RATE"], "DRAM_BEAT_WIDTH": params["DRAM_BEAT_WIDTH"],
           "DRAM_BL": params["DRAM_BL"], "NUM_RANKS": params["NUM_RANKS"]}
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


# ---- PUMICE-037: concurrent read + write, reader paced ---------------------
# Geometry is a PARAMETER, not an env override. The board is BL4 on an x16
# device (one DRAM burst = one AXI beat); the historical sim point is BL8 with
# device == beat (one burst = four beats). PUMICE-028's whole point is that the
# board shape was reachable in principle and never actually run, so both shapes
# run here and the board one is not opt-in.
#
# Gaps straddle the silicon edge: 0 and 4 are clean on the board, 8 and 15 are
# not. Keeping the clean side in the matrix is what separates "reproduced the
# defect" from "the test is broken".
# DFI read latency is the third board-faithful axis and it matters more than
# it looks. The default DFISlavePHY returns read data 2 cycles after the
# command, which is close enough to a loopback that same-bank overlap never
# builds up -- that is precisely how the per-entry arbiter bug stayed hidden
# until the open_page test drove real a7ddrphy latency. The board's bring-up
# tuple is rden 6 / rddata_delay 7, so 7 is the silicon-faithful point.
# Refresh is the last board-faithful axis, and the one with a standing
# suspicion attached: the bring-up notes record the residual on-silicon
# corruption as a possible refresh collision. The default t_refi here is far
# enough apart that a short run may see no refresh at all, so the tight point
# forces refreshes INTO the concurrent traffic rather than around it.
# Reads IN FLIGHT when the gap lands. At depth 1 the pipe is empty across every
# gap, so nothing can be in flight over it -- the board's generators run up to
# 32 outstanding AND pace, which is a different machine state entirely and the
# one the S_GAP / stray-beat path would bite. The BFM engine runner queues ARs
# back-to-back with no per-burst response wait, so this is the board's shape
# rather than an approximation of it.
@pytest.mark.parametrize("depth", [1, 32], ids=["depth1", "depth32_board"])
@pytest.mark.parametrize("trefi", [0x400, 0x40], ids=["refi_default", "refi_tight"])
@pytest.mark.parametrize("rdlat", [2, 7], ids=["rdlat2", "rdlat7_board"])
@pytest.mark.parametrize("geom", ["bl4x16", "bl8"])
@pytest.mark.parametrize("rd_gap", [0, 4, 8, 15])
def test_pumice_top_concurrent_rw(request, geom, rd_gap, rdlat, trefi, depth):
    """Read and write in flight together, reader pacing itself between bursts.

    The board returns wrong data and corrupts cells whenever the reader's gap
    is 8 or above; gap 0..7 is clean. This drives the same shape straight at
    pumice_top, with the golden MemoryModel checking BOTH symptoms separately:
    read beats against golden (bad data) and written cells against what was
    written (corruption).
    """
    params, env = _geom_params(geom)
    _run(request, "cocotb_test_pumice_top",
         extra_env={"TEST_TYPE": "concurrent_rw", "MEM_TYPE": "DDR2",
                    "RD_GAP": str(rd_gap), "DFI_READ_LATENCY": str(rdlat),
                    "T_REFI": str(trefi), "RD_DEPTH": str(depth), **env},
         params_over=params)


@pytest.mark.parametrize("test_type", _FUNC)
def test_pumice_top(request, test_type):
    mem = "LPDDR2" if test_type.endswith("lpddr2") else "DDR2"
    _run(request, "cocotb_test_pumice_top",
         extra_env={"TEST_TYPE": test_type, "MEM_TYPE": mem})

# Every legal AxLEN must work -- a compliant master may issue any of these, and
# a CPU storing one word issues AxLEN=0 routinely. 1 and 2 beats get the full
# treatment because they are the sub-DRAM-burst cases the padding exists for
# (at BL_WORDS=4 they are entirely filler-completed); 3 is the remaining
# sub-burst length; 4 is the exactly-aligned case; 5 and 7 are ragged
# multi-burst (a whole burst plus a remainder); 8 and 16 are whole multiples.
# Together they cover under / exact / over / ragged without a 256-wide sweep.
_BURST_LENS = [1, 2, 3, 4, 5, 7, 8, 16]


@pytest.mark.parametrize("blen", _BURST_LENS)
def test_pumice_top_burst_len(request, blen):
    _run(request, "cocotb_test_pumice_top",
         extra_env={"TEST_TYPE": "burst_len", "MEM_TYPE": "DDR2",
                    "BURST_LEN": str(blen)})

# Partial-WSTRB suite: every strobe shape x short burst lengths. `none` (all
# lanes masked) is legal AXI and must be a no-op, not a zero-fill; `all` is the
# control that must behave exactly like an ordinary write.
@pytest.mark.parametrize("blen", [1, 2, 4])
@pytest.mark.parametrize("pattern", [p for p, _ in _STRB_PATTERNS])
def test_pumice_top_partial_strb(request, pattern, blen):
    _run(request, "cocotb_test_pumice_top_partial_strb",
         extra_env={"STRB_PATTERN": pattern, "BURST_LEN": str(blen),
                    "MEM_TYPE": "DDR2"})

# Sub-burst READS: every length 1..BL_WORDS crossed with every start offset in
# the DRAM burst. offset+len is clamped in the test body to stay inside one
# burst, so each case is a pure "partial read of one DRAM burst".
@pytest.mark.parametrize("offset", [0, 1, 2, 3])
@pytest.mark.parametrize("nbeats", [1, 2, 3, 4])
def test_pumice_top_partial_rd(request, nbeats, offset):
    _run(request, "cocotb_test_pumice_top_partial_rd",
         extra_env={"RD_BEATS": str(nbeats), "RD_OFFSET": str(offset),
                    "MEM_TYPE": "DDR2"})





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


@pytest.mark.parametrize("gap", [0, 8, 13, 15])
def test_pumice_top_gen_replica(request, gap):
    """Board geometry + the hardware generators' EXACT pacing, including the
    S_GAP RREADY backpressure that the concurrent_rw model cannot express."""
    params, env = _geom_params("bl4x16")
    _run(request, "cocotb_test_pumice_top",
         extra_env={"TEST_TYPE": "gen_replica", "MEM_TYPE": "DDR2",
                    "GEN_GAP": str(gap),
                    "GEN_N": os.environ.get("GEN_N", "256"),
                    "GEN_BEATS": os.environ.get("GEN_BEATS", "8"),
                    "GEN_OS": os.environ.get("GEN_OS", "8"),
                    # Board tuple: read latency 7, deep return ring.
                    "DFI_READ_LATENCY": "7", "RD_DEPTH": "8",
                    # DFI read model. The default here is the IDEALISED
                    # loopback, which returns data with no PHY pipeline at all
                    # -- so a read/write turnaround hazard cannot appear in it
                    # no matter how faithfully the generators are replicated.
                    # DFI_PROFILE=a7ddrphy anchors the data to the READ COMMAND
                    # at read_latency like the board's PHY.
                    "DFI_PROFILE": os.environ.get("DFI_PROFILE", "ideal"),
                    **env},
         params_over=params)
