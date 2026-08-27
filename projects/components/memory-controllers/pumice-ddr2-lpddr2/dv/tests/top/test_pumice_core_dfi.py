# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Coverage suite for `pumice_core` against the STRICT DFISlavePHY + MemoryModel.

The DFISlavePHY decodes the DFI command bus, writes captured dfi_wrdata into a
golden MemoryModel, and returns MemoryModel contents on reads (per JEDEC latency).
So an AXI write-then-read to the same address is checked against a real DRAM
model — the bar that catches per-phase timing bugs, not a loopback.

Scenarios (all golden-checked):
  * multi-burst, multi-bank / multi-row writes then reads
  * interleaved banks (open-page + ACT/PRE exercised by the scheduler)
  * R-channel backpressure
"""

import os
import sys
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles

from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "dv/tb/pumice_core_tb_top.f")

NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 14, 10
DFI_RATE, DRAM_BEAT = 2, 64
DW = DRAM_BEAT * DFI_RATE          # 128
SW = DW // 8
BL = 8
BL_WORDS = BL // DFI_RATE          # 4 AXI beats / burst
BURST_INCR = 1


def _cfg(dut, page_policy=0):
    dut.memtype_i.value = 0
    dut.page_policy_i.value = page_policy
    dut.bank_lsb_i.value  = 10   # ROW_MAJOR
    dut.hash_en_i.value   = 0
    dut.hash_seed_i.value = 0
    for t, v in [("t_rcd_i", 3), ("t_rp_i", 3), ("t_ras_i", 4), ("t_rc_i", 6),
                 ("t_wr_i", 3), ("t_rtp_i", 2), ("t_faw_i", 6), ("t_rrd_i", 2),
                 ("t_wtr_i", 2), ("t_rtw_i", 2), ("t_ccd_i", 1)]:
        getattr(dut, t).value = v
    dut.t_refi_i.value = 0x0400          # periodic refresh during the run
    dut.t_rfc_i.value = 8
    dut.refresh_burst_i.value = 1
    for t in ("t_init_wait_i", "t_dll_wait_i"):
        getattr(dut, t).value = 0
    for t in ("t_mrd_wait_i", "t_rp_wait_i", "t_rfc_wait_i"):
        getattr(dut, t).value = 0
    dut.rd_phase_i.value = 0
    dut.wr_phase_i.value = 0
    dut.t_phy_wrlat_i.value = 1
    dut.t_rddata_en_i.value = 2
    for s in ("awid", "awaddr", "awlen", "awsize", "awburst", "awlock", "awcache",
              "awprot", "awqos", "awregion", "awuser", "awvalid",
              "wdata", "wstrb", "wlast", "wuser", "wvalid",
              "arid", "araddr", "arlen", "arsize", "arburst", "arlock", "arcache",
              "arprot", "arqos", "arregion", "aruser", "arvalid"):
        getattr(dut, f"s_axi_{s}").value = 0
    dut.s_axi_awburst.value = BURST_INCR
    dut.s_axi_arburst.value = BURST_INCR
    dut.s_axi_bready.value = 1
    dut.s_axi_rready.value = 1


def _mkaddr(bank, row, col):
    # {row|bank|col} << byte_offset(=log2(DRAM beat bytes)=3)
    return ((row << (COL_WIDTH + 3)) | (bank << COL_WIDTH) | col) << 3


async def _bring_up(dut, page_policy=0):
    """clocks + reset + config + strict DFISlavePHY(golden) + init -> returns memory."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, 4, units="ns").start())
    _cfg(dut, page_policy)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    await ClockCycles(dut.aclk, 10)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    await ClockCycles(dut.aclk, 6)

    mapping = AddressMapping(num_ranks=1, num_banks=NUM_BANKS,
                             num_rows=1 << ROW_WIDTH, num_cols=1 << COL_WIDTH,
                             mapping="row|bank|col")
    memory = MemoryModel(num_lines=NUM_BANKS * (1 << ROW_WIDTH) * (1 << COL_WIDTH),
                         bytes_per_line=DRAM_BEAT // 8, log=dut._log)
    base = DFIBase(dfi_version=DFIVersion.V2_1, memory_type=MemoryType.DDR2,
                   timings=builtin_timings("ddr2-650-mt47h64m16hr"),
                   mapping=mapping, beats_per_burst=BL)
    slave = DFISlavePHY(dut, dut.dfi_clk, base=base, memory=memory,
                        dfi_phase_bytes=DRAM_BEAT // 8)
    slave.dram = DramStateModel(timings=base.timings, num_banks=NUM_BANKS,
                                policy=ViolationPolicy(hard=frozenset()))

    async def _drive_init():
        for _ in range(2000):
            await RisingEdge(dut.dfi_clk)
            try:
                st = int(dut.phy_dfi_init_start.value)
            except Exception:
                st = 1
            if st:
                await ClockCycles(dut.dfi_clk, 4)
                dut.phy_dfi_init_complete.value = 1
                return
    dut.phy_dfi_init_complete.value = 0
    cocotb.start_soon(_drive_init())
    for _ in range(600):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"
    return memory, slave


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_pumice_core_dfi(dut):
    await _bring_up(dut, page_policy=0)   # OPEN

    rng = random.Random(int(os.environ.get("SEED", "1")))
    level = os.environ.get("TEST_LEVEL", "basic").lower()
    n = {"basic": 6, "medium": 20, "full": 48}.get(level, 6)

    # distinct addresses across banks/rows; BL-word aligned
    seen = set()
    reqs = []
    while len(reqs) < n:
        bank = rng.randint(0, NUM_BANKS - 1)
        row = rng.randint(0, 63)
        col = rng.randint(0, 63) * BL   # BL-aligned column
        # addr = {row|bank|col} << byte_offset ; byte offset = log2(DRAM beat bytes)=3
        word = (row << (COL_WIDTH + 3)) | (bank << COL_WIDTH) | col
        addr = word << 3
        if addr in seen:
            continue
        seen.add(addr)
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        reqs.append((addr, data))

    # ---- write phase ----
    for k, (addr, data) in enumerate(reqs):
        await _aw(dut, addr, k & 0xF)
        await _w(dut, data)
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                break

    # ---- read phase (R backpressure on the odd reads) ----
    for k, (addr, data) in enumerate(reqs):
        got = []
        bp = (k % 2 == 1)
        cocotb.start_soon(_r_sink(dut, got, throttle=bp))
        await _ar(dut, addr, k & 0xF)
        for _ in range(800):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == data, (
            f"read {k} @ {addr:#x} mismatch:\n  got {[hex(x) for x in got[:BL_WORDS]]}"
            f"\n  exp {[hex(x) for x in data]}")

    dut._log.info(f"PASS: {n} bursts written+read-back vs DFISlavePHY golden "
                  f"(multi-bank, refresh active, R backpressure)")


async def _r_sink(dut, out, throttle=False):
    import random as _r
    while len(out) < BL_WORDS:
        if throttle:
            dut.s_axi_rready.value = 0
            await ClockCycles(dut.aclk, 2)
            dut.s_axi_rready.value = 1
        await RisingEdge(dut.aclk)
        if int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value):
            out.append(int(dut.s_axi_rdata.value) & ((1 << DW) - 1))
    dut.s_axi_rready.value = 1


async def _aw(dut, addr, wid):
    dut.s_axi_awid.value = wid
    dut.s_axi_awaddr.value = addr
    dut.s_axi_awlen.value = BL_WORDS - 1
    dut.s_axi_awvalid.value = 1
    await RisingEdge(dut.aclk)
    while int(dut.s_axi_awready.value) == 0:
        await RisingEdge(dut.aclk)
    dut.s_axi_awvalid.value = 0


async def _w(dut, data):
    for i, d in enumerate(data):
        dut.s_axi_wdata.value = d
        dut.s_axi_wstrb.value = (1 << SW) - 1
        dut.s_axi_wlast.value = 1 if i == len(data) - 1 else 0
        dut.s_axi_wvalid.value = 1
        await RisingEdge(dut.aclk)
        while int(dut.s_axi_wready.value) == 0:
            await RisingEdge(dut.aclk)
    dut.s_axi_wvalid.value = 0
    dut.s_axi_wlast.value = 0


async def _ar(dut, addr, rid):
    dut.s_axi_arid.value = rid
    dut.s_axi_araddr.value = addr
    dut.s_axi_arlen.value = BL_WORDS - 1
    dut.s_axi_arvalid.value = 1
    await RisingEdge(dut.aclk)
    while int(dut.s_axi_arready.value) == 0:
        await RisingEdge(dut.aclk)
    dut.s_axi_arvalid.value = 0


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_pumice_core_close(dut):
    """CLOSE page policy: every column op is auto-precharge (RDA/WRA)."""
    await _bring_up(dut, page_policy=1)   # CLOSE
    rng = random.Random(int(os.environ.get("SEED", "2")))
    n = {"basic": 6, "medium": 16, "full": 32}.get(os.environ.get("TEST_LEVEL", "basic").lower(), 6)
    seen, reqs = set(), []
    while len(reqs) < n:
        a = _mkaddr(rng.randint(0, NUM_BANKS - 1), rng.randint(0, 63), rng.randint(0, 63) * BL)
        if a in seen:
            continue
        seen.add(a)
        reqs.append((a, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]))
    for k, (addr, data) in enumerate(reqs):
        await _aw(dut, addr, k & 0xF); await _w(dut, data)
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                break
    for k, (addr, data) in enumerate(reqs):
        got = []
        cocotb.start_soon(_r_sink(dut, got))
        await _ar(dut, addr, k & 0xF)
        for _ in range(800):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == data, f"CLOSE read {k} @ {addr:#x}: {got[:BL_WORDS]} != {data}"
    dut._log.info(f"PASS: CLOSE policy (auto-precharge) — {n} bursts round-trip vs golden")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_refresh_collide(dut):
    """Directed refresh-vs-read collision (TASK-SCHED-REFRESH).

    CLOSE policy (each read = ACT + RDA) + sustained SAME-bank page-hit reads +
    a SMALL tREFI so a refresh lands between a read's ACT and its RDA. Two checks
    fire on the bug (data-checking rule — never sequencing alone):
      * the standalone command-history scoreboard (u_cmd_history) asserts on the
        SEQUENCING violation (REFab granted while a bank row is still OPEN);
      * the golden compare below asserts on the corrupted DATA (the read that
        followed the refresh returns garbage).
    Expected RED on current RTL, GREEN after the arbiter refresh-sequencing fix.
    """
    _memory, slave = await _bring_up(dut, page_policy=1)  # CLOSE / auto-precharge
    dut.t_refi_i.value = 0x30                         # frequent refresh
    dut.t_rfc_i.value = 8
    BANK, ROW, N = 3, 5, 64

    exp = []
    for k in range(N):
        addr = _mkaddr(BANK, ROW, k * BL)
        data = [((k << 16) | (0xAB0 + i)) & ((1 << DW) - 1) for i in range(BL_WORDS)]
        exp.append((addr, data))
        await _aw(dut, addr, k & 0xF)
        await _w(dut, data)
    await ClockCycles(dut.aclk, 500)                 # drain writes into golden

    got = []
    async def _collect():
        cur = []
        while len(got) < N:
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value):
                cur.append(int(dut.s_axi_rdata.value) & ((1 << DW) - 1))
                if int(dut.s_axi_rlast.value):
                    got.append(cur); cur = []
    dut.s_axi_rready.value = 1
    cocotb.start_soon(_collect())

    for k in range(N):                               # sustained same-bank reads
        await _ar(dut, exp[k][0], k & 0xF)
    for _ in range(6000):
        if len(got) >= N:
            break
        await RisingEdge(dut.aclk)

    bad = 0
    for k, (addr, data) in enumerate(exp):
        if k >= len(got) or got[k][:BL_WORDS] != data:
            g = [hex(x) for x in got[k][:BL_WORDS]] if k < len(got) else "MISSING"
            dut._log.info(f"read {k} @ {addr:#x}: {g} != {[hex(x) for x in data]}")
            bad += 1
    assert bad == 0, (f"refresh collided with {bad}/{N} same-bank reads "
                      f"(golden data mismatch) — see CMD_HISTORY assertions for the "
                      f"REFab-while-row-open sequencing violation")

    # ANTI-VACUITY: this test is only a refresh-collision test if refreshes
    # actually happened during the traffic. The DFI slave decodes every REF
    # off the wire; zero REFs means the scenario never armed (dead t_refi
    # poke, gated refresh_ctrl, ...) and a green result proves nothing.
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC
    n_ref = slave.cmd_counts.get(_DC.REF, 0)
    dut._log.info(f"refresh_collide: DFI slave decoded {n_ref} REF commands")
    assert n_ref > 0, ("VACUOUS: zero REF commands reached the DFI during the "
                       "run — tREFI poke dead or refresh gated; the collision "
                       "scenario never armed")
    dut._log.info(f"PASS: {N} same-bank reads clean across {n_ref} refreshes (no collision)")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_fixed_open(dut):
    """PUMICE-006 Axis 2: fixed_open + adapt_time idle-timeout page close.

    Self-checking in BOTH directions so the feature cannot pass vacuously:

      arm A (mode OFF, red guard): OPEN policy, traffic to one bank, then a
        long idle. The row must STAY open -- zero PREs during idle. If the
        timeout engine ever leaks closes into mode 0, this arm fails.
      arm B (fixed_open): same traffic, short tr_init. The row MUST close
        during idle (PRE observed at the DFI with no demand present), and a
        subsequent same-row read must reopen (new ACT) and return golden data.
      arm C (adapt_time smoke): mode 4 with TR bounds behaves like a timeout
        close at tr_init and data stays golden (the adaptive TR walk gets its
        own directed test when its tuning matters; here it must not wedge).
    """
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC
    _memory, slave = await _bring_up(dut, page_policy=0)   # OPEN

    BANK, ROW = 2, 7
    rng = random.Random(int(os.environ.get("SEED", "5")))

    async def _wr_rd_one(col, rid):
        addr = _mkaddr(BANK, ROW, col * BL)
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        await _aw(dut, addr, rid & 0xF)
        await _w(dut, data)
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                break
        got = []
        cocotb.start_soon(_r_sink(dut, got))
        await _ar(dut, addr, rid & 0xF)
        for _ in range(800):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == data, f"data mismatch @ col {col}"

    async def _idle_pre_count(cycles):
        before = slave.cmd_counts.get(_DC.PRE, 0)
        await ClockCycles(dut.aclk, cycles)
        return slave.cmd_counts.get(_DC.PRE, 0) - before

    # ---- arm A: mode OFF -- the row must stay open across idle -------------
    dut.page_mode_i.value = 0
    await _wr_rd_one(0, 0)
    pres = await _idle_pre_count(300)
    assert pres == 0, (f"mode 0 leaked {pres} idle PRE(s) -- the timeout "
                       f"engine must be inert at the default encoding")

    # ---- arm B: fixed_open -- idle timeout closes the row ------------------
    dut.page_mode_i.value = 3          # fixed_open
    dut.page_tr_init_i.value = 16      # short idle fuse
    await _wr_rd_one(1, 1)
    pres = await _idle_pre_count(300)
    assert pres >= 1, ("fixed_open: row never closed during idle -- timeout "
                       "PRE did not issue")
    acts_before = slave.cmd_counts.get(_DC.ACT, 0)
    await _wr_rd_one(2, 2)             # same row again: must reopen + be clean
    assert slave.cmd_counts.get(_DC.ACT, 0) > acts_before, (
        "reopen after timeout close did not ACT -- row state inconsistent")

    # ---- arm C: adapt_time smoke -------------------------------------------
    dut.page_mode_i.value = 4          # adapt_time
    dut.page_tr_min_i.value = 8
    dut.page_tr_max_i.value = 64
    dut.page_tr_step_i.value = 4
    dut.page_mc_high_i.value = 2
    dut.page_mc_low_i.value = 1
    dut.page_mc_init_i.value = 0
    dut.page_check_ivl_i.value = 128
    await _wr_rd_one(3, 3)
    pres = await _idle_pre_count(300)
    assert pres >= 1, "adapt_time: no timeout close at TR=tr_init"
    await _wr_rd_one(4, 4)             # still coherent after adaptive close

    # ---- teardown: mode off, confirm inertness returns ---------------------
    dut.page_mode_i.value = 0
    await _wr_rd_one(5, 5)
    pres = await _idle_pre_count(300)
    assert pres == 0, "mode 0 after modes 3/4: timeout engine failed to disarm"
    dut._log.info("PASS fixed_open/adapt_time: inert at 0, closes on idle "
                  "timeout, clean reopen, disarms")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_rbl(dut):
    """PUMICE-006 Axis 2: rbl_static / rbl_dyn -- RBLA miss-counter table.

    A thrashing pattern (alternating rows A/B in ONE bank) makes every access
    a row-buffer miss. Under OPEN (mode 0) each turn needs a conflict PRE +
    ACT: PREs ~= turns. Under rbl_static, once a row's miss counter crosses
    the threshold its columns auto-precharge, so the explicit-PRE path goes
    quiet while ACT-per-turn continues. The contrast is the assertion:

      arm A (mode 0 baseline): thrash N turns -> count PREs (expect ~N).
      arm B (rbl_static, thresh=2): warm 4 turns, then thrash N turns ->
        PREs must be < half the arm-A count, data golden throughout, and a
        FRIENDLY row (a different bank, repeated hits) must stay open --
        zero ACTs between its consecutive accesses.
      arm C (rbl_dyn smoke): mode 7 with a short epoch; integrity holds and
        the mode disarms cleanly (threshold adaptation quality gets its own
        characterization on the board profiles).
    """
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC
    _memory, slave = await _bring_up(dut, page_policy=0)   # OPEN base

    BANK, ROW_A, ROW_B = 3, 5, 9
    FR_BANK, FR_ROW = 6, 4                      # friendly-row control
    rng = random.Random(int(os.environ.get("SEED", "7")))

    async def _one(bank, row, col, rid):
        addr = _mkaddr(bank, row, col * BL)
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        await _aw(dut, addr, rid & 0xF)
        await _w(dut, data)
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                break
        got = []
        cocotb.start_soon(_r_sink(dut, got))
        await _ar(dut, addr, rid & 0xF)
        for _ in range(800):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == data, f"data mismatch bank{bank} row{row}"

    async def _thrash(n, col0):
        before = slave.cmd_counts.get(_DC.PRE, 0)
        for t in range(n):
            await _one(BANK, ROW_A if (t & 1) == 0 else ROW_B, col0 + t, t)
        return slave.cmd_counts.get(_DC.PRE, 0) - before

    N = 12

    # ---- arm A: OPEN baseline -- thrash costs a PRE per turn ---------------
    dut.page_mode_i.value = 0
    pres_open = await _thrash(N, 0)
    assert pres_open >= N - 2, (f"baseline thrash produced only {pres_open} "
                                f"PREs for {N} turns -- pattern not thrashing")

    # ---- arm B: rbl_static -----------------------------------------------
    dut.page_mode_i.value = 6
    dut.page_rbl_thresh_i.value = 2
    dut.page_rbl_ivl_i.value = 0                # no epochs: evidence persists
    _ = await _thrash(4, 32)                    # warm the miss counters
    pres_rbl = await _thrash(N, 48)
    assert pres_rbl < pres_open // 2, (
        f"rbl_static did not suppress conflict PREs: {pres_rbl} vs baseline "
        f"{pres_open} -- low-locality rows are not auto-precharging")

    # friendly row: repeated hits in another bank must NOT be closed.
    await _one(FR_BANK, FR_ROW, 0, 8)           # opens the row (1 ACT)
    acts_before = slave.cmd_counts.get(_DC.ACT, 0)
    for k in range(4):
        await _one(FR_BANK, FR_ROW, 1 + k, 9 + k)
    acts_delta = slave.cmd_counts.get(_DC.ACT, 0) - acts_before
    assert acts_delta == 0, (
        f"friendly row re-activated {acts_delta}x under rbl -- a hit-served "
        f"row accumulated miss evidence it should not have")

    # ---- arm C: rbl_dyn smoke ---------------------------------------------
    dut.page_mode_i.value = 7
    dut.page_rbl_ivl_i.value = 256              # epochs on for the hill-climb
    _ = await _thrash(8, 96)
    dut.page_mode_i.value = 0
    pres_off = await _thrash(4, 120)
    assert pres_off >= 2, "mode 0 after rbl: auto-precharge failed to disarm"
    dut._log.info(f"PASS rbl: baseline {pres_open} PREs/{N} turns, "
                  f"rbl_static {pres_rbl}, friendly row stayed open, dyn+disarm ok")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_acc(dut):
    """PUMICE-006 Axis 2: adapt_access (mode 5) -- per-row 2-bit predictor.

    Happy's Hybrid counts ACCESSES PER ACTIVATION, so the thrash arm must be
    single-access: one write burst per activation, alternating two rows in one
    bank. Each conflict close then teaches "1 access -> close-friendly"
    (2'b01 -> 2'b10), and the next visit auto-precharges. NOTE this differs
    from the rbl test's thrash: a write+read pair is 2 accesses and would
    (correctly) teach the predictor to keep the row OPEN.

      arm A (mode 0 baseline): N single-write thrash turns -> PREs ~= N.
      arm B (adapt_access): warm 4 turns (one taught close per row), then N
        turns -> PREs < half of baseline; the written data reads back golden
        afterwards; and a FRIENDLY row (write+read pairs = reuse) in another
        bank stays open -- zero ACTs between consecutive accesses.
      arm C (disarm): back to mode 0 -> thrash costs PREs again (mask released
        and the table dropped).
    """
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC
    _memory, slave = await _bring_up(dut, page_policy=0)   # OPEN base

    BANK, ROW_A, ROW_B = 4, 6, 11
    FR_BANK, FR_ROW = 1, 3                      # friendly-row control
    rng = random.Random(int(os.environ.get("SEED", "9")))
    written = {}                                # addr -> data, for readback

    async def _wr_one(bank, row, col, rid):
        addr = _mkaddr(bank, row, col * BL)
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        written[addr] = data
        await _aw(dut, addr, rid & 0xF)
        await _w(dut, data)
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                break

    async def _rd_check(addr, rid):
        got = []
        cocotb.start_soon(_r_sink(dut, got))
        await _ar(dut, addr, rid & 0xF)
        for _ in range(800):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == written[addr], f"data mismatch @ {addr:#x}"

    async def _thrash(n, col0):
        before = slave.cmd_counts.get(_DC.PRE, 0)
        for t in range(n):
            await _wr_one(BANK, ROW_A if (t & 1) == 0 else ROW_B, col0 + t, t)
            await ClockCycles(dut.aclk, 20)     # let the burst land + close
        return slave.cmd_counts.get(_DC.PRE, 0) - before

    N = 12

    # ---- arm A: OPEN baseline -- single-access thrash costs a PRE/turn ----
    dut.page_mode_i.value = 0
    pres_open = await _thrash(N, 0)
    assert pres_open >= N - 2, (f"baseline thrash produced only {pres_open} "
                                f"PREs for {N} turns -- pattern not thrashing")

    # ---- arm B: adapt_access ---------------------------------------------
    dut.page_mode_i.value = 5
    _ = await _thrash(4, 32)                    # teach: 1 close per row
    pres_acc = await _thrash(N, 48)
    assert pres_acc < pres_open // 2, (
        f"adapt_access did not suppress conflict PREs: {pres_acc} vs baseline "
        f"{pres_open} -- single-access rows are not auto-precharging")

    # written data must read back golden (reads also re-teach; fine, counting
    # windows are already closed).
    for addr in list(written)[-4:]:
        await _rd_check(addr, 5)

    # friendly row: write+read pairs (2 accesses/activation) in another bank
    # must stay open -- reuse teaches OPEN and the weak-open init never closes.
    await _wr_one(FR_BANK, FR_ROW, 0, 8)
    await _rd_check(_mkaddr(FR_BANK, FR_ROW, 0), 8)
    acts_before = slave.cmd_counts.get(_DC.ACT, 0)
    for k in range(3):
        await _wr_one(FR_BANK, FR_ROW, 1 + k, 9 + k)
        await _rd_check(_mkaddr(FR_BANK, FR_ROW, (1 + k) * BL), 9 + k)
    acts_delta = slave.cmd_counts.get(_DC.ACT, 0) - acts_before
    assert acts_delta == 0, (
        f"friendly row re-activated {acts_delta}x under adapt_access -- a "
        f"reuse-served row was classified close")

    # ---- arm C: ctr_init knob ---------------------------------------------
    # ctr_init=3 (strong close) is applied while the mode is off, so on entry
    # EVERY fresh row predicts close at its first ACT: a cold-table thrash
    # needs at most one conflict PRE (closing whatever the last arm left open).
    dut.page_mode_i.value = 0
    dut.page_ctr_init_i.value = 3
    await ClockCycles(dut.aclk, 4)              # table re-inits while disabled
    dut.page_mode_i.value = 5
    pres_init3 = await _thrash(4, 80)
    assert pres_init3 <= 1, (
        f"ctr_init=3 cold table still cost {pres_init3} PREs in 4 turns -- "
        f"the init knob is not reaching the predictor")
    dut.page_ctr_init_i.value = 0

    # ---- arm D: disarm ----------------------------------------------------
    dut.page_mode_i.value = 0
    pres_off = await _thrash(4, 96)
    assert pres_off >= 2, "mode 0 after adapt_access: failed to disarm"
    dut._log.info(f"PASS adapt_access: baseline {pres_open} PREs/{N} turns, "
                  f"mode-5 {pres_acc}, friendly row stayed open, "
                  f"ctr_init=3 cold-table {pres_init3} PREs, disarm ok")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_sched_order(dut):
    """PUMICE-006 Axis 1: SCHED_POLICY.order_mode integrity sweep + the
    parked-victim WEDGE sentinel.

    The pick-level semantics of in_order / age_threshold are verified in the
    fub arbiter test (hand-driven vectors — deterministic); the rd reorder
    CAM releases AXI reads in AR order BY DESIGN, so completion order at this
    level cannot show scheduling differences. What this test pins:

      * the parked-victim pattern (a same-bank CONFLICT read held in the CAM
        while row-hits stream) completes with GOLDEN data under EVERY order
        mode. Before the column-guard fix this pattern WEDGED the read path
        at default FR-FCFS: a conflict-PRE fired in a column-readiness gap,
        a column picked against the 2-cycle-stale row-open image landed on
        the closed row, its data never returned, and the AR-order drain
        blocked behind it forever (rd-return checker DROP).
      * every mode drains the full pattern (no wedge, no data loss) and the
        overlay disarms back to mode 0.
    """
    _memory, slave = await _bring_up(dut, page_policy=0)   # OPEN
    rng = random.Random(int(os.environ.get("SEED", "13")))

    BANK, ROW_H, ROW_V = 2, 3, 9
    N = 12                                   # row-hit stream length
    VICTIM_ID = 7

    # ---- preload golden data (writes; hits row H cols 0..N-1, victim row V) --
    hit_addr = [_mkaddr(BANK, ROW_H, c * BL) for c in range(N)]
    vic_addr = _mkaddr(BANK, ROW_V, 0)
    golden = {}
    for addr in hit_addr + [_mkaddr(BANK, ROW_V, 0)]:
        golden[addr] = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        await _aw(dut, addr, 0)
        await _w(dut, golden[addr])
    await ClockCycles(dut.aclk, 300)         # drain all writes

    async def _run_arm(mode, thresh, row_sel=0, col_sel=0):
        dut.sched_order_mode_i.value = mode
        dut.sched_age_thresh_i.value = thresh
        dut.sched_row_sel_i.value = row_sel
        dut.sched_col_sel_i.value = col_sel
        done, vic_beats = [0], []

        async def _collect():
            while True:
                await RisingEdge(dut.aclk)
                if int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value):
                    if int(dut.s_axi_rid.value) == VICTIM_ID:
                        vic_beats.append(int(dut.s_axi_rdata.value))
                    if int(dut.s_axi_rlast.value):
                        done[0] += 1

        task = cocotb.start_soon(_collect())
        await _ar(dut, hit_addr[0], 1)       # opens row H
        await ClockCycles(dut.aclk, 4)
        await _ar(dut, vic_addr, VICTIM_ID)  # the parked conflict victim
        for c in range(1, N):
            await _ar(dut, hit_addr[c], 1 + (c % 6))
        for _ in range(4000):
            await RisingEdge(dut.aclk)
            if done[0] >= N + 1:
                break
        task.kill()
        assert done[0] == N + 1, (
            f"mode {mode}: only {done[0]}/{N+1} reads returned -- the "
            f"parked-victim pattern wedged the read path")
        assert vic_beats[:BL_WORDS] == golden[vic_addr], (
            f"mode {mode}: victim data not golden")

    for mode, thresh, rs, cs in ((0, 0, 0, 0), (3, 2, 0, 0), (1, 0, 0, 0),
                                 (0, 0, 1, 1), (0, 0, 2, 2), (0, 0, 0, 0)):
        await _run_arm(mode, thresh, rs, cs)
    dut._log.info(f"PASS sched_order: parked-victim pattern clean under "
                  f"fr_fcfs / age_threshold / in_order / most_pending / "
                  f"fewest_pending / disarm")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_refresh_credit(dut):
    """PUMICE-006 Axis 3: REF_CTRL postpone/pullin JEDEC +-8 credits.

    tREFI is poked small (96 cyc) so a demand stretch of ~40 back-to-back
    writes spans ~5 ticks. REF counts at the DFI slave are the observable.

      arm A (strict, red guard): defaults -> refreshes interleave with the
        demand stretch (>= 3 REFs). If postponement ever leaks into the
        default encoding, this arm fails.
      arm B (postpone=7): same stretch -> ZERO REFs (all postponed; backlog
        5 <= 7). A second stretch pushes the backlog past the limit -> the
        retention ceiling FORCES refreshes under demand (>= 1). Idle then
        drains the backlog (conservation: >= 8 REFs across both stretches
        plus drain).
      arm C (pullin=8): confirmed idle -> refreshes run AHEAD (>= 8 extra
        REFs banked as credit); the next demand stretch consumes credit
        instead of refreshing -> ZERO REFs during demand. Data stays golden.
      arm D (disarm): knobs back to 0 -> after leftover credits burn, strict
        interleaving returns (>= 3 REFs across a longer stretch).
    """
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC
    _memory, slave = await _bring_up(dut, page_policy=0)
    dut.t_refi_i.value = 96
    dut.t_rfc_i.value = 8
    # The tREFI counter only reloads on expiry, so the poke takes effect after
    # the STALE bring-up period (0x400) runs out once. Wait it out so every
    # timed window below really spans ~cycles/96 ticks.
    await ClockCycles(dut.aclk, 1100)
    rng = random.Random(int(os.environ.get("SEED", "11")))
    written = {}

    def _refs():
        return slave.cmd_counts.get(_DC.REF, 0)

    async def _demand(cycles, tag):
        """Sustained back-to-back writes for a TIMED window of `cycles` --
        keeps CAM occupancy (demand) high; the write loop paces itself off
        the AW/W handshakes and stops when the window elapses."""
        state = {"done": False}

        async def _window():
            await ClockCycles(dut.aclk, cycles)
            state["done"] = True

        cocotb.start_soon(_window())
        k = 0
        while not state["done"]:
            addr = _mkaddr((tag + k) % NUM_BANKS, (tag * 7 + k) & 0x3F,
                           (k & 0x3F) * BL)
            data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
            written[addr] = data
            await _aw(dut, addr, k & 0xF)
            await _w(dut, data)
            k += 1

    # ---- arm A: strict (red guard) -----------------------------------------
    dut.ref_postpone_i.value = 0
    dut.ref_pullin_i.value = 0
    b = _refs()
    await _demand(480, 1)                        # ~5 tREFI ticks
    refs_a = _refs() - b
    assert refs_a >= 3, (f"strict: only {refs_a} REFs across the demand "
                         f"stretch -- tREFI poke dead or refresh gated")

    # ---- arm B: postpone ----------------------------------------------------
    dut.ref_postpone_i.value = 7
    b = _refs()
    await _demand(480, 9)                        # ~5 ticks, under the limit
    refs_b1 = _refs() - b
    assert refs_b1 == 0, (f"postpone=7 leaked {refs_b1} REFs into a demand "
                          f"stretch of ~5 ticks (backlog below the limit)")
    await _demand(640, 17)                       # backlog passes the limit
    refs_b2 = _refs() - b
    assert refs_b2 >= 1, ("postpone: retention ceiling never forced a REF "
                          "with the backlog past the limit -- credit "
                          "accumulator is unbounded")
    await ClockCycles(dut.aclk, 1200)            # idle: drain the backlog
    refs_b3 = _refs() - b
    assert refs_b3 >= 8, (f"postpone: only {refs_b3} REFs after drain -- "
                          f"postponed refreshes were LOST, not deferred")

    # ---- arm C: pull-in -----------------------------------------------------
    dut.ref_postpone_i.value = 0
    dut.ref_pullin_i.value = 8
    b = _refs()
    await ClockCycles(dut.aclk, 400)             # confirmed idle: run ahead
    refs_c1 = _refs() - b
    assert refs_c1 >= 8, (f"pullin=8: only {refs_c1} REFs across a ~4-tick "
                          f"idle window -- credit is not running ahead")
    b = _refs()
    await _demand(480, 33)                       # ~5 ticks vs 8 credits
    refs_c2 = _refs() - b
    assert refs_c2 == 0, (f"pullin: {refs_c2} REFs during demand despite "
                          f"banked credit -- ticks are not consuming credit")
    for addr in list(written)[-3:]:              # integrity spot-check
        got = []
        cocotb.start_soon(_r_sink(dut, got))
        await _ar(dut, addr, 5)
        for _ in range(800):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == written[addr], f"data mismatch @ {addr:#x}"

    # ---- arm D: disarm ------------------------------------------------------
    dut.ref_pullin_i.value = 0
    b = _refs()
    await _demand(800, 41)                       # leftover credit burns first
    refs_d = _refs() - b
    assert refs_d >= 3, (f"disarm: only {refs_d} REFs -- strict behaviour "
                         f"did not return after the credits burned")
    dut._log.info(f"PASS refresh credits: strict {refs_a}, postpone 0/"
                  f"forced>={refs_b2}/drained {refs_b3}, pullin ahead "
                  f"{refs_c1}/demand {refs_c2}, disarm {refs_d}")


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_pumice_core_waw(dut):
    """WAW ordering + read-your-write: two writes to the SAME address, then read
    must return the YOUNGER write (in-order commit + youngest-match)."""
    await _bring_up(dut, page_policy=0)
    rng = random.Random(int(os.environ.get("SEED", "3")))
    n = {"basic": 4, "medium": 10, "full": 20}.get(os.environ.get("TEST_LEVEL", "basic").lower(), 4)
    for k in range(n):
        addr = _mkaddr(rng.randint(0, NUM_BANKS - 1), rng.randint(0, 63), rng.randint(0, 63) * BL)
        a_data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        b_data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        # write A then B to the same address (B is younger)
        await _aw(dut, addr, k & 0xF); await _w(dut, a_data)
        await _aw(dut, addr, k & 0xF); await _w(dut, b_data)
        for _ in range(600):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value):
                break
        await ClockCycles(dut.aclk, 200)  # let both writes fully commit+evict to golden
        got = []
        cocotb.start_soon(_r_sink(dut, got))
        await _ar(dut, addr, k & 0xF)
        for _ in range(800):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == b_data, \
            f"WAW read {k} @ {addr:#x} returned {got[:BL_WORDS]} != younger {b_data}"
    dut._log.info(f"PASS: WAW ordering — {n} same-address overwrites read back the younger write")


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_pumice_core_b2b(dut):
    """Back-to-back writes with NO inter-write spacing, then back-to-back reads.
    Regression sentinel for the DQ-bus-occupancy collision: at BL8/DFI_RATE=2 a
    burst owns the DQ bus for BL/DFI_RATE cycles, so consecutive column commands
    must be paced by pumice_dfi_cmd_path or the 2nd burst's wrdata collides and
    strands in the PHY (which then blocks all reads). Distinct addresses (no
    snarf) exercise the full write->DRAM->read path under tight issue."""
    memory, _slave = await _bring_up(dut, page_policy=0)
    rng = random.Random(int(os.environ.get("SEED", "4")))
    n = {"basic": 8, "medium": 24, "full": 48}.get(os.environ.get("TEST_LEVEL", "basic").lower(), 8)
    seen, reqs = set(), []
    while len(reqs) < n:
        a = _mkaddr(rng.randint(0, NUM_BANKS - 1), rng.randint(0, 63), rng.randint(0, 63) * BL)
        if a in seen:
            continue
        seen.add(a)
        reqs.append((a, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]))
    # fire every AW/W with no wait for B between them (tight, back-to-back)
    for k, (addr, data) in enumerate(reqs):
        await _aw(dut, addr, k & 0xF)
        await _w(dut, data)
    # drain all B responses
    for _ in range(4000):
        await RisingEdge(dut.aclk)
        if not int(dut.s_axi_awvalid.value) and not int(dut.s_axi_wvalid.value):
            break
    await ClockCycles(dut.aclk, 300)
    # read every address back-to-back and check vs golden
    for k, (addr, data) in enumerate(reqs):
        got = []
        cocotb.start_soon(_r_sink(dut, got))
        await _ar(dut, addr, k & 0xF)
        for _ in range(1200):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == data, \
            f"B2B read {k} @ {addr:#x}: {[hex(x) for x in got[:BL_WORDS]]} != {[hex(x) for x in data]}"
    dut._log.info(f"PASS: back-to-back — {n} tightly-issued bursts round-trip vs golden (DQ pacing)")


def _echo_seed(tag):
    # PUMICE-010: pytest shows captured stdout for FAILING tests, so a
    # one-off red is reproducible with SEED=<n> after the fact.
    sd = os.environ.get('SEED', str(random.randint(0, 100000)))
    print(f"[seed] {tag} SEED={sd}")
    return sd


def _run(request, testcase, params_over=None):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_core_tb_top"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = os.path.join(tests_dir, "local_sim_build", testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
              "COL_WIDTH": str(COL_WIDTH), "DFI_RATE": str(DFI_RATE),
              "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "BL": str(BL),
              "NUM_ENTRIES": "8", "N_SRAM_SLOTS": "8"}
    if params_over:
        params.update(params_over)
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml"),
                 "SEED": _echo_seed(testcase),
                 "TEST_LEVEL": os.environ.get("TEST_LEVEL", "basic")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--public-flat-rw", "--assert"],
        waves=(os.environ.get("WAVES", "0") == "1"),
        plus_args=(["--trace"] if os.environ.get("WAVES", "0") == "1" else []),
        keep_files=True, timescale="1ns/1ps")


def test_pumice_core_dfi(request):   _run(request, "cocotb_test_pumice_core_dfi")
def test_pumice_core_fixed_open(request):
    _run(request, "cocotb_test_pumice_core_fixed_open")


def test_pumice_core_rbl(request):
    _run(request, "cocotb_test_pumice_core_rbl")


def test_pumice_core_acc(request):
    _run(request, "cocotb_test_pumice_core_acc")


def test_pumice_core_refresh_credit(request):
    _run(request, "cocotb_test_pumice_core_refresh_credit")


def test_pumice_core_sched_order(request):
    _run(request, "cocotb_test_pumice_core_sched_order")


def test_pumice_core_refresh_collide(request):
    # CMD_HISTORY_EN arms the scheduler's command-history scoreboard -- the
    # sequencing half of the PUMICE-004 detector. Without it the docstring's
    # "expected RED" was vacuous: the generate block was off, and the loopback
    # DFI slave serves golden data regardless, so the data compare alone
    # cannot see a refresh-vs-open-row collision.
    _run(request, "cocotb_test_pumice_core_refresh_collide",
         params_over={"CMD_HISTORY_EN": "1"})
def test_pumice_core_close(request): _run(request, "cocotb_test_pumice_core_close")
def test_pumice_core_waw(request):   _run(request, "cocotb_test_pumice_core_waw")
def test_pumice_core_b2b(request):   _run(request, "cocotb_test_pumice_core_b2b")
