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
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, ClockCycles, with_timeout

from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from CocoTBFramework.components.axi4.axi4_sequence import AXI4Sequence
from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel

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
             "dv/tb/pumice_core_tb_top.f")

# dv/ on sys.path so `tbclasses.*` resolves (trackers + the shared AXI BFM).
# This runs BELOW the import block, so anything under `tbclasses` has to be
# imported after it -- that is why the tracker imports are function-local.
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.pumice_axi_bfm import PumiceAxiBfm      # noqa: E402

NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 14, 10
# Geometry. The defaults are the historical sim point (128b core, BL8, device
# width == beat width) -- NOT the board's. Overridable so a run can reproduce
# the FPGA exactly, which is the only way some rate limits are visible at all:
# at the default geometry one DRAM burst is FOUR core beats, so an issue path
# that admits half a sub-command per cycle still supplies 2 beats/cycle and
# looks healthy. The board (BL4 on x16, 32b beat) gets ONE beat per burst, so
# the same path measures exactly half the DRAM rate. That is how a 2x read
# throttle reached silicon with this suite green -- see PUMICE-025.
#   board:  TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16
DFI_RATE   = int(os.environ.get("TEST_DFI_RATE", "2"))
DRAM_BEAT  = int(os.environ.get("TEST_DRAM_BEAT", "64"))
BL         = int(os.environ.get("TEST_DRAM_BL", "8"))
DRAM_DEV_W = int(os.environ.get("TEST_DRAM_DEVICE_W", str(DRAM_BEAT)))
DW = DRAM_BEAT * DFI_RATE          # core/host data width
SW = DW // 8
# AXI beats per DRAM burst = (BL x device bits) / core width.
BL_WORDS = max(1, (BL * DRAM_DEV_W) // DW)
# Column addresses are decoded at DEVICE-word granularity: pumice_core sets
# BYTE_OFFSET_WIDTH = $clog2(DRAM_DEVICE_WIDTH/8) and addr_mapper shifts the
# AXI byte address down by it. This MUST be derived, not assumed -- it is 3
# only while the device word is 64 bits. On the board (x16) it is 1, and a TB
# that keeps shifting by 3 builds addresses four times too large: the bank
# field slides, 256 bursts meant for 8 banks land on 2, and the write stream
# loses the bank parallelism it exists to measure.
BYTE_OFFSET = max(0, (DRAM_DEV_W // 8).bit_length() - 1)   # == clog2(bytes)
# Utilization floors below are all "beats moved per access / cycles per
# access", and beats-per-access IS BL_WORDS. They were tuned at BL_WORDS=4, so
# on the board (BL_WORDS=1, one DFI burst per AXI beat) the same hardware reads
# a quarter of the number with nothing wrong. Scale them rather than carry a
# second set. See PUMICE-028.
GEOM_UTIL_SCALE = BL_WORDS / 4.0
# PHY-to-DRAM ratio: how many DEVICE words ride in one DFI phase. K=1 when the
# beat is the device word (the default sim geometry); K=2 for a 32-bit beat
# over an x16 part (the board). DFI beats per DRAM burst is BL/K -- the DUT
# drives that many phases, so a slave model told BL waits forever for phases
# that never come, and every read times out with nothing returned.
K_PHY = max(1, DRAM_BEAT // DRAM_DEV_W)
DFI_BEATS_PER_BURST = max(1, BL // K_PHY)
BURST_INCR = 1


def _cfg(dut, page_policy=0):
    dut.memtype_i.value = 0
    dut.page_policy_i.value = page_policy
    dut.bank_lsb_i.value  = 10   # ROW_MAJOR
    dut.hash_en_i.value   = 0
    dut.hash_seed_i.value = 0
    # Row timings are env-overridable (defaults unchanged) so a throughput
    # shortfall can be attributed instead of guessed at. That is how the
    # close-page gap was pinned: static_close measures 30.77% at tRRD 1, 2 AND
    # 4 alike, which rules out inter-bank ACT spacing, and only tRCD moves it
    # (to 37.5% with every row timing at minimum) -- so the limit is command
    # scheduling, not DRAM timing.
    for t, v in [("t_rcd_i", int(os.environ.get("TEST_T_RCD", "3"))),
                 ("t_rp_i", int(os.environ.get("TEST_T_RP", "3"))),
                 ("t_ras_i", 4), ("t_rc_i", int(os.environ.get("TEST_T_RC", "6"))),
                 ("t_wr_i", 3), ("t_rtp_i", 2), ("t_faw_i", int(os.environ.get("TEST_T_FAW", "6"))), ("t_rrd_i", int(os.environ.get("TEST_T_RRD", "2"))),
                 ("t_wtr_i", 2), ("t_rtw_i", 2),
                 # tCCD = the column's DQ occupancy in MC cycles, which is
                 # one DFI word per cycle for the length of the burst:
                 #     (BL x device bits) / (DRAM beat x DFI_RATE) == BL_WORDS
                 # BL8 x64 at DFI_RATE 2 is 4 DFI words -> 4, which is what this
                 # was hardcoded to. BL4 x16 (the board) is ONE -> 1, and
                 # leaving it at 4 spaces every column command four cycles apart
                 # and caps the write stream at ~25% with a 3-cycle stall
                 # between every burst. Derive it; do not assume BL8.
                 ("t_ccd_i", BL_WORDS)]:
        getattr(dut, t).value = v
    dut.t_refi_i.value = 0x0400          # periodic refresh during the run
    dut.refi_reload_i.value = 0
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
    # NOTE: the s_axi_* channels are deliberately NOT touched here. The
    # AXI4 master BFMs own every one of them (including AWBURST/ARBURST
    # and the B/R ready lines) -- driving them from the test as well
    # would be a second driver on the same nets, and hand-poking a
    # valid/ready interface is forbidden outright. See _masters_init().


def _mkaddr(bank, row, col):
    # {row|bank|col} << byte_offset. The "+ 3" in the row shift is the BANK
    # field width (log2(NUM_BANKS)=3) and is unrelated to the byte offset.
    return (((row << (COL_WIDTH + 3)) | (bank << COL_WIDTH) | col)
            << BYTE_OFFSET)


async def _bring_up(dut, page_policy=0, read_latency=0, strict_read=False):
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
                   mapping=mapping, beats_per_burst=DFI_BEATS_PER_BURST)
    slave = DFISlavePHY(dut, dut.dfi_clk, base=base, memory=memory,
                        dfi_phase_bytes=DRAM_BEAT // 8,
                        strict_read_timing=strict_read, read_latency=read_latency)
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
    # The command stream is released CMD_DELAY cycles after the arbiter pushes
    # it (WR data must lead), so the init sequence's tail -- its two REFs --
    # reaches the DFI ~20 cycles AFTER init_done. Let it land before any test
    # samples a refresh baseline (else "2 refreshes inside a parked window").
    await ClockCycles(dut.aclk, 40)

    # AXI4 master BFMs. HARD RULE (Sean 2026-08-27): no environment may
    # hand-poke a standard/valid-ready interface -- all host traffic goes
    # through the BFMs, whose randomizers model real protocol timing.
    # 'backtoback' (zero inter-beat delay) is mandatory for perf work:
    # a lazy driver starves the DUT and the numbers grade the testbench.
    _masters_init(dut)

    # PUMICE-012: opt-in structure trackers. PUMICE_TRACKERS=1 wires the
    # passive per-FUB trackers and each writes <sim_build>/<short>.out at
    # end of sim -- one greppable markdown table per structure, so a
    # paging / refresh / scheduling decision can be followed across them:
    #   grep '| pgpol' pgpol.out      # paging decisions
    #   grep '| refr'  refr.out       # refresh credits + grants
    #   grep '| camrd' camrd.out      # read CAM entry lifecycle
    # Off by default: zero cost to the normal regression.
    if os.environ.get("PUMICE_TRACKERS", "0") == "1":
        from tbclasses.trackers import wire_trackers
        wire_trackers(dut, log=dut._log, num_banks=NUM_BANKS, scope_paths={
            "sched":   "u_core.u_sched.u_arbiter",
            "btmr":    "u_core.u_sched.u_bank_timers",
            "refr":    "u_core.u_sched.u_refresh",
            "pgpol":   "u_core.u_sched.u_page_policy",
            "init":    "u_core.u_sched.u_init",
            "camrd":   "u_core.u_ifc.u_rd_cam",
            "camwr":   "u_core.u_ifc.u_wr_cam",
            "dficmd":  "u_core.u_dfi.u_cmd",
            "wrbeat":  "u_core.u_dfi.u_wr",
            "rdalign": "u_core.u_dfi.u_rd",
        })
        # AXI-side utilization + handshake run lengths (DV-side only; the
        # silicon equivalent is the external observer, PUMICE-008).
        from tbclasses.trackers import wire_axi_channels
        wire_axi_channels(dut, prefix="s_axi_", log=dut._log,
                          clk_signal="aclk")   # writes axi_util.out at exit
        dut._log.info("PUMICE_TRACKERS=1: structure + AXI channel trackers wired")

    return memory, slave


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_pumice_core_dfi(dut):
    await _bring_up(dut, page_policy=0)   # OPEN

    rng = random.Random(int(os.environ.get("SEED", "1")))
    level = os.environ.get("TEST_LEVEL", "basic").lower()
    n = {"gate": 6, "basic": 6, "func": 20, "medium": 20, "full": 48}.get(level, 6)

    # distinct addresses across banks/rows; BL-word aligned
    seen = set()
    reqs = []
    while len(reqs) < n:
        bank = rng.randint(0, NUM_BANKS - 1)
        row = rng.randint(0, 63)
        col = rng.randint(0, 63) * BL   # BL-aligned column
        addr = _mkaddr(bank, row, col)
        if addr in seen:
            continue
        seen.add(addr)
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        reqs.append((addr, data))

    # ---- write phase ----
    for k, (addr, data) in enumerate(reqs):
        await _write(dut, addr, data, k & 0xF)

    # ---- read phase (R backpressure on the odd reads) ----
    # Backpressure comes from the BFM's R-channel randomizer profile, NOT
    # from poking s_axi_rready: 'burst_pause' gives the R consumer real
    # ready_delay gaps (0 mostly, 12-25 cycles occasionally).
    for k, (addr, data) in enumerate(reqs):
        _set_r_profile(dut, "burst_pause" if (k % 2) else "backtoback")
        got = await _read(dut, addr, k & 0xF)
        assert got[:BL_WORDS] == data, (
            f"read {k} @ {addr:#x} mismatch:\n  got {[hex(x) for x in got[:BL_WORDS]]}"
            f"\n  exp {[hex(x) for x in data]}")

    _set_r_profile(dut, "backtoback")
    dut._log.info(f"PASS: {n} bursts written+read-back vs DFISlavePHY golden "
                  f"(multi-bank, refresh active, R backpressure via BFM profile)")


_BFM: dict = {}


def _masters_init(dut) -> None:
    """Build the shared AXI4 master BFMs (backtoback by default)."""
    _BFM['b'] = PumiceAxiBfm(dut, data_width=DW, bl_words=BL_WORDS)


def _set_r_profile(dut, profile: str) -> None:
    """Retime ONLY the read master's R channel (consumer backpressure)."""
    _BFM['b'].set_profile(profile, channels=('r',))


async def _run_seq(dut, seq, *, engine: bool = False):
    return await _BFM['b'].run(seq, engine=engine)


async def _write(dut, addr, data, wid=0):
    await _BFM['b'].write(addr, data, wid)


async def _read(dut, addr, rid=0):
    return await _BFM['b'].read(addr, rid)


async def _write_many(dut, reqs):
    await _BFM['b'].write_many(reqs)


async def _read_many(dut, addrs, axid_fn=lambda k: k & 0xF):
    return await _BFM['b'].read_many(addrs, axid_fn)


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_pumice_core_close(dut):
    """CLOSE page policy: every column op is auto-precharge (RDA/WRA)."""
    await _bring_up(dut, page_policy=1)   # CLOSE
    rng = random.Random(int(os.environ.get("SEED", "2")))
    n = {"gate": 6, "basic": 6, "func": 16, "medium": 16, "full": 32}.get(os.environ.get("TEST_LEVEL", "basic").lower(), 6)
    seen, reqs = set(), []
    while len(reqs) < n:
        a = _mkaddr(rng.randint(0, NUM_BANKS - 1), rng.randint(0, 63), rng.randint(0, 63) * BL)
        if a in seen:
            continue
        seen.add(a)
        reqs.append((a, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]))
    for k, (addr, data) in enumerate(reqs):
        await _write(dut, addr, data, k & 0xF)
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                break
    for k, (addr, data) in enumerate(reqs):
        got = await _read(dut, addr, k & 0xF)
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
        await _write(dut, addr, data, k & 0xF)
    await ClockCycles(dut.aclk, 500)                 # drain writes into golden

    # Sustained same-bank reads as ONE pipelined BFM sequence: the read
    # master keeps AR busy, which is what makes a refresh land mid-burst.
    results = await _read_many(dut, [a for a, _ in exp])
    by_addr = {a: beats for a, beats in results}

    bad = 0
    for k, (addr, data) in enumerate(exp):
        beats = by_addr.get(addr)
        if beats is None or beats[:BL_WORDS] != data:
            g = [hex(x) for x in beats[:BL_WORDS]] if beats else "MISSING"
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
    """TASK-001 Axis 2: fixed_open + adapt_time idle-timeout page close.

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
        await _write(dut, addr, data, rid & 0xF)
        got = await _read(dut, addr, rid & 0xF)
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
async def cocotb_test_pumice_core_sched_order(dut):
    """TASK-001 Axis 1: SCHED_POLICY.order_mode integrity sweep + the
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
        await _write(dut, addr, golden[addr], 0)
    await ClockCycles(dut.aclk, 300)         # drain all writes

    async def _run_arm(mode, thresh, row_sel=0, col_sel=0):
        dut.sched_order_mode_i.value = mode
        dut.sched_age_thresh_i.value = thresh
        dut.sched_row_sel_i.value = row_sel
        dut.sched_col_sel_i.value = col_sel
        # ONE ordered read sequence: row-H opener, then the parked
        # conflict victim, then the rest of the row-H stream. The BFM
        # issues them in order and reports every completion, so the
        # wedge check is "did all N+1 come back" with no hand-driving.
        seq = AXI4Sequence("parked_victim", data_width=DW)
        seq.add_read(hit_addr[0], length=BL_WORDS, axid=1)
        seq.add_read(vic_addr,    length=BL_WORDS, axid=VICTIM_ID)
        for c in range(1, N):
            seq.add_read(hit_addr[c], length=BL_WORDS, axid=1 + (c % 6))
        res = await _run_seq(dut, seq)

        assert len(res) == N + 1, (
            f"mode {mode}: only {len(res)}/{N+1} reads returned -- the "
            f"parked-victim pattern wedged the read path")
        vic = [list(d["data"]) for d in res if d.get("addr") == vic_addr]
        assert vic and vic[0][:BL_WORDS] == golden[vic_addr], (
            f"mode {mode}: victim data not golden")

    for mode, thresh, rs, cs in ((0, 0, 0, 0), (3, 2, 0, 0), (1, 0, 0, 0),
                                 (0, 0, 1, 1), (0, 0, 2, 2), (0, 0, 0, 0)):
        await _run_arm(mode, thresh, rs, cs)
    dut._log.info(f"PASS sched_order: parked-victim pattern clean under "
                  f"fr_fcfs / age_threshold / in_order / most_pending / "
                  f"fewest_pending / disarm")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_refresh_credit(dut):
    """TASK-001 Axis 3: REF_CTRL postpone/pullin JEDEC +-8 credits.

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
    # Force the tREFI counter to pick up the new interval NOW. It otherwise
    # reloads only on expiry, so the already-armed interval from bring-up
    # would run first -- which is why this used to burn ~1100 idle cycles and
    # still leaked a stale refresh into the measurement window.
    dut.refi_reload_i.value = 1
    await ClockCycles(dut.aclk, 2)
    dut.refi_reload_i.value = 0
    await ClockCycles(dut.aclk, 2)
    rng = random.Random(int(os.environ.get("SEED", "11")))
    written = {}

    def _refs():
        return slave.cmd_counts.get(_DC.REF, 0)

    async def _demand_n(n, tag):
        """`n` back-to-back writes as ONE pipelined BFM sequence, so the CAM
        stays occupied for the whole window -- that occupancy IS the
        `demand_i` the credit logic keys off."""
        reqs = []
        for k in range(n):
            addr = _mkaddr((tag + k) % NUM_BANKS, (tag * 7 + k) & 0x3F,
                           (k & 0x3F) * BL)
            data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
            written[addr] = data
            reqs.append((addr, data))
        await _write_many(dut, reqs)

    # Every arm below asserts over a TIMED window -- arm B's whole claim is
    # that nothing refreshes inside a stretch SHORTER than the postpone
    # budget (7 backlogged refreshes x tREFI 96 = 672 cycles), and that a
    # LONGER stretch does force one. Demand, however, is issued as WORK, and
    # cycles-per-burst depends on profile, page policy and DFI rate.
    #
    # Estimating the burst count up front does not work, in either direction:
    # two hardcoded guesses (10, then 50 cycles/burst) overshot and forced the
    # refreshes arm B says are withheld; a measured one-shot calibration then
    # UNDERSHOT, because an 8-burst sample carries sequence-setup overhead
    # (9.4 cyc/burst) while steady state is ~5.5 -- so a 480-cycle request
    # delivered 287 and the backlog never reached the limit.
    #
    # So close the loop on elapsed time instead of predicting it: issue small
    # calibrated batches until the window has actually elapsed, refining the
    # rate as we go. Batches are capped so the overshoot past `cycles` stays
    # well inside the postpone budget.
    _rate = [8.0]                       # cycles/burst, refined per batch
    _BATCH_MAX = 16

    def _elapsed(t0):
        return (get_sim_time('ns') - t0) / 10.0

    async def _demand(cycles, tag):
        """Sustained demand for at least `cycles` cycles of real sim time."""
        t0, r0 = get_sim_time('ns'), _refs()
        k = 0
        while _elapsed(t0) < cycles:
            want = cycles - _elapsed(t0)
            n = max(2, min(_BATCH_MAX, int(want / _rate[0])))
            b0 = get_sim_time('ns')
            await _demand_n(n, tag + k * _BATCH_MAX)
            _rate[0] = max(1.0, (get_sim_time('ns') - b0) / 10.0 / n)
            k += 1
        el = _elapsed(t0)
        dut._log.info("demand(want=%d tag=%d): actual=%.0f cyc (%.1f tREFI "
                      "ticks) in %d batches @%.1f cyc/burst, REFs=%d",
                      cycles, tag, el, el / 96.0, k, _rate[0], _refs() - r0)

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
    # <= 1, not == 0: the per-bank arbiter's faster column schedule shifts the
    # demand window by ~one arbiter tick relative to the REF cadence, so a
    # single REF at the very edge of the window can slip through before demand
    # fully ramps. The credit mechanism is unaffected (it still consumes on the
    # ticks); this is a measurement-boundary effect, one REF, not a leak.
    assert refs_c2 <= 1, (f"pullin: {refs_c2} REFs during demand despite "
                          f"banked credit -- ticks are not consuming credit")
    for addr in list(written)[-3:]:              # integrity spot-check
        got = await _read(dut, addr, 5)
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
    n = {"gate": 4, "basic": 4, "func": 10, "medium": 10, "full": 20}.get(os.environ.get("TEST_LEVEL", "basic").lower(), 4)
    for k in range(n):
        addr = _mkaddr(rng.randint(0, NUM_BANKS - 1), rng.randint(0, 63), rng.randint(0, 63) * BL)
        a_data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        b_data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        # write A then B to the same address (B is younger)
        await _write(dut, addr, a_data, k & 0xF)
        await _write(dut, addr, b_data, k & 0xF)
        for _ in range(600):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value):
                break
        await ClockCycles(dut.aclk, 200)  # let both writes fully commit+evict to golden
        got = await _read(dut, addr, k & 0xF)
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
    n = {"gate": 8, "basic": 8, "func": 24, "medium": 24, "full": 48}.get(os.environ.get("TEST_LEVEL", "basic").lower(), 8)
    seen, reqs = set(), []
    while len(reqs) < n:
        a = _mkaddr(rng.randint(0, NUM_BANKS - 1), rng.randint(0, 63), rng.randint(0, 63) * BL)
        if a in seen:
            continue
        seen.add(a)
        reqs.append((a, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]))
    # fire every AW/W with no wait for B between them (tight, back-to-back)
    for k, (addr, data) in enumerate(reqs):
        await _write(dut, addr, data, k & 0xF)
    # drain all B responses
    for _ in range(4000):
        await RisingEdge(dut.aclk)
        if not int(dut.s_axi_awvalid.value) and not int(dut.s_axi_wvalid.value):
            break
    await ClockCycles(dut.aclk, 300)
    # read every address back-to-back and check vs golden
    for k, (addr, data) in enumerate(reqs):
        got = await _read(dut, addr, k & 0xF)
        assert got[:BL_WORDS] == data, \
            f"B2B read {k} @ {addr:#x}: {[hex(x) for x in got[:BL_WORDS]]} != {[hex(x) for x in data]}"
    dut._log.info(f"PASS: back-to-back — {n} tightly-issued bursts round-trip vs golden (DQ pacing)")


# ---------------------------------------------------------------------------
# Write-stream perf measurement (TASK-002)
#
# Two tests share ONE experiment and change ONE knob: the refresh interval.
# That is the whole point -- a ceiling with nothing to compare it against
# cannot tell you whether the measurement is even sensitive. The parked-
# refresh run says "the datapath never stalls"; the frequent-refresh run
# proves the instrument can SEE a stall, and prices refresh in the same
# units. Neither claim is worth much without the other.
# ---------------------------------------------------------------------------

async def _measure_write_stream(dut, *, t_refi, t_rfc, label, title, n=256,
                                page_mode=0, page_policy=0, sched=None,
                                dump=True):
    """Run a clean write stream and account for every W-channel cycle.

    Everything that could inject a command into the DRAM stream or close a
    row behind us is parked, EXCEPT refresh, which is the independent
    variable:

      * paging OPEN     -- page_policy_e OPEN (=0, NOT 1: that encoding is
                           CLOSE, and picking it re-activated on every burst
                           -- 258 ACTs for 256 bursts). The Axis-2 mode stays
                           at the build default, so no idle-timeout PRE and
                           no adaptive predictor closes rows behind us.
      * page HITS only  -- strictly incrementing columns inside ONE row per
                           bank, so after the opening ACT per bank there is
                           no ACT/PRE in steady state.
      * writes only     -- no read turnaround (tWTR/tRTW) in the stream.
      * b2b on BOTH     -- AW and W randomizers at `backtoback` (zero
                           inter-beat delay), issued through the ENGINE
                           runner so all AWs queue up front and the W
                           channel never waits on an address.
      * refresh         -- t_refi_i = `t_refi`. Postpone/pullin credits at 0
                           and ref_mode_i=0 so refresh is plain periodic:
                           nothing defers a refresh out of the window or
                           runs ahead to bank credit.

    Measurement:

      utilization = beats / cycles WVALID was high

    The denominator is only the cycles the master actually held wvalid --
    which naturally ends when the last wready drops it. Cycles where the
    master had nothing to offer are the testbench's gaps and say nothing
    about the DUT, so they are excluded rather than diluted into the
    number. Defined this way 100% means "every cycle data was offered, the
    DUT took it", which is the thing the design is answerable for:

      wvalid && !wready -> DUT refusing data. The ONLY way to fall below 100%.
      !wvalid && wready -> testbench not keeping up. Excluded from the ratio,
                           but asserted on by callers: a starved window
                           measures the driver, not the design.

    Returns a dict of the accounting; callers assert on it.
    """
    from tbclasses.trackers import AxiChanTracker
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC

    _memory, slave = await _bring_up(dut, page_policy=page_policy)

    # Axis-2 paging mode under test (0 = build default). Axis-1 scheduling
    # knobs default to 0 = build default unless `sched` overrides them.
    dut.page_mode_i.value = page_mode
    for k, v in (sched or {}).items():
        getattr(dut, k).value = v

    dut.t_refi_i.value       = t_refi
    dut.t_rfc_i.value        = t_rfc
    dut.ref_postpone_i.value = 0
    dut.ref_pullin_i.value   = 0
    dut.ref_mode_i.value     = 0
    # Force the tREFI counter to pick up the new interval NOW. It otherwise
    # reloads only on expiry, so the already-armed interval from bring-up
    # would run first -- which is why this used to burn ~1100 idle cycles and
    # still leaked a stale refresh into the measurement window.
    dut.refi_reload_i.value = 1
    await ClockCycles(dut.aclk, 2)
    dut.refi_reload_i.value = 0
    await ClockCycles(dut.aclk, 2)

    trk = AxiChanTracker(dut, 'w', valid="s_axi_wvalid", ready="s_axi_wready",
                         last="s_axi_wlast", log=dut._log)
    cocotb.start_soon(trk.run())
    # TB-attributable starvation: W offering nothing while the DUT is NOT
    # holding AW. With a rate-matched write commit (2026-09-09) the CAM fills
    # under refresh and AW back-pressures; the W engine then has no address to
    # stream against, which the W-only tracker would book as "TB starved".
    starv_tb = [0]
    async def _starv_tb():
        while True:
            await RisingEdge(dut.aclk)
            w_starv = (not int(dut.s_axi_wvalid.value)) and int(dut.s_axi_wready.value)
            aw_bp   = int(dut.s_axi_awvalid.value) and (not int(dut.s_axi_awready.value))
            if w_starv and not aw_bp:
                starv_tb[0] += 1
    cocotb.start_soon(_starv_tb())
    # WHERE the backpressure falls, split at "every bank has a row open".
    # This was added expecting the opening ACTs to show up here and they do
    # NOT: at board geometry bp_open is 0 and the single 2-cycle stall lands
    # at burst 44, the same burst at n=256 and n=1024. Probed at that cycle
    # the DUT holds AW as well (aw_valid=1, aw_ready=0) while the DFI write
    # side is ready -- so it is the 8-entry write CAM momentarily full, not
    # the datapath.
    #
    # That is the rate-match signature. At BL_WORDS=1 one AXI beat IS one
    # DRAM burst and tCCD is 1, so supply and drain are exactly matched: the
    # opening ACTs spend command slots the stream never gets back, the CAM
    # runs one entry behind from then on, and it resyncs once. The cost is
    # therefore FIXED, not a rate -- which is what the n=256 vs n=1024
    # comparison measures and why the assertion below bounds it by a constant
    # instead of requiring zero. A datapath that genuinely could not sustain
    # the stream would stall per burst and scale with n.
    bp_open, bp_steady = [0], [0]
    async def _bp_split():
        bursts_done = 0
        while True:
            await RisingEdge(dut.aclk)
            v, r = int(dut.s_axi_wvalid.value), int(dut.s_axi_wready.value)
            if v and not r:
                (bp_steady if bursts_done >= NUM_BANKS else bp_open)[0] += 1
            elif v and r and int(dut.s_axi_wlast.value):
                bursts_done += 1
    cocotb.start_soon(_bp_split())
    starv_tb0 = starv_tb[0]
    base = (trk.prod, trk.bp, trk.starv, trk.idle)
    ev0 = len(trk.events)

    rng = random.Random(int(os.environ.get("SEED", "7")))
    reqs = []
    for k in range(n):
        addr = _mkaddr(k % NUM_BANKS, 0x11, (k // NUM_BANKS) * BL)
        reqs.append((addr, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]))
    ref0 = slave.cmd_counts.get(_DC.REF, 0)
    t0 = get_sim_time('ns')
    await _write_many(dut, reqs)
    elapsed = (get_sim_time('ns') - t0) / 10.0

    m = {
        'label': label, 'title': title, 'bursts': n, 'beats': n * BL_WORDS,
        't_refi': t_refi, 't_rfc': t_rfc, 'elapsed': elapsed,
        'prod':  trk.prod  - base[0], 'bp':   trk.bp   - base[1],
        'starv': trk.starv - base[2], 'idle': trk.idle - base[3],
        'starv_tb': starv_tb[0] - starv_tb0,
        'bp_open': bp_open[0], 'bp_steady': bp_steady[0],
        'refs': slave.cmd_counts.get(_DC.REF, 0) - ref0,
        'max_run': max(trk.max_run, trk._run), 'max_bp_run': trk.max_bp_run,
    }
    m['valid_cycles'] = m['prod'] + m['bp']
    m['active'] = m['prod'] + m['bp'] + m['starv']
    m['util'] = (m['prod'] / m['valid_cycles']) if m['valid_cycles'] else 0.0
    # stall-run shape: one BP_<n> event per contiguous !wready stretch, so
    # this is the bubble profile -- a refresh should show up as a run of
    # roughly tRFC, not as scattered single cycles.
    runs = [int(ev.event[3:]) for ev in list(trk.events)[ev0:]
            if ev.event.startswith("BP_")]
    hist = {}
    for r in runs:
        hist[r] = hist.get(r, 0) + 1
    m['stall_runs'] = len(runs)
    m['stall_hist'] = dict(sorted(hist.items()))

    dut._log.info("=" * 66)
    dut._log.info("%s", title)
    dut._log.info("  t_refi=%d t_rfc=%d  bursts=%d beats=%d window=%.0f cyc",
                  t_refi, t_rfc, n, m['beats'], elapsed)
    dut._log.info("  UTILIZATION = %d beats / %d wvalid-cycles = %.2f%%",
                  m['prod'], m['valid_cycles'], 100.0 * m['util'])
    dut._log.info("  W prod=%d bp=%d starv=%d idle=%d  REFs=%d",
                  m['prod'], m['bp'], m['starv'], m['idle'], m['refs'])
    dut._log.info("  max handshake run=%d  stall runs=%d (max %d) hist=%s",
                  m['max_run'], m['stall_runs'], m['max_bp_run'],
                  m['stall_hist'])
    dut._log.info("=" * 66)

    # cocotb swallows stdout, so a printed number is invisible to whoever
    # runs this. Write the summary where the tracker's own .out files land.
    if not dump:
        return m
    try:
        with open(f"{label}.out", "w") as f:
            f.write(f"# {title}\n")
            f.write("# page policy OPEN, page-hit stream, writes only, AW+W b2b,\n")
            f.write("# engine runner (AWs queued back-to-back).\n")
            f.write("#\n# UTILIZATION = beats / cycles WVALID was high.\n")
            f.write("#   Cycles the master offered nothing are excluded --\n")
            f.write("#   they grade the testbench, not the DUT. So the only\n")
            f.write("#   way to fall below 100% is wvalid && !wready.\n\n")
            f.write(f"t_refi            {t_refi}\n")
            f.write(f"t_rfc             {t_rfc}\n")
            f.write(f"bursts            {n}\n")
            f.write(f"beats             {m['beats']}\n\n")
            f.write(f"wvalid_cycles     {m['valid_cycles']}\n")
            f.write(f"UTILIZATION       {100.0 * m['util']:.2f}%   "
                    f"({m['prod']} beats / {m['valid_cycles']} wvalid-cycles)\n\n")
            f.write(f"REFs_in_window    {m['refs']}\n")
            f.write(f"window_cycles     {elapsed:.0f}   # incl. TB gaps\n")
            f.write(f"max_handshake_run {m['max_run']}\n")
            f.write(f"stall_runs        {m['stall_runs']}\n")
            f.write(f"max_stall_run     {m['max_bp_run']}\n")
            f.write(f"stall_run_hist    {m['stall_hist']}   # cycles:count\n\n")
            f.write(f"W_productive      {m['prod']}\n")
            f.write(f"W_backpressure    {m['bp']}   # wvalid && !wready -- DUT stall\n")
            f.write(f"W_bp_opening      {m['bp_open']}   # during the first {NUM_BANKS} bursts (opening ACT per bank)\n")
            f.write(f"W_bp_steady       {m['bp_steady']}   # after every bank has a row open\n")
            f.write(f"W_starvation      {m['starv']}   # !wvalid && wready -- TB gap\n")
            f.write(f"W_starv_tb        {m['starv_tb']}   # starv NOT explained by AW backpressure\n")
            f.write(f"W_active          {m['active']}   # prod + bp + starv\n")
            f.write(f"W_idle            {m['idle']}\n\n")
            # The geometry this ran at. Without it a dump cannot be compared
            # against another run, and "the sim does not reproduce it" turns
            # into a property of the defect instead of of the build.
            f.write(f"# geometry: DRAM_BEAT={DRAM_BEAT} DRAM_BL={BL} "
                    f"DEVICE_W={DRAM_DEV_W} DFI_RATE={DFI_RATE}\n")
            f.write(f"# derived : DW={DW} BL_WORDS={BL_WORDS} "
                    f"BYTE_OFFSET={BYTE_OFFSET} t_ccd={BL_WORDS}\n")
    except Exception as e:                                    # noqa: BLE001
        dut._log.warning("%s.out dump failed: %s", label, e)

    return m


def _assert_stream_sane(m):
    """Checks that must hold for EITHER refresh setting."""
    assert m['prod'] == m['beats'], (
        f"W channel moved {m['prod']} beats, expected {m['beats']} -- the "
        f"accounting window does not cover the traffic")
    starv_tb = m.get('starv_tb', m['starv'])
    # PER BURST, not per active cycle. The engine's W refill gap is a fixed
    # cost per burst, so a share-of-window bound grades the GEOMETRY instead
    # of the driver: measured at 256 bursts, starvation is 30 cycles at
    # BL_WORDS=4 and 28 at BL_WORDS=1 -- the same driver -- but the active
    # window shrinks 4x with the burst, so the identical behaviour reads as
    # 2.9% and 9.8%. The old 8%-of-active passed one and failed the other.
    # Two terms, because there are two sources of TB-side gap:
    #   per BURST   -- the engine's refill gap. Measured 30 cycles / 256
    #                  bursts at BL_WORDS=4 and 28 / 256 at BL_WORDS=1
    #                  (0.117 and 0.109 cyc/burst): the same driver either way.
    #   per REFRESH -- each refresh stops the stream and the engine pays the
    #                  gap again on restart. refresh_bubbles measures 107
    #                  cycles over 256 bursts with 28 REFs; subtract the 30
    #                  burst-term cycles and that is 77/28 = 2.75 cyc/refresh.
    # Budgets are ~2x and ~1.5x the measured values.
    #
    # NOT a share of the active window. That was the old rule and it graded
    # the GEOMETRY: the identical driver reads as 2.9% at BL_WORDS=4 and 9.8%
    # at BL_WORDS=1 purely because the window shrinks 4x with the burst. It
    # also silently loosened whenever the DUT got SLOWER -- refresh inflates
    # `active`, so the allowance grew with the stalls it was meant to police.
    budget = max(8.0, 0.25 * m['bursts'] + 4.0 * m['refs'])
    assert m['active'] and starv_tb <= budget, (
        f"stimulus starved the DUT for {starv_tb} cycles over {m['bursts']} "
        f"bursts ({starv_tb / max(m['bursts'], 1):.3f} cyc/burst, budget "
        f"{budget:.0f}; W starv {m['starv']}, active {m['active']}) -- this "
        f"window measures the testbench, not the design; do not quote it")


async def _measure_read_stream(dut, *, t_refi, t_rfc, label, title, n=256,
                               page_policy=0, read_latency=0, strict_read=False):
    """Read-throughput CEILING: the DUT is the PRODUCER on R, so its own
    throttle is !rvalid && rready (starvation in the tracker frame). Hold
    rready continuously high (backtoback sink) and require the DUT to never
    fail to hand over a beat the sink is waiting for. Mirror of
    _measure_write_stream; the AR->first-R fill latency is excluded by only
    counting once rvalid has first risen, so every counted starv cycle is a
    genuine mid-stream read-datapath bubble.
    """
    from tbclasses.trackers import AxiChanTracker
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC

    _memory, slave = await _bring_up(dut, page_policy=page_policy,
                                     read_latency=read_latency,
                                     strict_read=strict_read)
    dut.t_refi_i.value = t_refi
    dut.t_rfc_i.value = t_rfc
    dut.ref_postpone_i.value = 0
    dut.ref_pullin_i.value = 0
    dut.ref_mode_i.value = 0
    dut.refi_reload_i.value = 1
    await ClockCycles(dut.aclk, 2)
    dut.refi_reload_i.value = 0
    await ClockCycles(dut.aclk, 2)

    # preload the exact pages we will read back: page-hit stream, one row per
    # bank (same address pattern the write ceiling streams).
    rng = random.Random(int(os.environ.get("SEED", "7")))
    reqs = []
    for k in range(n):
        addr = _mkaddr(k % NUM_BANKS, 0x11, (k // NUM_BANKS) * BL)
        reqs.append((addr, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]))
    await _write_many(dut, reqs)
    await ClockCycles(dut.aclk, 800)              # drain writes into golden
    _set_r_profile(dut, "backtoback")             # sink always ready

    # Start accounting only after the first R beat -- the AR->R fill is
    # unavoidable latency, not a datapath bubble.
    trk = AxiChanTracker(dut, 'r', valid="s_axi_rvalid", ready="s_axi_rready",
                         last="s_axi_rlast", log=dut._log)
    async def _track_after_fill():
        while True:
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_rvalid.value):
                break
        await trk.run()
    cocotb.start_soon(_track_after_fill())

    # EXACT beat accounting, independent of the tracker's arming. The tracker
    # deliberately starts late (it breaks on the edge where rvalid is first
    # high, then awaits trk.run()), so it samples up to two edges after the
    # first beat and never counts them. That loss hid under the
    # "beats - BL_WORDS" tolerance while a burst was 4 beats wide; at the
    # board geometry a burst is ONE beat and the same two lost edges fail the
    # check. Counting handshakes from t0 costs nothing -- no R beat can exist
    # before rvalid first rises -- and turns a "~expected" tolerance into an
    # exact equality.
    rbeats = [0]
    async def _count_r():
        while True:
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value):
                rbeats[0] += 1
    cocotb.start_soon(_count_r())

    ref0 = slave.cmd_counts.get(_DC.REF, 0)
    t0 = get_sim_time('ns')
    results = await _read_many(dut, [a for a, _ in reqs])
    elapsed = (get_sim_time('ns') - t0) / 10.0
    # _read_many and _count_r wake on the SAME RisingEdge and the order
    # between two coroutines on one edge is undefined, so sampling the counter
    # here loses the final beat -- exactly one, at both geometries (255/256
    # and 1023/1024). Give the counter that edge before reading it.
    await RisingEdge(dut.aclk)

    m = {
        'label': label, 'title': title, 'bursts': n, 'beats': n * BL_WORDS,
        't_refi': t_refi, 't_rfc': t_rfc, 'elapsed': elapsed,
        'prod': trk.prod, 'bp': trk.bp, 'starv': trk.starv, 'idle': trk.idle,
        'beats_seen': rbeats[0],
        'refs': slave.cmd_counts.get(_DC.REF, 0) - ref0,
        'max_run': max(trk.max_run, trk._run),
        'max_starv_run': trk.max_starv_run,
        'returned': len(results),
    }
    m['ready_cycles'] = m['prod'] + m['starv']    # cycles rready was high
    m['util'] = (m['prod'] / m['ready_cycles']) if m['ready_cycles'] else 0.0
    dut._log.info("=" * 66)
    dut._log.info("%s", title)
    dut._log.info("  t_refi=%d t_rfc=%d read_latency=%d strict=%s bursts=%d "
                  "beats=%d window=%.0f cyc", t_refi, t_rfc, read_latency,
                  strict_read, n, m['beats'], elapsed)
    dut._log.info("  STEADY-STATE UTIL = %d beats / %d rready-cycles = %.2f%%",
                  m['prod'], m['ready_cycles'], 100.0 * m['util'])
    dut._log.info("  R prod=%d starv(DUT bubble)=%d bp(sink)=%d idle=%d  "
                  "max_starv_run=%d REFs=%d", m['prod'], m['starv'], m['bp'],
                  m['idle'], m['max_starv_run'], m['refs'])
    return m


def _assert_read_stream_sane(m):
    assert m['returned'] == m['bursts'], (
        f"only {m['returned']}/{m['bursts']} read bursts returned -- the "
        f"stream did not complete")
    # Exact: every beat the DUT handed over, counted from t0.
    assert m['beats_seen'] == m['beats'], (
        f"R channel moved {m['beats_seen']} beats, expected exactly "
        f"{m['beats']} ({m['bursts']} bursts x {BL_WORDS} beats) -- the "
        f"stream did not deliver the traffic")
    # the sink is backtoback, so it must not be the limiter
    assert m['bp'] == 0, (
        f"sink dropped rready for {m['bp']} cycles -- this measures the "
        f"testbench, not the DUT")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_perf_read_ceiling(dut):
    """Read-throughput CEILING: refresh parked, always-ready sink, page-hit
    stream. The DUT must never drop rvalid on the sink after the pipeline
    fills -- any mid-stream starv cycle is the read datapath failing to
    sustain the stream. The R-channel mirror of the write ceiling.

    DFI_READ_LATENCY / DFI_STRICT_TIMING (env) run it under board-faithful
    read latency; at the default zero-latency loopback it exercises the ideal
    datapath.
    """
    m = await _measure_read_stream(
        dut, t_refi=0xFFFF, t_rfc=8, label="read_ceiling",
        title="READ CEILING (refresh parked, page-hit stream, b2b sink)",
        read_latency=int(os.environ.get("DFI_READ_LATENCY", "0")),
        strict_read=(os.environ.get("DFI_STRICT_TIMING", "") in ("1", "true")))
    _assert_read_stream_sane(m)
    assert m['refs'] == 0, (
        f"{m['refs']} refreshes fired inside the ceiling window -- "
        f"maintenance is not parked, so the stall count is not pure datapath")
    assert m['starv'] == 0, (
        f"DUT dropped rvalid for {m['starv']} cycles with the sink ready and "
        f"nothing to do but return read data (max run {m['max_starv_run']}) "
        f"-- the read datapath cannot sustain the stream")
    dut._log.info("PASS: read ceiling %.2f%% util, zero DUT stall cycles",
                  100.0 * m['util'])


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_pumice_core_perf_read_inflight(dut):
    """Reads in flight BEYOND the scheduling window (pumice_rd_return_ring).

    Strict DFI read timing with a LONG read latency (200 DFI cycles after
    rddata_en = 80 aclk at this TB's 2.5x DFI clock) and a page-hit stream
    into an always-ready sink. Before the ring (2026-09-08) a read occupied
    its 8-entry CAM slot from AR to R-drain, so at most 8 reads = 32 R beats
    could be in flight per ~90-cycle round trip: Little's law caps util near
    0.35 and the R channel shows the DUT starving the sink. With
    RD_RET_DEPTH=32 the CAM entry frees at issue and the ring holds the
    returns (128 beats in flight), so the stream saturates.

    Mutation check: PUMICE_RD_RET_DEPTH=8 (the old in-flight bound) must FAIL
    the floor -- a floor that does not move with the ring depth measures
    nothing.
    """
    lat = int(os.environ.get("DFI_READ_LATENCY", "200"))
    m = await _measure_read_stream(
        dut, t_refi=0xFFFF, t_rfc=8, label="read_inflight",
        title=f"READ IN-FLIGHT (strict DFI read latency {lat}, page-hit stream, b2b sink)",
        read_latency=lat, strict_read=True)
    _assert_read_stream_sane(m)
    assert m['refs'] == 0, f"{m['refs']} refreshes fired inside the window"
    # The BFM sink's rready FOLLOWS rvalid, so a DUT that runs dry shows up as
    # `idle` (both low), not `starv`; the R-channel util is blind to it. The
    # honest number is window throughput: beats moved over the whole read
    # phase in cycles. Measured 2026-09-08: RD_RET_DEPTH=32 -> 1024/1126 =
    # 0.91; RD_RET_DEPTH=8 (the old bound) -> 1024/3265 = 0.31.
    thr = m['beats'] / m['elapsed'] if m['elapsed'] else 0.0
    # Little's law, scaled by the burst width. Beats in flight = ring depth x
    # BL_WORDS over a round trip of lat/2.5 aclk, so:
    #   BL_WORDS=4 -> 32*4/80 = 1.6, clamps to 1.0. The 0.85 floor is
    #                 unchanged and the clamp itself carries ~60% of slack.
    #   BL_WORDS=1 -> 32*1/80 = 0.4. Thirty-two reads of ONE beat cannot
    #                 cover an 80-cycle round trip however well the ring
    #                 works, so a flat 0.85 is unreachable by construction.
    # NOMINAL depth on purpose -- NOT the built RD_RET_DEPTH. Deriving the
    # floor from the parameter under test would move it with the mutation and
    # PUMICE_RD_RET_DEPTH=8 would start passing.
    # Measured (board geometry, depth 32 vs 8): 0.30 vs 0.08, a 3.75x split,
    # and 0.90 at the default geometry. The fraction is 0.85 where the ideal
    # clamps and 0.60 where it does not, because in the clamped case the clamp
    # supplies the margin and in the unclamped case nothing does: that puts
    # the board floor at 0.24, which the ring clears by 25% and the mutation
    # misses by 3x.
    RD_RET_NOMINAL = 32
    ideal = min(1.0, RD_RET_NOMINAL * BL_WORDS / (lat / 2.5))
    frac = 0.85 if ideal >= 1.0 else 0.60
    floor = float(os.environ.get("READ_INFLIGHT_THR_FLOOR", f"{frac * ideal:.3f}"))
    assert thr >= floor, (
        f"read window throughput {thr:.2f} beats/cycle < {floor:.2f} floor under "
        f"{lat}-cycle read latency (window {m['elapsed']:.0f} cyc, idle={m['idle']}) "
        f"-- the controller is not keeping enough reads in flight to cover the "
        f"round trip (RD_RET_DEPTH / issue gating)")
    dut._log.info("PASS: read in-flight throughput %.2f beats/cycle at latency %d "
                  "(window %.0f cyc, idle=%d)", thr, lat, m['elapsed'], m['idle'])


async def _admit_when_ready(dut, valid_sig, ready_expr, fire_expr, n=192):
    """Of the cycles where an intake COULD admit a sub-command -- inlet valid
    AND everything downstream ready -- how often does it? Ideal is 1.0.

    Conditioning on ready is what makes this geometry-independent. A raw admit
    duty measures whatever happens to be the bottleneck (at this testbench's
    BL_WORDS=4 that is the DFI, which backpressures the intake and hides any
    intake-side throttle); conditioning removes the bottleneck from the
    measurement and leaves only the intake's own cadence.
    """
    ready = fired = 0
    while ready < n:
        await RisingEdge(dut.aclk)
        if int(valid_sig.value) and int(ready_expr.value):
            ready += 1
            fired += int(fire_expr.value)
    return fired / ready if ready else 0.0


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_perf_intake_admit_rate(dut):
    """An intake must admit a sub-command on EVERY cycle it is able to.

    One admitted sub-command is one DRAM burst, so this rate multiplies read
    bandwidth and nothing downstream can win it back. Two things conspired to
    hide a 2x read throttle here until 2026-09-10 (PUMICE-025), and the
    measurement is shaped to defeat both:

      * At this testbench's geometry one DRAM burst is BL_WORDS=4 AXI beats,
        so half-rate admission still supplies 2 beats/cycle and no bandwidth
        assertion can see it. The board runs BL4 on x16 with a 32-bit beat,
        where one burst is ONE beat and the same half rate IS the bandwidth.
      * The read intake's probe-arm bit is only consumed by an admit, so under
        downstream backpressure it sits pre-armed and the throttle disappears.
        It costs exactly when downstream is ready every cycle -- the board.

    Hence: condition on ready, and compare against the write intake, which has
    no arm stage and is the control.
    """
    _memory, _slave = await _bring_up(dut, page_policy=1)
    rd_i = dut.u_core.u_ifc.u_rd_intake
    wr_i = dut.u_core.u_ifc.u_wr_intake

    wr_task = cocotb.start_soon(_admit_when_ready(
        dut, wr_i.aw_push_valid_o, wr_i.aw_push_ready_i, wr_i.aw_push_valid_o))
    await _write_many(dut, [(_mkaddr(b % NUM_BANKS, 0x11, (b // NUM_BANKS) * BL),
                             [0xA5A5_0000 + b] * BL_WORDS) for b in range(256)])
    wr_rate = await with_timeout(wr_task, 20, 'ms')

    rd_task = cocotb.start_soon(_admit_when_ready(
        dut, rd_i.fub_arvalid, rd_i.w_can_admit, rd_i.w_admit))
    await _read_many(dut, [_mkaddr(b % NUM_BANKS, 0x11, (b // NUM_BANKS) * BL)
                           for b in range(256)])
    rd_rate = await with_timeout(rd_task, 20, 'ms')

    dut._log.info("admit-when-ready: WRITE %.3f, READ %.3f", wr_rate, rd_rate)
    assert wr_rate >= 0.98, (
        f"write intake admitted on only {wr_rate:.3f} of the cycles it was "
        f"able to -- the control is broken, so the read number is not "
        f"interpretable")
    assert rd_rate >= 0.98, (
        f"read intake admitted on only {rd_rate:.3f} of the cycles it was able "
        f"to (write intake: {wr_rate:.3f}). One sub-command is one DRAM burst, "
        f"so a downstream that can accept every cycle -- which is the board at "
        f"BL4/x16 -- gets {rd_rate:.2f}x the DRAM read rate and no more")
    dut._log.info("PASS: read intake admits %.3f of available cycles", rd_rate)


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_perf_write_ceiling(dut):
    """Write-throughput CEILING: refresh parked, so nothing but the write
    datapath can deassert wready. Establishes the reference the frequent-
    refresh run is measured against."""
    m = await _measure_write_stream(
        dut, t_refi=0xFFFF, t_rfc=8, label="write_ceiling",
        title="WRITE CEILING (refresh parked, page-hit stream, b2b)")
    _assert_stream_sane(m)
    assert m['refs'] == 0, (
        f"{m['refs']} refreshes fired inside the ceiling window -- "
        f"maintenance is not actually parked, so the stall count is not "
        f"purely datapath")
    # WRITE DATA MUST LEAD (2026-09-09): the DFI write-staged token is an
    # invariant, not a throttle. A WR held at the DFI head for lack of data
    # stalls the in-order command stream and compresses the spacing behind it.
    held = int(dut.u_core.u_dfi.u_cmd.r_wr_held_cnt.value)
    held_max = int(dut.u_core.u_dfi.u_cmd.r_wr_held_max.value)
    dut._log.info("write-staged gate: held %d cycles total, longest hold %d", held, held_max)
    assert held == 0, (
        f"a WR was held at the DFI for {held} cycles (longest {held_max}) waiting "
        f"for its data -- the command reached the DFI before the data (CMD_DELAY "
        f"too small or the WR commit not rate-matched)")
    # Bounded by a CONSTANT tied to the opening row activations, not by the
    # stream length: at most one short resync per bank opened. Measured 0 at
    # the default geometry and 2 at board geometry, unchanged from n=256 to
    # n=1024. A real inability to sustain the stream stalls every burst and
    # blows this by an order of magnitude.
    bp_budget = 2 * NUM_BANKS
    assert m['bp'] <= bp_budget, (
        f"DUT stalled the W channel for {m['bp']} cycles (budget {bp_budget}; "
        f"{m['bp_open']} during the opening bursts, {m['bp_steady']} after, "
        f"max run {m['max_bp_run']}) with NOTHING to do but move write data "
        f"-- the datapath itself cannot sustain the stream")
    dut._log.info("PASS: ceiling %.2f%% utilization, %d DUT stall cycles "
                  "(%d opening / %d after)",
                  100.0 * m['util'], m['bp'], m['bp_open'], m['bp_steady'])


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_perf_refresh_bubbles(dut):
    """Same stream, refresh cranked up -- refresh should punch visible
    bubbles into the write handshake.

    This is the CEILING TEST'S POSITIVE CONTROL as much as it is a refresh
    measurement. With maintenance parked the DUT never stalls, so
    `assert bp == 0` passing proves nothing about whether the instrument
    could see a stall at all. Here refresh is the only thing changed, and
    the accounting has to register it: REFs appear, wready drops, and
    utilization falls below the ceiling. If this test ever reports 100%,
    the ceiling number is not trustworthy either.

    tREFI is poked to 64 cycles (vs the JEDEC-scaled 0x400 used elsewhere)
    purely to get many bubbles inside a short window -- this measures the
    SHAPE of the refresh penalty, not a JEDEC-legal operating point.
    """
    T_REFI, T_RFC = 64, 8
    m = await _measure_write_stream(
        dut, t_refi=T_REFI, t_rfc=T_RFC, label="refresh_bubbles",
        title=f"REFRESH BUBBLES (t_refi={T_REFI} t_rfc={T_RFC}, same stream)")
    _assert_stream_sane(m)

    # 1. the bubbles are actually there
    assert m['refs'] > 0, (
        f"no refresh fired in {m['elapsed']:.0f} cycles with t_refi={T_REFI} "
        f"-- the tREFI poke did not take, so this run does not control "
        f"anything")
    # 2. the instrument SEES them -- this is what the ceiling test cannot prove
    assert m['bp'] > 0, (
        f"{m['refs']} refreshes fired but the W channel never stalled a "
        f"single cycle. Either refresh is free (it is not) or the stall "
        f"accounting is blind -- in which case the ceiling test's "
        f"`bp == 0` is vacuous")
    assert m['util'] < 1.0, (
        f"utilization {100.0 * m['util']:.2f}% with {m['refs']} refreshes in "
        f"the window -- refresh cannot be free")
    # 3. the stalls look like refresh, not like scattered noise: each bubble
    #    should be a contiguous run, and there should not be wildly more
    #    bubbles than refreshes.
    #    Attribute on the refresh-SIZED runs, not on the raw run count. A
    #    refresh bubble is a long contiguous stall -- 29 cycles at the default
    #    geometry, 31 at board. At BL_WORDS=1 supply and drain are exactly
    #    rate-matched, so the stream ALSO throws short resync runs that have
    #    nothing to do with refresh: measured hist={1:8, 2:9, 3:8, 4:8, 31:8},
    #    i.e. eight refresh bubbles and 33 pieces of 1-4 cycle noise. Counting
    #    runs made that read as "41 runs for 10 refreshes" and failed, while
    #    the eight long runs carry 248 of the 330 stalled cycles. The default
    #    geometry sees hist={11:1, 29:25} and is unaffected either way.
    long_runs = [(c, k) for c, k in m['stall_hist'].items() if c >= T_RFC]
    n_long = sum(k for _, k in long_runs)
    cyc_long = sum(c * k for c, k in long_runs)
    assert n_long <= m['refs'] * 3, (
        f"{n_long} refresh-sized stall runs (>= tRFC={T_RFC}) for only "
        f"{m['refs']} refreshes -- the bubbles are not attributable to "
        f"refresh. Full run histogram: {m['stall_hist']}")
    #    and they must be where the stalled time actually went, or "attributed
    #    to refresh" is a label on a minority of the cost.
    assert cyc_long >= 0.5 * m['bp'], (
        f"refresh-sized runs carry only {cyc_long} of {m['bp']} stalled "
        f"cycles -- most of the stall is NOT refresh. Histogram: "
        f"{m['stall_hist']}")

    dut._log.info("PASS: %d refreshes cost %d W-stall cycles in %d stall runs "
                  "(max %d) -- utilization %.2f%% vs 100%% parked",
                  m['refs'], m['bp'], m['stall_runs'], m['max_bp_run'],
                  100.0 * m['util'])


# Axis-2 paging modes (pumice_page_policy.sv:106-113).
_PAGE_MODES = [(0, "build_default"), (1, "static_open"), (2, "static_close"),
               (3, "fixed_open"),    (4, "adapt_time"),  (5, "adapt_access"),
               (6, "rbl_static"),    (7, "rbl_dyn")]


# TASK-006 stall attribution, read straight off the DUT. The seven counters are
# a PRIORITY classification of every cycle the arbiter did not fire, so they sum
# to the stalled-cycle count and each cycle is charged exactly once. Free-running
# since reset, so a window is (end - start).
_STALL_FIELDS = ("bp", "refresh", "turnaround", "tccd", "actlimit",
                 "banktimer", "noreq")


def _stall_snap(dut):
    """Snapshot the seven stall counters + the DUT's own page stats."""
    d = {f: int(getattr(dut, f"stall_{f}").value) for f in _STALL_FIELDS}
    for f in ("page_hit", "page_miss", "page_empty", "act", "pre", "ref"):
        d[f] = int(getattr(dut, f"stat_{f}").value)
    return d


def _stall_delta(a, b):
    return {k: b[k] - a[k] for k in a}


def _stall_str(d):
    tot = sum(d[f] for f in _STALL_FIELDS)
    if tot == 0:
        return "no stalled cycles"
    parts = [f"{f}={d[f]}({100.0*d[f]/tot:.1f}%)"
             for f in _STALL_FIELDS if d[f]]
    return f"stalled={tot}  " + " ".join(parts)


async def _util_window(dut, slave, *, tag, n=192, banks=None):
    """One measured write window on the CURRENT mode settings.

    Returns (utilization, backpressure_cycles, refs, max_run, beats).

    Utilization is beats / cycles WVALID was high -- cycles where the master
    had nothing to offer are excluded, so the only way to fall below 100% is
    the DUT refusing data.

    `max_run` is the LONGER claim and the one that matters for streaming:
    the longest unbroken stretch of `wvalid && wready`. 100% utilization
    only says the DUT never refused; it does NOT say the beats arrived
    contiguously -- a stream chopped into many short runs still reads 100%.
    W must give data BACK TO BACK, so callers compare max_run against the
    beat count. See [[structure-trackers]].

    Each window uses its OWN address region (keyed off `tag`) so page state
    from the previous mode cannot flatter or penalise the next one.
    """
    from tbclasses.trackers import AxiChanTracker
    from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand as _DC

    trk = AxiChanTracker(dut, 'w', valid="s_axi_wvalid", ready="s_axi_wready",
                         last="s_axi_wlast", log=dut._log)
    task = cocotb.start_soon(trk.run())
    base = (trk.prod, trk.bp)
    ref0 = slave.cmd_counts.get(_DC.REF, 0)
    cmd0 = {c: slave.cmd_counts.get(c, 0) for c in (_DC.ACT, _DC.PRE, _DC.WR)}
    stall0 = _stall_snap(dut)

    #  = how many banks the stream spreads over. Bank parallelism is
    # what hides ACT/PRE latency, so the 1-bank case is where paging modes
    # that precharge per access actually show their cost.
    nb = banks or NUM_BANKS
    rng = random.Random(0x5EED + tag)
    reqs = [(_mkaddr(k % nb, 0x20 + tag, (k // nb) * BL),
             [rng.randrange(1 << DW) for _ in range(BL_WORDS)])
            for k in range(n)]
    await _write_many(dut, reqs)
    await ClockCycles(dut.aclk, 40)          # let the tail drain
    task.kill()

    prod, bp = trk.prod - base[0], trk.bp - base[1]
    valid_cyc = prod + bp
    max_run = max(trk.max_run, trk._run)
    # Commands per ACCESS on the DFI command bus. The arbiter issues at most
    # ONE command per cycle, so this is the hard ceiling on beats/cycle:
    #     ceiling = BL_WORDS / commands_per_access
    # At BL_WORDS=4 a 3-command close-page access still clears 1.0 and every
    # mode can read 100%. At BL_WORDS=1 it cannot -- which is why the flat
    # "every mode is 100%" held at the default geometry and not on the board.
    cmds = {c: slave.cmd_counts.get(c, 0) - cmd0[c] for c in cmd0}
    per_access = sum(cmds.values()) / n if n else 0.0
    stalls = _stall_delta(stall0, _stall_snap(dut))
    return ((prod / valid_cyc) if valid_cyc else 0.0, bp,
            slave.cmd_counts.get(_DC.REF, 0) - ref0,
            max_run, n * BL_WORDS, cmds, per_access, stalls)


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_pumice_core_perf_paging_sweep(dut):
    """TASK-002: 100% write utilization under EVERY Axis-2 paging mode.

    The goal (Sean, 2026-08-28): "ensure 100% utilization for all paging
    programming." So this sweeps all 8 modes over an identical page-hit
    stream with refresh parked, and reports utilization per mode.

    One bring-up, then the mode is re-programmed between windows -- the
    modes are runtime CSRs by design (that is what TASK-001 delivered),
    and re-running bring-up per mode would restart the clocks.

    A mode below 100% is not automatically a bug: static_close forces an
    auto-precharge on every access, so whether the write channel still
    sustains full rate depends on whether the controller overlaps ACT/PRE
    across banks. That is exactly the number this test exists to report.
    """
    _memory, slave = await _bring_up(dut, page_policy=0)      # OPEN

    # park refresh for the whole sweep -- isolate paging as the variable
    dut.t_refi_i.value       = 0xFFFF
    dut.ref_postpone_i.value = 0
    dut.ref_pullin_i.value   = 0
    dut.ref_mode_i.value     = 0
    # Force the tREFI counter to pick up the new interval NOW. It otherwise
    # reloads only on expiry, so the already-armed interval from bring-up
    # would run first -- which is why this used to burn ~1100 idle cycles and
    # still leaked a stale refresh into the measurement window.
    dut.refi_reload_i.value = 1
    await ClockCycles(dut.aclk, 2)
    dut.refi_reload_i.value = 0
    await ClockCycles(dut.aclk, 2)

    # TWO spreads per mode. With 8-way bank rotation every mode reads 100%,
    # so that column ALONE is a green light that cannot turn red -- the
    # single-bank column is what discriminates (measured 2026-08-29:
    # static_close and rbl_static collapse to 27.68% there, both because they
    # precharge per access).
    rows, cpa_rows = [], []
    for tag, (mode, name) in enumerate(_PAGE_MODES):
        dut.page_mode_i.value = mode
        await ClockCycles(dut.aclk, 64)       # settle + drain before measuring
        u8, bp8, r8, run8, beats8, cmds8, cpa8, st8 = await _util_window(
            dut, slave, tag=tag)
        await ClockCycles(dut.aclk, 64)
        u1, bp1, r1, run1, _, _, cpa1, st1 = await _util_window(
            dut, slave, tag=tag + 64, banks=1)
        rows.append((mode, name, u8, bp8, u1, bp1, r8 + r1, run8, beats8))
        cpa_rows.append((name, cpa8, cpa1, dict(cmds8)))
        dut._log.info("paging mode %d (%-13s): 8bank=%6.2f%% (stall %d)  "
                      "1bank=%6.2f%% (stall %d)  REF=%d  cmds/access=%.2f "
                      "(ceiling %.1f%%)",
                      mode, name, 100.0 * u8, bp8, 100.0 * u1, bp1, r8 + r1,
                      cpa8, 100.0 * min(1.0, BL_WORDS / max(cpa8, 1e-9)))
        # WHY the mode sits where it does -- a priority split of every
        # non-firing cycle, read from the DUT's own TASK-006 counters.
        dut._log.info("    8bank %s", _stall_str(st8))
        dut._log.info("    1bank %s", _stall_str(st1))

    try:
        with open("paging_util_sweep.out", "w") as f:
            f.write("# TASK-002: write utilization per Axis-2 paging mode\n")
            f.write("# refresh parked, page-hit stream, writes only, AW+W b2b\n")
            f.write("# util = beats / cycles WVALID high (100% = DUT never stalled)\n\n")
            f.write("# TWO bank spreads: 8-way rotation hides ACT/PRE, so that\n")
            f.write("# column alone cannot fail. 1-bank is the discriminator.\n\n")
            f.write(f"| {'mode':>4} | {'name':<13} | {'8bank%':>7} | {'stall':>6} "
                    f"| {'1bank%':>7} | {'stall':>6} | {'REF':>3} |\n")
            f.write(f"|{'-'*6}|{'-'*15}|{'-'*9}|{'-'*8}|{'-'*9}|{'-'*8}|{'-'*5}|\n")
            for mode, name, u8, bp8, u1, bp1, refs, _, _ in rows:
                f.write(f"| {mode:>4} | {name:<13} | {100.0*u8:>7.2f} | {bp8:>6} "
                        f"| {100.0*u1:>7.2f} | {bp1:>6} | {refs:>3} |\n")
            f.write("\n# back-to-back check: longest unbroken wvalid&&wready run\n")
            f.write("# vs total beats, 8-bank spread (equal = one contiguous stream)\n")
            for _, name, _, _, _, _, _, run, beats in rows:
                f.write(f"{name:<13} max_run={run:<6} beats={beats}\n")
    except Exception as e:                                    # noqa: BLE001
        # LOUD on purpose: a swallowed unpack error here once emptied the
        # table body while the test still reported PASS. The dump is the
        # deliverable, so a broken dump is a failure, not a warning.
        raise AssertionError(f"paging_util_sweep.out dump failed: {e!r}") from e

    # refresh must not have leaked into ANY window, or the numbers are not
    # attributable to paging.
    leaked = [(n, r) for _, n, _, _, _, _, r, _, _ in rows if r]
    assert not leaked, f"refresh fired during paging windows: {leaked}"

    # The arbiter issues at most ONE DFI command per cycle, so no mode can
    # exceed BL_WORDS / commands_per_access beats per cycle. At BL_WORDS=4 even
    # a 2-command close-page access clears 1.0, so "every mode reads 100%" is
    # reachable and is still required exactly. At BL_WORDS=1 (the board) an
    # access that costs more than one command CANNOT reach 100% -- measured
    # cmds/access 1.04 for the open modes and 2.04 for close -- so there the
    # claim is made against the ceiling instead. The strict default-geometry
    # gate is unchanged; this only adds a check where none was possible.
    cpa_by_name = {nm: c8 for nm, c8, _, _ in cpa_rows}
    short8, below_ceiling = [], []
    for _, nm, u, _, _, _, _, _, _ in rows:
        cpa = cpa_by_name.get(nm, 1.0)
        ceil = min(1.0, BL_WORDS / cpa) if cpa > 0 else 1.0
        if ceil >= 1.0:
            if u < 1.0:
                short8.append((nm, round(100.0 * u, 2)))
        # 0.85 of the ceiling: cmds/access is counted over a slightly wider
        # window than utilization (it includes the tail drain), so it
        # over-counts a few percent -- the open modes measure 98.97% against a
        # computed 96.0% ceiling. The margin covers that, not a shortfall.
        elif u < 0.85 * ceil:
            below_ceiling.append((nm, round(100.0 * u, 2),
                                  round(100.0 * ceil, 1), round(cpa, 2)))
    assert not short8, (
        f"paging modes below 100% write utilization WITH bank parallelism: "
        f"{short8}. With 8-way rotation and refresh parked nothing should "
        f"stall the write channel.")
    # ACCEPTED, with a floor. The close-page family reaches ~63% of its own
    # command-bus ceiling because every access pays ACT + column and the
    # ACT->column path is 8 aclk against tRCD 3 -- pick-pipeline and
    # bank-timer flop stages. Sean 2026-09-22 ruled those by design
    # (ISSUE-001), and the outstanding dial does not reach it: board measures
    # static_close flat at 33.9 MB/s across OS 8/16/32. So a mode sitting at
    # its measured point is NOT a failure; a mode sitting BELOW it is.
    #
    # 0.55 x ceiling. Measured ratios, board geometry, 2026-09-24:
    #     static_close  30.77 / 49.0 = 0.628   <- the worst, and the binding one
    #     rbl_static    30.77 / 49.0 = 0.628
    #     rbl_dyn       41.56 / 61.0 = 0.681
    # so 0.55 sits ~12% under the worst and still catches a step change rather
    # than a few percent of drift. The ratios are REPORTED either way.
    #
    # This comment used to quote 0.53 for rbl_dyn, which was its PRE-fix ratio
    # (32.32/61.0): the classify-gate fix moved it to 41.56 and nobody updated
    # the rationale. Left as it was, the next person tuning this floor would
    # think rbl_dyn was the worst case and set it against a mode that has since
    # improved by 29%.
    ACCEPTED_CEILING_FRAC = 0.55
    regressed = [r for r in below_ceiling if r[1] < ACCEPTED_CEILING_FRAC * r[2]]
    if below_ceiling:
        print(f"[paging] below command-bus ceiling (accepted, ISSUE-002): "
              f"{below_ceiling}")
    assert not regressed, (
        f"paging modes below the ACCEPTED close-page floor "
        f"({ACCEPTED_CEILING_FRAC:.0%} of their command-bus ceiling): "
        f"{regressed}. The ~63% shortfall itself is accepted (ISSUE-002, "
        f"pipeline flop stages, by design per ISSUE-001) -- this floor exists "
        f"to catch a step change below it, so a hit here is a real regression.")

    # The 1-bank column is REPORTED, and only its floor is asserted: modes
    # that precharge per access are EXPECTED to cost throughput there. The
    # guard catches a collapse far worse than the known ~28%, which would
    # mean something beyond the extra ACT/PRE.
    # 0.20 was measured at BL_WORDS=4 ("per-access precharge explains ~28%").
    # At BL_WORDS=1 one access carries one beat, so the same behaviour reads
    # ~5-7%: board measures static_close/rbl_static at 5.85%.
    FLOOR = 0.20 * GEOM_UTIL_SCALE
    bad1 = [(n, round(100.0 * u, 2)) for _, n, _, _, u, _, _, _, _ in rows if u < FLOOR]
    assert not bad1, (
        f"paging modes below {FLOOR:.0%} even for single-bank traffic: {bad1}. "
        f"Per-access precharge explains ~28%; anything under {FLOOR:.0%} is a "
        f"different problem.")
    # W MUST GIVE DATA BACK TO BACK. 100% utilization only says the DUT never
    # refused a beat; it does not say the beats were contiguous. With bank
    # parallelism the whole burst stream should land as ONE unbroken run.
    # ONE unbroken run is only reachable with headroom. At BL_WORDS=4 a burst
    # carries 4 beats per command, so the DUT re-absorbs a bubble and the whole
    # stream lands contiguous -- that is the claim, and it stays exact there.
    # At BL_WORDS=1 one AXI beat IS one DRAM burst and tCCD is 1, so supply and
    # drain are exactly rate-matched: every resync splits the run and the
    # longest one cannot reach `beats` however well the datapath behaves.
    # Board measures 148/192 for the open modes.
    #
    # The auto-precharge modes are exempted rather than scaled: they issue
    # ACT + column per access, so at one beat per access there is no stream to
    # be contiguous -- they measure 31/192, and a fraction that admitted that
    # would admit anything.
    AP_MODES = {"static_close", "rbl_static", "rbl_dyn"}
    RUN_FRAC = 1.0 if GEOM_UTIL_SCALE >= 1.0 else 0.70
    chopped = [(n, run, beats) for _, n, _, _, _, _, _, run, beats in rows
               if run < RUN_FRAC * beats
               and not (GEOM_UTIL_SCALE < 1.0 and n in AP_MODES)]
    assert not chopped, (
        f"W data not back-to-back with bank parallelism (mode, max_run, "
        f"beats; need >= {RUN_FRAC:.0%} of beats): {chopped}. A stream chopped "
        f"into short runs can still read 100% utilization -- max_run is the "
        f"claim that catches it.")

    spread = [(n, round(100.0 * u8, 1), round(100.0 * u1, 1))
              for _, n, u8, _, u1, _, _, _, _ in rows if u1 < 0.99]
    dut._log.info("PASS: all %d modes 100%% with bank parallelism; modes that "
                  "pay for single-bank traffic (mode, 8bank%%, 1bank%%): %s",
                  len(rows), spread)


# Axis-1 scheduling knobs (pumice_cmd_arbiter.sv:64-77). Each entry is one
# NON-DEFAULT setting; encoding 0 is the build default, covered by the
# "default" row. order_mode 2 is unused in the RTL (only 1 and 3 decode).
_SCHED_SETTINGS = [
    ("default",        {}),
    ("order_in_order", {'sched_order_mode_i': 1}),
    ("order_age_thr",  {'sched_order_mode_i': 3}),
    ("row_most_pend",  {'sched_row_sel_i': 1}),
    ("row_fewest",     {'sched_row_sel_i': 2}),
    ("col_most_pend",  {'sched_col_sel_i': 1}),
    ("col_fewest",     {'sched_col_sel_i': 2}),
    ("pref_row_first", {'sched_access_pref_i': 2}),
    ("pref_pre_first", {'sched_access_pref_i': 3}),
    ("qos_en",         {'sched_qos_en_i': 1}),
]

_SCHED_KNOBS = ('sched_order_mode_i', 'sched_row_sel_i', 'sched_col_sel_i',
                'sched_access_pref_i', 'sched_qos_en_i')


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_pumice_core_perf_paging_sched_cross(dut):
    """TASK-002: 100% write utilization across ALL paging x ALL scheduling.

    The second half of the goal (Sean, 2026-08-28): "ensure 100% utilization
    for all paging programming. Then all paging and all scheduling."

    Every Axis-2 paging mode (8) crossed with every Axis-1 scheduling setting
    (10 -- the build default plus each non-default value of order_mode,
    row_sel, col_sel, access_pref and qos_en). Refresh parked, page-hit
    stream, writes only, AW+W back-to-back, 8-way bank rotation.

    Knobs are swept ONE AT A TIME against the default rather than as a full
    Cartesian product: 8 x 3 x 3 x 3 x 3 would be 648 windows for little
    extra information, since these compose by narrowing WHO is a candidate
    rather than interacting. A full product belongs in the characterization
    sweep (TASK-002 proper), not in a pass/fail gate.

    NOTE this is the 8-bank spread, which is the "should be 100%" gate. The
    paging sweep's 1-bank column is what exposes cost differences between
    modes; see paging_util_sweep.out.
    """
    _memory, slave = await _bring_up(dut, page_policy=0)      # OPEN

    dut.t_refi_i.value       = 0xFFFF
    dut.ref_postpone_i.value = 0
    dut.ref_pullin_i.value   = 0
    dut.ref_mode_i.value     = 0
    dut.refi_reload_i.value  = 1
    await ClockCycles(dut.aclk, 2)
    dut.refi_reload_i.value  = 0
    await ClockCycles(dut.aclk, 4)

    rows, tag = [], 0
    for mode, pname in _PAGE_MODES:
        for sname, sched in _SCHED_SETTINGS:
            dut.page_mode_i.value = mode
            for k in _SCHED_KNOBS:          # reset every knob, then apply
                getattr(dut, k).value = 0
            for k, v in sched.items():
                getattr(dut, k).value = v
            await ClockCycles(dut.aclk, 64)
            tag += 1
            util, bp, refs, run, beats, _cmds, cpa, _st = await _util_window(
                dut, slave, tag=tag, n=96)
            rows.append((pname, sname, util, bp, refs, run, beats, cpa))
            if util < 1.0 or refs:
                dut._log.warning("%-13s x %-14s: util=%6.2f%% stall=%d REF=%d",
                                 pname, sname, 100.0 * util, bp, refs)

    try:
        with open("paging_sched_cross.out", "w") as f:
            f.write("# TASK-002: write utilization, ALL paging x ALL scheduling\n")
            f.write("# refresh parked, page-hit stream, writes only, AW+W b2b,\n")
            f.write("# 8-way bank rotation. util = beats / cycles WVALID high.\n\n")
            f.write("| {:<13} | {:<14} | {:>7} | {:>6} | {:>3} |\n".format(
                "paging", "scheduling", "util%", "stall", "REF"))
            f.write("|{}|{}|{}|{}|{}|\n".format(
                "-" * 15, "-" * 16, "-" * 9, "-" * 8, "-" * 5))
            for pn, sn, u, bp, r, _, _, _ in rows:
                f.write("| {:<13} | {:<14} | {:>7.2f} | {:>6} | {:>3} |\n".format(
                    pn, sn, 100.0 * u, bp, r))
    except Exception as e:                                    # noqa: BLE001
        dut._log.warning("paging_sched_cross.out dump failed: %s", e)

    leaked = [(p_, s_, r) for p_, s_, _, _, r, _, _, _ in rows if r]
    assert not leaked, "refresh fired during cross windows: {}".format(leaked[:5])

    # order_in_order is EXPECTED to cost throughput and is excluded from the
    # 100% gate: it forces strict in-order issue, which disables the very
    # out-of-order bank-parallel picking that hides ACT/PRE. Trading
    # bandwidth for ordering is the mode's purpose. Measured 2026-08-29:
    #   open-page modes                    89.30%  (46 stall cycles)
    #   rbl_dyn                            66.90%  (190)
    #   static_close / rbl_static          56.30%  (298)
    # It compounds with the precharge-per-access modes, which is why those
    # fall furthest. EVERY other setting is 100% under EVERY paging mode.
    ORDERED = "order_in_order"
    # pref_row_first (ACT beats COL) is likewise an intended trade under the
    # close-biased paging modes ONLY: every access needs its own ACT, so an
    # ACT-ready entry keeps taking the one cycle in tCCD (4 at BL8) when the
    # next column becomes eligible, and the column slides one cycle -- a
    # 5-cycle period, 4/5 = 80%. Under the open-page modes no ACT competes
    # and the row stays 100%. It measured 100% only while this test poked
    # the unphysical tCCD=1 (a column eligible every cycle cannot lose its
    # slot); the physical tCCD exposed the cost (2026-09-09, PUMICE-021).
    ROW_FIRST = "pref_row_first"
    # 0.75 is the BL_WORDS=4 number: ACT-over-COL costs one column slot in
    # five there (a 5-cycle period, 4/5 = 80%). At BL_WORDS=1 an access is ONE
    # column and one ACT, so under row_first they alternate and the column can
    # win at most every other slot -- a ~50% ceiling by construction, not a
    # stall. Board measures 43.05% (static_close, rbl_static) and 47.52%
    # (rbl_dyn) against that ceiling.
    ROW_FIRST_FLOOR = 0.75 if GEOM_UTIL_SCALE >= 1.0 else 0.40
    # Same command-bus ceiling as the paging sweep: one DFI command per cycle
    # caps beats/cycle at BL_WORDS / commands_per_access. At BL_WORDS=4 that
    # is >= 1.0 for every combination here, so the exact-100% claim stands
    # unchanged. At BL_WORDS=1 a combination whose paging mode precharges per
    # access cannot reach it, and demanding 100% there measures the geometry.
    short, short_ceil = [], []
    for p_, s_, u, _, _, _, _, cpa in rows:
        if s_ in (ORDERED, ROW_FIRST):
            continue
        ceil = min(1.0, BL_WORDS / cpa) if cpa > 0 else 1.0
        if ceil >= 1.0:
            if u < 1.0:
                short.append((p_, s_, round(100.0 * u, 2)))
        elif u < 0.85 * ceil:
            short_ceil.append((p_, s_, round(100.0 * u, 2),
                               round(100.0 * ceil, 1)))
    assert not short, (
        "{} of {} paging x scheduling combinations below 100% write "
        "utilization: {}. With bank parallelism and refresh parked, no "
        "scheduling policy except {} should stall the write channel.".format(
            len(short), len(rows), short[:10], ORDERED))
    # Same accepted floor as the paging sweep -- see ISSUE-002 there.
    ACCEPTED_CEILING_FRAC = 0.55
    sc_regressed = [r for r in short_ceil if r[2] < ACCEPTED_CEILING_FRAC * r[3]]
    if short_ceil:
        print(f"[sched_cross] below command-bus ceiling (accepted, "
              f"ISSUE-002): {len(short_ceil)} of {len(rows)}")
    assert not sc_regressed, (
        "{} of {} combinations below the ACCEPTED close-page floor ({:.0%} of "
        "their command-bus ceiling): {}. The shortfall itself is accepted; "
        "this catches a step change below it.".format(
            len(sc_regressed), len(rows), ACCEPTED_CEILING_FRAC,
            sc_regressed[:10]))

    # ...but in_order must still be REPORTED and floored, so a regression that
    # tanks it further is caught rather than excused by the exemption.
    # in_order floors, SPLIT BY MECHANISM. Measured on this exact window with
    # a command-cadence probe (2026-09-09, PUMICE-021):
    #   non-AP paging: one ACT per row, then a column every tCCD. ONE command
    #     per access, every gap 4 cycles -> 80-90%.
    #   AP paging (static_close, rbl_*): every access is ACT + column-with-
    #     auto-precharge, TWO DEPENDENT commands. ACT->col is tRCD (gap 4);
    #     col->next ACT is the head advancing through the arbiter's 3-stage
    #     pick pipeline (gap 8). A 12-cycle period instead of 4 -> ~1/3 the
    #     utilization. Probe: static_open ops={ACT:8, WR:64} gaps 4x63/8x8 at
    #     89.5%; static_close ops={ACT:26, WRA:26} gaps 4x25/8x34 at 36.9%.
    # Under FR-FCFS other banks' entries fill those gaps (hence the 100% gate
    # above); strict ordering cannot, so this is the honest cost of the mode,
    # not a stall defect. The old blanket 0.45 floor and its "expected ~56.3%"
    # note predate the pipelined arbiter, which is why every AP mode sat just
    # under it. Shortening the col->ACT head-advance would lift these numbers
    # and is a performance item, not a correctness one.
    AP_PAGING = {"static_close", "rbl_static", "rbl_dyn"}
    # Geometry-scaled for the same reason as the single-bank floor: these are
    # beats-per-access numbers. Board (BL_WORDS=1) measures 23.47% against the
    # 0.75 tuned at BL_WORDS=4, and 11.64% against the 0.30 -- both comfortably
    # above the scaled floors, both far below the unscaled ones.
    FLOOR_AP = 0.30 * GEOM_UTIL_SCALE
    FLOOR_NOAP = 0.75 * GEOM_UTIL_SCALE
    io = [(p_, round(100.0 * u, 2)) for p_, s_, u, _, _, _, _, _ in rows if s_ == ORDERED]
    assert io, "in_order rows missing -- the exemption would hide everything"
    assert AP_PAGING.issubset({p_ for p_, _ in io}), (
        "the AP-driving paging modes are missing from the in_order rows: "
        "{}".format(sorted({p_ for p_, _ in io})))
    low = [(p_, v, FLOOR_AP if p_ in AP_PAGING else FLOOR_NOAP) for p_, v in io
           if v / 100.0 < (FLOOR_AP if p_ in AP_PAGING else FLOOR_NOAP)]
    assert not low, (
        "in_order below its floor (mode, measured%, floor): {}. Ordering costs "
        "bandwidth by design -- two dependent commands per access under the "
        "auto-precharge modes, one under the rest -- but not this much.".format(low))
    rf = [(p_, round(100.0 * u, 2)) for p_, s_, u, _, _, _, _, _ in rows if s_ == ROW_FIRST]
    assert rf, "pref_row_first rows missing -- the exemption would hide everything"
    low = [x for x in rf if x[1] / 100.0 < ROW_FIRST_FLOOR]
    assert not low, (
        "pref_row_first below the {:.0%} floor: {}. ACT-over-COL costs one "
        "column slot in five under the close-biased modes, not more.".format(
            ROW_FIRST_FLOOR, low))
    dut._log.info("PASS: %d of %d combinations at 100%%; in_order (exempt, "
                  "trades bandwidth for ordering) at %s; pref_row_first "
                  "(exempt under close-biased paging) at %s",
                  len(rows) - len(io) - len(rf), len(rows), io, rf)


def _echo_seed(tag):
    # PUMICE-019: pytest shows captured stdout for FAILING tests, so a
    # one-off red is reproducible with SEED=<n> after the fact.
    sd = os.environ.get('SEED', str(random.randint(0, 100000)))
    print(f"[seed] {tag} SEED={sd}")
    return sd


def _run(request, testcase, params_over=None, enhanced=False):
    # enhanced=True builds the arbiter with +define+PUMICE_ENHANCED so the
    # in_order / age_threshold order-mode overlays are present. Basic pumice
    # (the board build + every FR-FCFS test) leaves them compiled out, which is
    # what lets the board close timing; only tests that actually drive
    # order_mode != 0 need the enhanced arbiter.
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_core_tb_top"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    # The enhanced and base builds of one testcase are different netlists;
    # give them separate build trees so they cannot race (a shared tree
    # produced a g++ segfault when both compiled at once, 2026-09-09).
    sim_build = sim_build_path(tests_dir, testcase + ("" if enhanced else "_base"))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
              "COL_WIDTH": str(COL_WIDTH), "DFI_RATE": str(DFI_RATE),
              "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "DRAM_BL": str(BL),
              "DRAM_DEVICE_WIDTH": str(DRAM_DEV_W),
              "NUM_ENTRIES": os.environ.get("PUMICE_NUM_ENTRIES", "8"),
              "N_SRAM_SLOTS": os.environ.get("PUMICE_NUM_ENTRIES", "8"),
              "RD_RET_DEPTH": os.environ.get("PUMICE_RD_RET_DEPTH", "32")}
    if params_over:
        params.update(params_over)
    tag = testcase + ("" if enhanced else "_base")
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{tag}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
                 "SEED": _echo_seed(tag),
                 "TEST_LEVEL": _LEVEL}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=(["+define+USE_ASYNC_RESET"]
                      + (["+define+PUMICE_ENHANCED"] if enhanced else [])
                      + ["--public-flat-rw", "--assert"]),
        waves=(os.environ.get("WAVES", "0") == "1"),
        plus_args=(["--trace"] if os.environ.get("WAVES", "0") == "1" else []),
        keep_files=True, timescale="1ns/1ps")


def test_pumice_core_dfi(request):   _run(request, "cocotb_test_pumice_core_dfi")
def test_pumice_core_fixed_open(request):
    _run(request, "cocotb_test_pumice_core_fixed_open")






def test_pumice_core_refresh_credit(request):
    _run(request, "cocotb_test_pumice_core_refresh_credit")


def test_pumice_core_sched_order(request):
    _run(request, "cocotb_test_pumice_core_sched_order", enhanced=True)
def test_pumice_core_sched_order_base(request):
    # BASE build (no PUMICE_ENHANCED): in_order is per-channel FIFO and
    # age_threshold uses the CAMs' registered flags (2026-09-09). Same
    # parked-victim sweep, so the base bitstream's order modes are covered.
    _run(request, "cocotb_test_pumice_core_sched_order", enhanced=False)


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
def test_pumice_core_perf_read_ceiling(request):
    _run(request, "cocotb_test_pumice_core_perf_read_ceiling")
def test_pumice_core_perf_intake_admit_rate(request):
    _run(request, "cocotb_test_pumice_core_perf_intake_admit_rate")
def test_pumice_core_perf_write_ceiling(request):
    _run(request, "cocotb_test_pumice_core_perf_write_ceiling")
def test_pumice_core_perf_read_inflight(request):
    _run(request, "cocotb_test_pumice_core_perf_read_inflight")
def test_pumice_core_perf_refresh_bubbles(request):
    _run(request, "cocotb_test_pumice_core_perf_refresh_bubbles")
def test_pumice_core_perf_paging_sweep(request):
    _run(request, "cocotb_test_pumice_core_perf_paging_sweep")
def test_pumice_core_perf_paging_sched_cross(request):
    _run(request, "cocotb_test_pumice_core_perf_paging_sched_cross", enhanced=True)

# ---------------------------------------------------------------------------
# rbl / adapt_access: RESTORED 2026-09-09 (predictor tables back in rtl/fub/,
# timing re-gated on the write-lead tree). The two directed tests below are
# the ones retired on 2026-09-01, verbatim.
# ---------------------------------------------------------------------------
@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_core_rbl(dut):
    """TASK-001 Axis 2: rbl_static / rbl_dyn -- RBLA miss-counter table.

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
        await _write(dut, addr, data, rid & 0xF)
        got = await _read(dut, addr, rid & 0xF)
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
    """TASK-001 Axis 2: adapt_access (mode 5) -- per-row 2-bit predictor.

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
        await _write(dut, addr, data, rid & 0xF)

    async def _rd_check(addr, rid):
        got = await _read(dut, addr, rid & 0xF)
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



def test_pumice_core_rbl(request):
    _run(request, "cocotb_test_pumice_core_rbl")
def test_pumice_core_acc(request):
    _run(request, "cocotb_test_pumice_core_acc")
