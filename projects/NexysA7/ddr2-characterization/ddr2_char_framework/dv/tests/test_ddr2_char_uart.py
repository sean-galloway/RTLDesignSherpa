# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host program against the harness in simulation, over UART.

This is the sim half of the silicon/sim equivalence. `ddr2_char_uart_tb_top`
wraps the full `ddr2_char_harness` (real UART bridge + harness_csr + engines +
pumice controller); a cocotb UARTMaster/Monitor drives the identical ASCII W/R
byte stream the host sends to the FPGA. The DFI side is the framework's
DFISlavePHY + MemoryModel loopback (no a7ddrphy — not simulatable). The
synchronous host program runs in a worker thread via cocotb.external and talks
to the sim through CocotbUartChannel (see cocotb_uart_bridge.py).

Tests:
  * uart_smoke  — BUILD_ID + SCRATCH round-trip over the real bridge RTL,
                  then a tiny write->read CRC pass. Proves the byte protocol
                  and the engine path round-trip in sim.
  * uart_simple — the UNMODIFIED pumice_master.SimpleTest program (init + a
                  write-then-read integrity pass). Proves the authored-once
                  program runs in sim exactly as on silicon.
"""

import os
import sys

import cocotb
import pytest
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel

_REPO = os.environ["REPO_ROOT"]
_HOST = os.path.join(_REPO, "projects/NexysA7/ddr2-characterization/"
                            "flows-ours-uart/host")
_TBC = os.path.join(_REPO, "projects/NexysA7/ddr2-characterization/"
                           "ddr2_char_framework/dv/tbclasses")
_BRIDGE = os.path.join(_REPO, "projects/components/converters/bin")
for _p in (_HOST, _TBC, _BRIDGE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.harness import UartSimHarness      # noqa: E402
import ddr2_char as dc                                  # noqa: E402
import pumice_master as pm                              # noqa: E402


# Matches ddr2_char_uart_tb_top default (FPGA_CLK_HZ / UART_BAUD = 16).
CLKS_PER_BIT   = 16
# DFI loopback geometry — MUST match the harness controller (ROW_WIDTH=13,
# COL_WIDTH=10) so the BFM decodes DFI addresses the same way (a mismatch
# corrupts the read path). MemoryModel is lazily zero-paged, so the large
# num_lines only commits the pages the small workloads actually touch.
ROW_W, COL_W   = 13, 10
NUM_BANKS      = 8
DRAM_BL        = 4    # DDR2 MR0 default BL — must match the controller
# DFI rate / DRAM beat width. Default = rate-2 / 64b beat (GEAR=1, the known-
# good macro config). Override via env to match the BOARD exactly: rate-4 /
# 32b beat (GEAR=2) — TEST_DFI_RATE=4 TEST_DRAM_BEAT_BYTES=4. The tb_top SV
# params are set to match by the pytest wrapper.
DFI_RATE        = int(os.environ.get("TEST_DFI_RATE", "2"))
DRAM_BEAT_BYTES = int(os.environ.get("TEST_DRAM_BEAT_BYTES", "8"))
# Physical DRAM device width in bytes (x16 => 2). Default = DRAM_BEAT_BYTES so
# one pumice DRAM beat == one physical beat (ratio 1, legacy). The board's x16
# device with a 32b (4-byte) pumice beat packs 2 physical beats per pumice beat,
# so a JEDEC BL4 delivers DRAM_BL*DEVICE_BYTES/DRAM_BEAT_BYTES = 2 pumice beats
# (1 DFI cycle) per command — modeling this is what makes the sim reproduce the
# board's x16 over-read (and validate the burst-length fix).
DRAM_DEVICE_BYTES = int(os.environ.get("TEST_DRAM_DEVICE_BYTES", str(DRAM_BEAT_BYTES)))
# Model the DRAM at PHYSICAL device-word granularity: memory lines + columns are
# device words (x16 => 2 bytes), and a command transfers DRAM_BL device words to
# DRAM_BL consecutive device-word columns. The DFISlavePHY still samples the DFI
# bus in DRAM-beat (DFI-phase) slices (dfi_phase_bytes) so DFI_RATE/rddata_valid
# stay correct; K=beat/device device words pack into each phase. This lets the
# oracle catch the column-stride OVERLAP (per-command footprint of DRAM_BL device
# words collides with a controller column stride < DRAM_BL). device==beat => K=1
# => bit-identical to the legacy single-granularity model.
BEATS_PER_BURST  = DRAM_BL


def _make_dfi_slave(dut):
    num_lines = NUM_BANKS * (1 << ROW_W) * (1 << COL_W)
    memory = MemoryModel(num_lines=num_lines, bytes_per_line=DRAM_DEVICE_BYTES,
                         log=dut._log)
    mapping = AddressMapping(num_ranks=1, num_banks=NUM_BANKS,
                             num_rows=1 << ROW_W, num_cols=1 << COL_W,
                             mapping="row|bank|col")
    base = DFIBase(dfi_version=DFIVersion.V2_1, memory_type=MemoryType.DDR2,
                   timings=builtin_timings("ddr2-650-mt47h64m16hr"),
                   mapping=mapping, beats_per_burst=BEATS_PER_BURST)
    _strict = os.environ.get("TEST_STRICT_WRITE_TIMING", "0") == "1"
    _wrlat = int(os.environ.get("TEST_WRITE_LATENCY", "0"))
    _strict_rd = os.environ.get("TEST_STRICT_READ_TIMING", "0") == "1"
    _rdlat = int(os.environ.get("TEST_READ_LATENCY", "8"))
    slave = DFISlavePHY(dut, dut.aclk, base=base, memory=memory,
                        strict_write_timing=_strict, write_latency=_wrlat,
                        strict_read_timing=_strict_rd, read_latency=_rdlat,
                        # DFI phase (pumice DRAM beat) width for bus slicing;
                        # memory is device-word granular. Equal => legacy K=1.
                        dfi_phase_bytes=DRAM_BEAT_BYTES)
    # Demote HARD JEDEC violations to SOFT: we validate data loopback, not
    # the controller's exact tRCD/tFAW here.
    slave.dram = DramStateModel(timings=base.timings, num_banks=NUM_BANKS,
                                policy=ViolationPolicy(hard=frozenset()))
    return slave, memory


async def _bringup(dut, *, init_complete_delay: int = 20):
    """Clock + reset + DFI loopback BFM + UART pump; returns a DDR2CharDriver
    whose transport is the sim UART (traced). The generic clock/reset/UART
    bringup is the shared UartSimHarness; only the DFI backend BFM +
    init_complete are DDR2-specific and stay here."""
    h = UartSimHarness(dut, clks_per_bit=CLKS_PER_BIT,
                       idle_inputs={"phy_dfi_init_complete": 0,
                                    "phy_dfi_ctrlupd_ack": 0,
                                    "phy_dfi_phyupd_req": 0,
                                    "phy_dfi_phyupd_type": 0})
    chan = await h.start()

    dfi_slave, memory = _make_dfi_slave(dut)

    async def _assert_init_complete():
        await ClockCycles(dut.aclk, init_complete_delay)
        dut.phy_dfi_init_complete.value = 1
    cocotb.start_soon(_assert_init_complete())

    drv = dc.DDR2CharDriver(bridge=h.make_bridge())
    return drv, chan, dfi_slave, memory


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_uart_smoke(dut):
    drv, chan, _dfi, _mem = await _bringup(dut)

    def prog():
        results = {}
        results["build_id"] = drv.build_id()
        results["scratch"] = drv.scratch(0x00C0FFEE)
        # tiny write -> read integrity pass. Mirrors the known-good macro sim
        # flow: BL=4 (= DRAM BL), LFSR pattern (data_mode off), and NO
        # clear_stats between wr and rd (that would drop the latched CRC).
        drv.soft_reset()
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=int(os.environ.get("TEST_T_PHY_WRLAT", "4")),
                               t_rddata_en=4, rd_in_order=True)
        # DFI command-phase placement (pumice DFI_PHASE CSR). Default 0/0 keeps
        # the legacy phase-0 behavior; TEST_RD_PHASE=1 exercises the a7ddrphy
        # rdphase=1 path (RD command on DFI phase 1). The phase-aware DFISlavePHY
        # follows whichever phase carries the command.
        drv.set_dfi_phase(rd_phase=int(os.environ.get("TEST_RD_PHASE", "0")),
                          wr_phase=int(os.environ.get("TEST_WR_PHASE", "0")))
        seed = 0xABCD1234
        # stride = burst_len * bytes_per_beat, so bursts don't overlap
        stride = 4 * 8
        drv.program_wr_engine(start_addr=0x0, burst_len=4, txn_count=4,
                              stride_0=stride, lfsr_seed=seed,
                              axi_size=dc.AXI_SIZE_8)
        drv.start_wr(); results["wr"] = pm.wait_engine(drv, "wr", timeout_s=30)
        drv.program_rd_engine(start_addr=0x0, burst_len=4, txn_count=4,
                              stride_0=stride, lfsr_seed=seed,
                              axi_size=dc.AXI_SIZE_8)
        drv.start_rd(); results["rd"] = pm.wait_engine(drv, "rd", timeout_s=30)
        exp, act, match, valid = drv.crc()
        results.update(exp=exp, act=act, match=match, valid=valid,
                       mism=drv.beats_mismatched())
        return results

    r = await cocotb.external(prog)()
    dut._log.info("smoke results: %s", r)
    assert r["build_id"] == 0x44445232, f"BUILD_ID mismatch: 0x{r['build_id']:08X}"
    assert r["scratch"] == 0x00C0FFEE, f"SCRATCH round-trip failed: {r['scratch']:#x}"
    assert r["wr"] and r["rd"], f"engine did not finish: {r}"
    assert r["valid"] and r["match"] and r["mism"] == 0, f"CRC/data mismatch: {r}"
    # Wire sanity: the host->device stream is well-formed W/R ASCII lines.
    tx = chan.tx_bytes()
    assert tx.count(b"\n") >= 10, "too few UART commands captured"
    assert tx.startswith((b"R ", b"W ")), f"unexpected first bytes: {tx[:8]!r}"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_multichunk(dut):
    """Multi-chunk write->read integrity. burst_len=4 at GEAR=2 splits into
    two DRAM-BL chunks; the second chunk's DRAM column must advance by GEAR
    DRAM beats, not AXI beats (regression for the addr_mapper BYTE_OFFSET_WIDTH
    fix — chunk 2 used to overwrite chunk 1's tail). Single-chunk (bl=2) is the
    control; both must round-trip clean."""
    drv, chan, _dfi, _mem = await _bringup(dut)

    def wr_rd(bl, seed):
        drv.program_wr_engine(start_addr=0x0, burst_len=bl, txn_count=1,
                              lfsr_seed=seed, axi_size=dc.AXI_SIZE_8)
        drv.start_wr(); w = pm.wait_engine(drv, "wr", timeout_s=20)
        drv.program_rd_engine(start_addr=0x0, burst_len=bl, txn_count=1,
                              lfsr_seed=seed, axi_size=dc.AXI_SIZE_8)
        drv.clear_stats(); drv.start_rd()
        r = pm.wait_engine(drv, "rd", timeout_s=15)
        return w, r, drv.beats_mismatched()

    def prog():
        drv.soft_reset()
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=int(os.environ.get("TEST_T_PHY_WRLAT", "4")),
                               t_rddata_en=4, rd_in_order=True)
        return {"bl2": wr_rd(2, 0x5A5A0001),   # 1 chunk (control)
                "bl4": wr_rd(4, 0x5A5A0001)}   # 2 chunks (the fix)

    r = await cocotb.external(prog)()
    dut._log.info("MULTICHUNK rate=%d: %s", DFI_RATE, r)
    for name in ("bl2", "bl4"):
        w, rd, mism = r[name]
        assert w and rd and mism == 0, (
            f"{name} multi-chunk integrity failed: wr={w} rd={rd} mism={mism}")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_simple(dut):
    drv, chan, _dfi, _mem = await _bringup(dut)

    def prog():
        # The UNMODIFIED authored-once program. t_rddata_en=4 matches the
        # known-good DFI-loopback config; leveling is skipped (loopback needs
        # none — the read eye is trivially wide).
        st = pm.SimpleTest(drv, base_addr=0x0, t_phy_wrlat=4, t_rddata_en=4)
        st.init(do_leveling=False)
        return st.run(burst_len=8, txn_count=8)

    res = await cocotb.external(prog)()
    dut._log.info("SimpleTest: ok=%s exp=0x%08X act=0x%08X mism=%d",
                  res.ok, res.expected, res.actual, res.mismatched)
    assert res.ok, (f"SimpleTest failed: exp=0x{res.expected:08X} "
                    f"act=0x{res.actual:08X} mismatched={res.mismatched}")



# =============================================================================
# pytest wrappers
# =============================================================================
def _run(testcase: str, dfi_rate: int = 2, dram_beat_width: int = 64,
         strict_write_timing: bool = False, write_latency: int = 0,
         t_phy_wrlat: int = 4, cmd_delay: int = 0,
         strict_read_timing: bool = False, read_latency: int = 8,
         rd_phase: int = 0, wr_phase: int = 0, dram_device_width: int = 0):
    # dram_device_width=0 => default to dram_beat_width (ratio 1, legacy). Set to
    # 16 to model the board's x16 device (JEDEC BL4 = 1 DFI cycle).
    if dram_device_width == 0:
        dram_device_width = dram_beat_width
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_uart_tb_top"
    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/ddr2_char_uart_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    tag = f"{testcase}_r{dfi_rate}"
    sim_build = os.path.join(tests_dir, "local_sim_build", tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
        # tell the cocotb test how to size the DFISlavePHY BFM
        "TEST_DFI_RATE": str(dfi_rate),
        "TEST_DRAM_BEAT_BYTES": str(dram_beat_width // 8),
        "TEST_DRAM_DEVICE_BYTES": str(dram_device_width // 8),
        # Faithful DFI write-timing: capture wrdata at command+write_latency
        # (like real DRAM) instead of lenient FIFO-on-wrdata_en. Reproduces the
        # on-silicon write-timing failure the lenient BFM hides.
        "TEST_STRICT_WRITE_TIMING": "1" if strict_write_timing else "0",
        "TEST_WRITE_LATENCY": str(write_latency),
        "TEST_T_PHY_WRLAT": str(t_phy_wrlat),
        "TEST_CMD_DELAY": str(cmd_delay),
        "TEST_STRICT_READ_TIMING": "1" if strict_read_timing else "0",
        "TEST_READ_LATENCY": str(read_latency),
        "TEST_RD_PHASE": str(rd_phase),
        "TEST_WR_PHASE": str(wr_phase),
    }
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP",
    ]
    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module="test_ddr2_char_uart",
        testcase=testcase,
        # SV param override so the tb_top's DFI bus matches the BFM geometry.
        parameters={"DFI_RATE": str(dfi_rate),
                    "DRAM_BEAT_WIDTH": str(dram_beat_width),
                    "DRAM_DEVICE_WIDTH": str(dram_device_width)},
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, compile_args=compile_args,
        keep_files=True, timescale="1ns/1ps")


# ---- rate-2 / GEAR-1 (known-good macro config) ----
def test_ddr2_char_uart_smoke(request):
    _run("cocotb_test_uart_smoke")


def test_ddr2_char_uart_simple(request):
    _run("cocotb_test_uart_simple")




# ---- rate-4 / GEAR-2 (the BOARD's exact DFI config: AXI=64, DRAM beat=32) ----
def test_ddr2_char_uart_smoke_rate4(request):
    _run("cocotb_test_uart_smoke", dfi_rate=4, dram_beat_width=32)


def test_ddr2_char_uart_multichunk_rate4(request):
    _run("cocotb_test_uart_multichunk", dfi_rate=4, dram_beat_width=32)


# ---- rate-2 / GEAR-2 (the NEW board config: match LiteDRAM's proven nphases=2,
#      which serializes only DFI phases 0,1 at 4 beats/sys-cycle; AXI=64, beat=32) -
def test_ddr2_char_uart_smoke_rate2_beat32(request):
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32)


def test_ddr2_char_uart_multichunk_rate2_beat32(request):
    _run("cocotb_test_uart_multichunk", dfi_rate=2, dram_beat_width=32)


# ---- FAITHFUL write timing (a7ddrphy write_latency=0): the BFM samples wrdata
#      at command+write_latency like real DRAM, so a controller whose wrdata is
#      late fails (reproducing on-silicon). pumice's raw command->wrdata skew is
#      5 sys-cycles (measured), so the dfi_cmd_delay shim (CMD_DELAY=5) realigns
#      the command with the data. This test proves the fix: strict (write_latency
#      =0) PASSES only with CMD_DELAY=5. Regression guard for the DFI write-timing
#      contract that the lenient loopback cannot see. -----------------------------
def test_ddr2_char_uart_smoke_rate2_strict(request):
    # Pre-pull (PREPULL_EN in the char macro) stages wrdata before the command.
    # With the FSM-free wr-path front end (pumice_wr_splitter chopper + intake),
    # the DFI command and wrdata are aligned at the strict write_latency=0
    # window with NO residual offset, so the runtime cmd_delay CSR is 0. (The
    # prior 1-cycle command-shorter-than-wrdata offset that needed cmd_delay=1
    # is gone.) A stale cmd_delay=1 rotates the captured stream by one beat
    # (seed lands at the last column) -> every read beat mismatches.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         strict_write_timing=True, write_latency=0, t_phy_wrlat=0, cmd_delay=0)


def test_ddr2_char_uart_smoke_rate2_strict_read(request):
    # Faithful read gate: rddata returns read_latency after the controller's
    # dfi_rddata_en (FIFO-ordered per RD command), NOT self-timed off CL. Checks
    # the controller asserts rddata_en with the right cadence + captures right.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0, cmd_delay=0)


def test_ddr2_char_uart_smoke_rate2_faithful(request):
    # Full a7ddrphy contract: strict write (write_latency=0) AND strict read
    # (rddata_en-gated, read_latency=8). If this passes, pumice's DFI drive is
    # faithful to the real PHY -> the board should read+write correctly.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0, cmd_delay=0)


def test_ddr2_char_uart_smoke_rate2_x16(request):
    # Board-accurate x16 model. A 32b pumice DRAM beat packs 2 physical x16
    # beats, so a JEDEC BL4 = 1 DFI cycle: the oracle delivers beats_per_burst=2
    # per DRAM command (DRAM_DEVICE_BYTES=2), and pumice scales its burst length
    # (DRAM_DEVICE_WIDTH=16 => bl_val 4->2) so a 4-beat burst SPLITS into two BL4
    # commands, each capturing exactly 1 real DFI cycle. Without the scaling
    # pumice issues one 4-beat command capturing 2 DFI cycles while the DRAM
    # delivers only 1 -> the on-silicon 50% over-read. This test reproduces that
    # (fails) without the fix and passes with it.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16, strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0, cmd_delay=0)


def test_ddr2_char_uart_smoke_rate2_rdphase1(request):
    # rdphase=1: pumice's DFI_PHASE CSR places the READ command on DFI phase 1
    # (the a7ddrphy contract for DDR2/CL3/nphases=2). Proves the CSR -> formatter
    # phase-select relocates the command AND the full read path still completes
    # (the phase-aware DFISlavePHY follows the command to phase 1). The board's
    # on-silicon ILA showed RD-on-phase-0 corrupts the burst tail; this is the
    # digital mechanism that fixes it. See project_ddr2_ila_read_valid_skew.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0, cmd_delay=0,
         rd_phase=1, wr_phase=0)
