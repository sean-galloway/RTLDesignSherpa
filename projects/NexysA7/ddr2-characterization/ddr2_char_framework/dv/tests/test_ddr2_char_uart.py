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

import pytest
import cocotb
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
from CocoTBFramework.components.dfi.dfi_timing import DFITimingProfile
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
DRAM_BL        = int(os.environ.get("TEST_DRAM_BL", "4"))  # JEDEC MR0 BL — must
# match the controller. Now passed to the tb_top as an SV param (DRAM_BL) AND to
# the BFM as beats_per_burst, so DUT and oracle cannot diverge.
#
# Default 4 = the board build: DFI_RATE=2 / BL4, matching the a7ddrphy netlist
# (1:2 — 1-bit rdphase CSR, ISERDES DATA_WIDTH=4 on sys2x) and LiteDRAM's proven
# DDR2 config on this board. The earlier BL8 default came from the nphases=4
# theory, which silicon disproved: the PHY's DFI exposes 4 phases but only 2 are
# real, so p2/p3 carry the previous cycle's beats.
# DFI rate / DRAM beat width. Default = rate-2 / 64b beat (GEAR=1, the known-
# good macro config). Override via env to match the BOARD exactly: rate-4 /
# 32b beat (GEAR=2) — TEST_DFI_RATE=4 TEST_DRAM_BEAT_BYTES=4. The tb_top SV
# params are set to match by the pytest wrapper.
DFI_RATE        = int(os.environ.get("TEST_DFI_RATE", "2"))
DRAM_BEAT_BYTES = int(os.environ.get("TEST_DRAM_BEAT_BYTES", "8"))
# gear_ratio CSR = log2(active DFI rate) and MUST match the compile-time DFI_RATE
# of this build (rate-2 => 1, rate-4 => 2). set_dfi_phase does a full-word
# DFI_PHASE write, so we pass this explicitly; otherwise gear_ratio would be
# clobbered (=1:1) and pumice masks off all but DFI phase 0 -> reads never
# complete. (A build that never calls set_dfi_phase keeps the RTL reset, which
# is 2=1:4 -- correct for the board's fixed nphases=4 but NOT for a rate-2 sim.)
GEAR_RATIO      = DFI_RATE.bit_length() - 1
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
    # Faithful a7ddrphy read model: rddata_valid is presented a fixed latency
    # after the READ COMMAND and (read_en_gated) driven ONLY on cycles the
    # controller asserts dfi_rddata_en — the real Artix-7 ISERDES capture
    # window. Unlike the strict_read_timing path (read_ref=rddata_en, which
    # SLAVES the return to whatever cadence the controller's rddata_en has and
    # thus masks an aligner mis-pacing), this catches a controller that fires
    # rddata_en at the wrong cadence for tCCD-paced reads.
    _a7_gated = os.environ.get("TEST_A7_READ_GATED", "0") == "1"
    # a7ddrphy-faithful free-running ISERDES read model: DATA anchored to the
    # command, VALID = rddata_en delayed by TEST_A7_READ_VALID_LAT. Decoupled
    # data/valid reproduce the on-silicon consecutive-read one-slot shift.
    _a7_free = os.environ.get("TEST_A7_READ_FREE", "0") == "1"
    _vlat = int(os.environ.get("TEST_A7_READ_VALID_LAT", str(_rdlat)))
    # a7ddrphy BL < 2*nphases anchored-phase read model (RDS-DV, task #146). A BL4
    # read on the fixed nphases=4 PHY fills only its rd_phase-anchored phase-pair;
    # the other phases hold the OTHER packed read's beats (stale). pumice's
    # grab-all aligner captures the whole DFI word -> 2 of 4 device-words stale ->
    # beats_mismatched == 2*txn (the on-silicon rate4_x16 fingerprint, invariant to
    # gear since the board built at DFI_RATE=nphases=4 and still failed).
    _a7_bl4 = os.environ.get("TEST_A7_READ_BL4", "0") == "1"
    if _a7_bl4:
        _timing = DFITimingProfile.a7ddrphy_bl4(
            read_latency=_rdlat, write_latency=_wrlat,
            read_en_gated=(os.environ.get("TEST_A7_READ_GATED", "0") == "1"))
    elif _a7_free:
        _timing = DFITimingProfile.a7ddrphy_free_running(
            read_latency=_rdlat, read_valid_latency=_vlat,
            write_latency=_wrlat)
    elif _a7_gated:
        _timing = DFITimingProfile.a7ddrphy(read_latency=_rdlat,
                                            write_latency=_wrlat,
                                            read_en_gated=True)
    else:
        _timing = None
    # Per-64b-beat READ SKEW injection (DFISlavePHY model knob, default 0 = off).
    # Kept as a fault-injection hook; the controller-side deskew CSR that once
    # "cancelled" it was removed (disproven dead-end — see TASKS.md TASK-DESKEW).
    _hi_skew = int(os.environ.get("TEST_READ_HI_SKEW", "0"))
    _lo_skew = int(os.environ.get("TEST_READ_LO_SKEW", "0"))
    if _timing is not None and (_hi_skew or _lo_skew):
        _timing.read_hi_skew = _hi_skew
        _timing.read_lo_skew = _lo_skew
    # a7ddrphy 4-phase read-window offset (RDS-DV #32): non-zero reproduces the
    # nphases=4-PHY / DFI_RATE=2-controller device-word read corruption in sim.
    _dwoff = int(os.environ.get("TEST_READ_DW_OFFSET", "0"))
    slave = DFISlavePHY(dut, dut.aclk, base=base, memory=memory,
                        strict_write_timing=_strict, write_latency=_wrlat,
                        strict_read_timing=_strict_rd, read_latency=_rdlat,
                        timing=_timing, read_device_word_offset=_dwoff,
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
                          wr_phase=int(os.environ.get("TEST_WR_PHASE", "0")),
                          gear_ratio=GEAR_RATIO, bl=DRAM_BL)
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
async def cocotb_test_uart_pagehit(dut):
    """Board-failing pattern: MANY page-hit reads paced at tCCD=2.

    The on-silicon ILA showed the read corruption only appears when the
    controller issues MULTIPLE sequential-column reads in ONE open row
    (page hits) paced at tCCD=2 PAIRS. The return is shifted by one READ:
    read N's data lands in read N+1's slot; read 0's slot returns ZERO ->
    beats_mismatched == 2 * txn_count. A single read (smoke's txn=4 is too
    few / not tightly tCCD-paced) cannot exhibit a one-read SHIFT.

    This drives write-then-read of the SAME region: BL4, TEST_PAGEHIT_TXN
    (default 8) sequential columns in one row, stride = BL*8 bytes. NO
    clear_stats between wr and rd (keeps the latched CRC)."""
    drv, chan, _dfi, _mem = await _bringup(dut)

    NTXN = int(os.environ.get("TEST_PAGEHIT_TXN", "8"))

    def prog():
        results = {}
        drv.soft_reset()
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=int(os.environ.get("TEST_T_PHY_WRLAT", "4")),
                               t_rddata_en=int(os.environ.get("TEST_T_RDDATA_EN", "4")),
                               rd_in_order=True)
        drv.set_dfi_phase(rd_phase=int(os.environ.get("TEST_RD_PHASE", "0")),
                          wr_phase=int(os.environ.get("TEST_WR_PHASE", "0")),
                          gear_ratio=GEAR_RATIO, bl=DRAM_BL)
        seed = 0xABCD1234
        stride = 4 * 8   # BL * bytes_per_beat -> consecutive columns, same row
        drv.program_wr_engine(start_addr=0x0, burst_len=4, txn_count=NTXN,
                              stride_0=stride, lfsr_seed=seed,
                              axi_size=dc.AXI_SIZE_8)
        drv.start_wr(); results["wr"] = pm.wait_engine(drv, "wr", timeout_s=60)
        drv.program_rd_engine(start_addr=0x0, burst_len=4, txn_count=NTXN,
                              stride_0=stride, lfsr_seed=seed,
                              axi_size=dc.AXI_SIZE_8)
        drv.start_rd(); results["rd"] = pm.wait_engine(drv, "rd", timeout_s=60)
        exp, act, match, valid = drv.crc()
        results.update(exp=exp, act=act, match=match, valid=valid,
                       mism=drv.beats_mismatched())
        return results

    r = await cocotb.external(prog)()
    dut._log.info("PAGEHIT results (NTXN=%d): %s", NTXN, r)
    assert r["wr"] and r["rd"], f"engine did not finish: {r}"
    assert r["valid"] and r["match"] and r["mism"] == 0, (
        f"page-hit read mismatch (NTXN={NTXN}): {r} "
        f"(board fails here with mism == 2*txn == {2*NTXN})")


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
        # Program DFI_PHASE for THIS build. The RTL gear_ratio resets to 1:4
        # (2'd2) and bl resets to 4; a rate-2 build MUST override gear_ratio to
        # log2(DFI_RATE) or the runtime active-rate (=1<<gear) exceeds the built
        # phase count and reads never complete. Every other test does this via
        # set_dfi_phase; multichunk previously relied on the (wrong) reset.
        drv.set_dfi_phase(rd_phase=int(os.environ.get("TEST_RD_PHASE", "0")),
                          wr_phase=int(os.environ.get("TEST_WR_PHASE", "0")),
                          gear_ratio=GEAR_RATIO, bl=DRAM_BL)
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


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_uart_sweep(dut):
    """Short BOTH-ORDERINGS functional smoke over the COMMON harness. Runs a
    ~SWEEP_NPKT (default 20) packet write->read integrity pass twice:
      * in-order : force_inorder=1, single AXI id
      * ooo      : force_inorder=0, multi-id id-spread (id_mode=COUNTER) so the
                   scheduler reorders across ids
    Responses always return in AR order (the rd CAM is a reorder buffer), so the
    engine's per-beat LFSR check is valid for both legs. One init; force_inorder
    is a runtime scheduler knob flipped between legs; the ooo leg uses a separate
    address region so it can't alias the in-order data. Parametrized over the DFI
    build configs by the pytest wrappers (gear-1 / rate4 / beat32 / x16)."""
    drv, chan, _dfi, _mem = await _bringup(dut)

    NPKT   = int(os.environ.get("SWEEP_NPKT", "20"))
    BURST  = 4
    STRIDE = BURST * 8
    SEED   = 0xABCD1234

    def _leg(base, force_inorder, id_mode):
        drv.set_scheduler(force_inorder=force_inorder)   # runtime, next quiet pt
        drv.program_wr_engine(start_addr=base, burst_len=BURST, txn_count=NPKT,
                              stride_0=STRIDE, lfsr_seed=SEED,
                              axi_size=dc.AXI_SIZE_8, id_mode=id_mode)
        drv.start_wr(); w = pm.wait_engine(drv, "wr", timeout_s=60)
        drv.program_rd_engine(start_addr=base, burst_len=BURST, txn_count=NPKT,
                              stride_0=STRIDE, lfsr_seed=SEED,
                              axi_size=dc.AXI_SIZE_8, id_mode=id_mode)
        drv.clear_stats(); drv.start_rd()
        r = pm.wait_engine(drv, "rd", timeout_s=60)
        return dict(wr=w, rd=r, mism=drv.beats_mismatched())

    def prog():
        results = {"build_id": drv.build_id()}
        drv.soft_reset()
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=4,
                               t_rddata_en=4, rd_in_order=True)
        drv.set_dfi_phase(rd_phase=0, wr_phase=0, gear_ratio=GEAR_RATIO, bl=DRAM_BL)
        results["inorder"] = _leg(0x00000, force_inorder=True,
                                  id_mode=dc.ID_MODE_FIXED)
        results["ooo"]     = _leg(0x40000, force_inorder=False,
                                  id_mode=dc.ID_MODE_COUNTER)
        return results

    r = await cocotb.external(prog)()
    dut._log.info("sweep results (NPKT=%d): %s", NPKT, r)
    assert r["build_id"] == 0x44445232, f"BUILD_ID mismatch: 0x{r['build_id']:08X}"
    for name in ("inorder", "ooo"):
        res = r[name]
        assert res["wr"] and res["rd"], f"{name}: engine did not finish: {res}"
        assert res["mism"] == 0, f"{name}: {res['mism']} beat(s) mismatched: {res}"



# =============================================================================
# pytest wrappers
# =============================================================================
def _run(testcase: str, dfi_rate: int = 2, dram_beat_width: int = 64,
         strict_write_timing: bool = False, write_latency: int = 0,
         t_phy_wrlat: int = 4, cmd_delay: int = 0,
         strict_read_timing: bool = False, read_latency: int = 8,
         rd_phase: int = 0, wr_phase: int = 0, dram_device_width: int = 0,
         a7_read_gated: bool = False, read_device_word_offset: int = 0,
         a7_read_free: bool = False, a7_read_valid_lat: int = -1,
         a7_read_bl4: bool = False,
         pagehit_txn: int = 8):
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
        # DFI-loopback sim: zero-skew BFM -> the host programs' board-tuple
        # PHY-timing defaults (t_phy_wrlat=1 / rddata_delay=7) do not apply.
        "TEST_T_PHY_WRLAT": os.environ.get("TEST_T_PHY_WRLAT", "0"),
        "TEST_RDDATA_DELAY": os.environ.get("TEST_RDDATA_DELAY", "0"),
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
        # tell the cocotb test how to size the DFISlavePHY BFM
        "TEST_DFI_RATE": str(dfi_rate),
        # gear_ratio CSR for this build = log2(DFI_RATE). Threaded to host progs
        # (SimpleTest) that call set_dfi_phase, so the full-word DFI_PHASE write
        # sets the correct active-phase count instead of clobbering it to 1:1.
        "TEST_GEAR_RATIO": str(dfi_rate.bit_length() - 1),
        # JEDEC burst length for this build (board = DDR2 BL8). SimpleTest.init
        # reads this so its set_dfi_phase programs bl for the build (board omits
        # it => preserve the RTL reset bl=8, a full-DFI-word BL8 x16 read).
        "TEST_DRAM_BL": str(DRAM_BL),
        "TEST_DRAM_BEAT_BYTES": str(dram_beat_width // 8),
        "TEST_DRAM_DEVICE_BYTES": str(dram_device_width // 8),
        "TEST_READ_HI_SKEW": os.environ.get("TEST_READ_HI_SKEW", "0"),
        "TEST_READ_LO_SKEW": os.environ.get("TEST_READ_LO_SKEW", "0"),
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
        "TEST_T_RDDATA_EN": os.environ.get("TEST_T_RDDATA_EN", "4"),
        "TEST_A7_READ_GATED": "1" if a7_read_gated else "0",
        "TEST_READ_DW_OFFSET": str(read_device_word_offset),
        "TEST_A7_READ_FREE": "1" if a7_read_free else "0",
        "TEST_A7_READ_VALID_LAT": str(a7_read_valid_lat if a7_read_valid_lat >= 0
                                      else read_latency),
        "TEST_A7_READ_BL4": "1" if a7_read_bl4 else "0",
        "TEST_PAGEHIT_TXN": str(pagehit_txn),
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
        # DRAM_BL is overridden explicitly rather than left to the
        # ddr2_char_macro default: the DUT's burst framing and the BFM's
        # beats_per_burst must come from ONE value. They previously agreed only
        # by coincidence (both 8), and when they diverged the mismatch showed up
        # as a phantom "BL8 write-path corruption" in the controller.
        parameters={"DFI_RATE": str(dfi_rate),
                    "DRAM_BL": str(DRAM_BL),
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


# The rate4_x16 tests are the BOARD config (gear 1:4 == PHY nphases=4, x16, BL4)
# INTEGRATION GATE, run under the faithful a7ddrphy BL4 anchored read model. They
# are now GREEN (task #146 sub-DFI-word packing landed; verified 2026-07-15):
#
#   FIX: the DFI command path issues the N_SUBCMD (=2 here) BL4 sub-column reads
#   in ONE DFI cycle at command phases {rd_phase, rd_phase+bl_pumice} = {0, 2}.
#   The faithful a7ddrphy de-interleaver anchors each sub's BL beats to its
#   command phase, so BOTH anchored runs land in ONE 128b DFI word -> fully
#   packed, ZERO stale. The read aligner captures that ONE word (BL_WORDS=1) and
#   returns it -> reads COMPLETE and beats_mismatched == 0.
#
# The on-board BUG (issue ONE BL4 read per DFI word -> the other phase-pair holds
# the previous read's beats, 2 of 4 device-words stale, beats_mismatched == 2*txn)
# and the FIX (2 packed reads -> 0 stale) are BOTH proven at the model level in
# test_a7ddrphy_bl4_anchored.py against the SHARED DV de-interleaver
# (dfi_slave_phy.deinterleave_read_window + dfi_timing.bl_anchored_slot_mask); the
# RTL mirrors that geometry in pumice_dfi_cmd_path's elaboration assertion. These
# integration gates assert the positive result (mism == 0, reads complete).
#
# NOTE (pytest surface): a cocotb run() failure surfaces as SystemExit here; the
# honest signal is the cocotb log line "<PHASE> results ...: {'rd': ..., 'mism': ...}".


def test_ddr2_char_uart_smoke_rate4_x16(request):
    # BOARD CONFIG integration gate (task #146): gear 1:4 (DFI_RATE=4) + true x16
    # (32b pumice beat, 16b device). A JEDEC BL4 x16 burst delivers 4 device-words
    # = 2 DFI phases = HALF the fixed nphases=4 8-slot de-interleave window. The
    # faithful a7ddrphy BL4 read model (a7ddrphy_bl4) anchors each RD's beats to its
    # command phase. GREEN: the RTL packs the two BL4 sub-reads into one DFI word at
    # phases {0,2}, so the read completes and mism == 0 (the smoke path asserts it).
    _run("cocotb_test_uart_smoke", dfi_rate=4, dram_beat_width=32,
         dram_device_width=16, a7_read_bl4=True, read_latency=8,
         t_phy_wrlat=0)


def test_ddr2_char_uart_multichunk_rate4_x16(request):
    # Multi-read under the board x16+gear1:4 config, faithful a7ddrphy BL4 anchored
    # read model. GREEN: the sub-DFI-word packing lands the two BL4 sub-reads in one
    # DFI word (phases {0,2}) so reads complete with mism == 0.
    _run("cocotb_test_uart_multichunk", dfi_rate=4, dram_beat_width=32,
         dram_device_width=16, a7_read_bl4=True, read_latency=8,
         t_phy_wrlat=0)


def test_ddr2_char_uart_pagehit_rate4_x16(request):
    # The EXACT board DFI config (gear 1:4 == PHY nphases=4, x16, BL4) under the
    # faithful a7ddrphy BL4 anchored read model, driven by the on-silicon page-hit
    # pattern (many tCCD-paced sequential-column reads) — the closest integration
    # analogue of the board run. On the board this returned 2-of-4 device-words
    # STALE (beats_mismatched == 2*txn). GREEN now: the RTL issues the two BL4
    # sub-reads in one DFI cycle at command phases {0,2}, the a7ddrphy packs both
    # anchored runs into one DFI word (0 stale), so the page-hit read stream
    # completes with beats_mismatched == 0 (the pagehit path asserts mism == 0).
    _run("cocotb_test_uart_pagehit", dfi_rate=4, dram_beat_width=32,
         dram_device_width=16, a7_read_bl4=True, read_latency=8,
         t_phy_wrlat=0)


def test_ddr2_char_uart_smoke_rate2_beat32(request):
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32)


def test_ddr2_char_uart_multichunk_rate2_beat32(request):
    _run("cocotb_test_uart_multichunk", dfi_rate=2, dram_beat_width=32)


# ---- FAITHFUL write timing (a7ddrphy write_latency=0): the BFM samples wrdata
#      at command+write_latency like real DRAM, so a controller whose wrdata is
#      late fails (reproducing on-silicon). The runtime dfi_cmd_delay CSR is a
#      HARDWARE bring-up knob (compensates the real PHY's analog command<->DQ
#      skew, swept live on the board) — NOT a functional-test constant. In sim
#      (deterministic, write_latency=0) the DFI-correct alignment is 0, so we do
#      NOT set it: pumice's wr-path front end (pumice_wr_splitter chopper +
#      intake) drives wrdata concurrent with the WR command by design. If any of
#      these ever needs a non-zero cmd_delay to pass, that is a real RTL wr-timing
#      regression to FIX in RTL (it shows up as a one-beat stream rotation -> the
#      LFSR seed lands at the last column -> mism), not a constant to tune here. --
def test_ddr2_char_uart_smoke_rate2_strict(request):
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         strict_write_timing=True, write_latency=0, t_phy_wrlat=0)


def test_ddr2_char_uart_smoke_rate2_strict_read(request):
    # Faithful read gate: rddata returns read_latency after the controller's
    # dfi_rddata_en (FIFO-ordered per RD command), NOT self-timed off CL. Checks
    # the controller asserts rddata_en with the right cadence + captures right.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0)


def test_ddr2_char_uart_smoke_rate2_faithful(request):
    # Full a7ddrphy contract: strict write (write_latency=0) AND strict read
    # (rddata_en-gated, read_latency=8). If this passes, pumice's DFI drive is
    # faithful to the real PHY -> the board should read+write correctly.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0)


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
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0)


def test_ddr2_char_uart_pagehit_rate2_x16(request):
    # Board-failing PATTERN under the faithful x16 strict-read config
    # (offset=0, no artificial injection). Drives many page-hit reads paced
    # at tCCD=2 -- the exact pattern the on-silicon ILA showed corrupts
    # (mism == 2*txn). If this fails NATURALLY, the sim reproduces the board
    # bug from the pattern alone. If it PASSES, the DFISlavePHY read model is
    # not faithful enough to the a7ddrphy consecutive-read timing.
    _run("cocotb_test_uart_pagehit", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16, strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0)


def test_ddr2_char_uart_pagehit_rate2_x16_a7gated(request):
    # Same board-failing page-hit pattern but under the a7ddrphy COMMAND-
    # anchored, rddata_en-GATED read model (read_ref=command, not slaved to
    # the controller's rddata_en cadence). read_latency == t_rddata_en(=4)
    # so a single read aligns; only the tCCD consecutive-read cadence bug can
    # break it. This is the model most likely to expose the one-read shift.
    _run("cocotb_test_uart_pagehit", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16, strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=4, t_phy_wrlat=0,
         a7_read_gated=True)


def test_ddr2_char_uart_pagehit_rate2_x16_free(request):
    # a7ddrphy-FAITHFUL free-running ISERDES read model on the board-failing
    # page-hit pattern. DATA is anchored to the READ COMMAND (read_latency=8);
    # VALID is the controller's rddata_en delayed by read_valid_latency. Data
    # and valid are DECOUPLED (unlike strict_read / a7_gated, which re-lock them
    # and hide the shift). read_valid_latency == read_latency => aligned control
    # (should read clean, proving the model is bit-exact when timing matches).
    # read_valid_latency=5 lands the valid strobe INSIDE the command-anchored
    # data window (aligned control -> reads clean; empirically 4 or 5 pass).
    _run("cocotb_test_uart_pagehit", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16, strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0,
         a7_read_free=True, a7_read_valid_lat=5)


@pytest.mark.xfail(strict=True, reason="deliberate valid/data decoupling "
                   "(valid_lat=6 vs data-anchored cadence) must be SEEN as "
                   "mismatches. On the board this class is aligned by the "
                   "t_rddata_en/rddata_delay tuple, not RTL — see TASK-BRINGUP.")
def test_ddr2_char_uart_pagehit_rate2_x16_free_earlyen(request):
    # NEGATIVE model (strict xfail): the rddata_en->valid strobe DECOUPLED from
    # the command-anchored data by one DFI cycle -> read N's data lands in read
    # N+1's slot (beats_mismatched == 2*txn, the historical ILA signature).
    _run("cocotb_test_uart_pagehit", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16, strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0,
         a7_read_free=True, a7_read_valid_lat=6)


@pytest.mark.xfail(strict=True, reason="deliberate fault injection: a "
                   "device-word window offset must be SEEN as mismatches "
                   "(negative model). The #143-era premise that the board had "
                   "this offset was disproven — the board reads clean at "
                   "offset 0 with the wrlat=1/rden=6/rddata_delay=7 tuple.")
def test_ddr2_char_uart_smoke_rate2_x16_readshift(request):
    # NEGATIVE model (strict xfail): inject a device-word read-window offset
    # (RDS-DV #32 DFISlavePHY knob) and require the metric to flag it. The
    # companion _readshift0 (offset=0) must PASS -> the knob is bit-exact off.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16, strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0,
         read_device_word_offset=2)


def test_ddr2_char_uart_smoke_rate2_x16_readshift0(request):
    # Control: same config, offset=0 (ideal window) -> reads clean. Guards that
    # the new DFISlavePHY knob is bit-exact at 0 (no regression).
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16, strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0,
         read_device_word_offset=0)


def test_ddr2_char_uart_smoke_rate2_x16_a7gated(request):
    # BOARD-FAITHFUL a7ddrphy read model: rddata_valid presented read_latency
    # after the READ COMMAND and driven ONLY inside the controller's rddata_en
    # window (read_en_gated). Unlike the strict_read path (which slaves the
    # return to the controller's own rddata_en cadence and thus HIDES an aligner
    # mis-pacing), this reproduces the on-silicon read failure: pumice's DFI
    # scheduler paces same-row reads at tCCD=2, but pumice_dfi_rd_aligner drives
    # CONTIGUOUS (zero-bubble, BL_WORDS-apart) rddata_en windows, so the 2nd
    # read's enable fires a cycle early and captures a ZERO beat (ILA-confirmed,
    # beats_mismatched=32). EXPECTED TO FAIL until the aligner respects the
    # per-command (tCCD) read cadence.
    # read_latency MUST match the controller's t_rddata_en (=4 in the smoke prog)
    # so the command-anchored data window overlaps the enable window: with that
    # aligned, a SINGLE read works and only the tCCD read-cadence bug (2nd+ read's
    # enable a cycle early) can make it fail. read_latency != t_rddata_en would
    # stall unconditionally (gated model) and mask the actual defect.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16, strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=4, t_phy_wrlat=0,
         a7_read_gated=True)


def test_ddr2_char_uart_smoke_rate2_rdphase1(request):
    # rdphase=1: pumice's DFI_PHASE CSR places the READ command on DFI phase 1
    # (the a7ddrphy contract for DDR2/CL3/nphases=2). Proves the CSR -> formatter
    # phase-select relocates the command AND the full read path still completes
    # (the phase-aware DFISlavePHY follows the command to phase 1). The board's
    # on-silicon ILA showed RD-on-phase-0 corrupts the burst tail; this is the
    # digital mechanism that fixes it. See project_ddr2_ila_read_valid_skew.
    _run("cocotb_test_uart_smoke", dfi_rate=2, dram_beat_width=32,
         strict_write_timing=True, write_latency=0,
         strict_read_timing=True, read_latency=8, t_phy_wrlat=0,
         rd_phase=1, wr_phase=0)


# ---- short both-orderings functional sweep (in-order + OOO multi-id) ---------
#      ~20 packets/leg over the common harness, across the DFI build configs.
def test_ddr2_char_uart_sweep(request):            # gear-1 (AXI=64, beat=64)
    _run("cocotb_test_uart_sweep", dfi_rate=2, dram_beat_width=64)


def test_ddr2_char_uart_sweep_rate4(request):      # board DFI (rate4, beat=32)
    _run("cocotb_test_uart_sweep", dfi_rate=4, dram_beat_width=32)


def test_ddr2_char_uart_sweep_beat32(request):     # rate2 / beat=32
    _run("cocotb_test_uart_sweep", dfi_rate=2, dram_beat_width=32)


def test_ddr2_char_uart_sweep_x16(request):        # x16 device model
    _run("cocotb_test_uart_sweep", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16)
