# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_kestrel_mem_loader
# Purpose: Task 11 board-glue tests for kestrel_mem_loader: (a) an AXIL
#          window test over both memory regions with wstrb partial-word
#          writes, CTRL.run readback, and a tiny preloaded program run to
#          halt after run releases; (b) the golden-trace board path -- a
#          Task-8 battery image streamed THROUGH THE AXIL PORT with the
#          battery's golden interpreter diff + spike lockstep reused via
#          RV32UIBattery(tb_class=KestrelLoaderTB); (c) load-mode
#          isolation: core_rst_n stays asserted and core-side reads return
#          the pre-load image while the loader owns the memory.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-07

"""kestrel_mem_loader board-glue tests.

The DUT is kestrel_loader_tb_top (kestrel_mem_loader + kestrel_core).  A
CocoTBFramework AXIL4 master drives the loader's s_axil_* port; the loader
holds the core in reset, takes the image over AXIL, and CTRL.run (AXIL
address 0x20000, bit 0) releases it.

The golden case boots the core at RESET_ADDR = 0x80000000 (the battery
image link base) exactly like the Task-8 direct-load battery, so the golden
interpreter trace and the spike lockstep compare against identical
0x80000000-based PCs; the loader's address window is the low 18 bits on
both wirings, so the board path itself is stressed identically.  The
directed cases boot at 0x0, the loader's power-on default.
"""

import os
import sys
from pathlib import Path

import cocotb
import pytest
from cocotb.triggers import FallingEdge, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = str(Path(__file__).resolve().parents[1])
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

PROGRAMS_DIR = Path(__file__).resolve().parent / "programs"
if str(PROGRAMS_DIR) not in sys.path:
    sys.path.insert(0, str(PROGRAMS_DIR))

from tbclasses.kestrel.kestrel_loader_tb import (                    # noqa: E402
    AXIL_ADDR_MASK,
    CTRL_ADDR,
    KestrelLoaderTB,
)
from tbclasses.kestrel.rv32i_interpreter import RV32IInterpreter     # noqa: E402
from tbclasses.kestrel.rv32ui_battery import (                       # noqa: E402
    LINK_BASE,
    RV32UIBattery,
)

# ---------------------------------------------------------------------------
# Directed program for the AXIL window test (assembled at address 0).
#   addi x1, x0, 0x123   (0x12300093)
#   sw   x1, 0x20(x0)    (0x02102023)  -- store 0x123 to byte 0x20 (imem
#                                         array: addr[16] clear)
#   lw   x2, 0x20(x0)    (0x02002103)  -- load it back
#   lui  x3, 0x10        (0x000101B7)  -- x3 = 0x10000 (dmem region)
#   sw   x1, 0x20(x3)    (0x0211A023)  -- store 0x123 to byte 0x10020
#                                         (dmem array: addr[16] set)
#   lw   x4, 0x20(x3)    (0x0201A203)  -- load it back through the
#                                         core->dmem cross-mux read
#   jal  x0, +0xffe8      (0x7E90F06F)  -- pc-relative jump to 0x10000:
#                                         fetch code from the dmem region
#                                         through the imem port cross-mux
# code at 0x10000 (word index 0x4000):
#   addi x5, x0, 0x55    (0x05500293)
#   ecall                (0x00000073)  -- halt, cause 1
# Encodings are verified by the golden interpreter before the DUT runs, and
# the load/fetch beats are pinned explicitly below.
# ---------------------------------------------------------------------------
PROG_WORDS = {
    0: 0x1230_0093,
    1: 0x0210_2023,
    2: 0x0200_2103,
    3: 0x0001_01B7,
    4: 0x0211_A023,
    5: 0x0201_A203,
    6: 0x7E90_F06F,
    0x4000: 0x0550_0293,
    0x4001: 0x0000_0073,
}
PROG_STORE_ADDR = 0x20        # low byte address the program stores to
# Same word in the AXIL map: byte 0x20 has addr[16] clear, so the unified
# map holds it in the imem array; the dmem region is exercised below.
PROG_STORE_AXIL = 0x00020
# High store target and the dmem-region code, in the AXIL map.
PROG_HIMEM_ADDR = 0x10020     # byte address in the dmem region (addr[16]=1)
PROG_HIMEM_AXIL = 0x10020
PROG_HICODE_AXIL = 0x10000    # jal target, code fetched from the dmem array
PROG_HICODE_INSN = 0x0550_0293


async def _window(dut):
    """AXIL write/read window over both regions, wstrb partials, CTRL
    readback, then a tiny preloaded program run to halt after run
    releases -- including core-side observation of the loaded contents."""
    tb = KestrelLoaderTB(dut, reset_addr=0x0000_0000)
    await tb.ensure_clock()
    await tb.assert_reset()
    await tb.enter_load_mode_only()
    assert int(dut.core_rst_n.value) == 0, "core_rst_n high in load mode"

    # CTRL register: reads back 0 while in load mode.
    assert await tb.axil_read(CTRL_ADDR) == 0, "CTRL.run set in load mode"

    # Full-word and partial-word (wstrb) writes, read back, both regions.
    await tb.axil_write(0x100, 0xAABB_CCDD)
    assert await tb.axil_read(0x100) == 0xAABB_CCDD
    await tb.axil_write(0x100, 0x1122_3344, strb=0b0101)
    assert await tb.axil_read(0x100) == 0xAA22_CC44, "imem wstrb merge"
    await tb.axil_write(0x10100, 0xAABB_CCDD)
    assert await tb.axil_read(0x10100) == 0xAABB_CCDD
    await tb.axil_write(0x10100, 0x1122_3344, strb=0b1010)
    assert await tb.axil_read(0x10100) == 0x11BB_33DD, "dmem wstrb merge"

    # Load the program (image streams here) and check the core is still
    # held; run_to_halt then writes CTRL.run, releases the core, and
    # samples the trace to the ecall halt.
    golden = RV32IInterpreter(PROG_WORDS, reset_addr=0)
    golden.run()
    assert golden.halt_cause == 1, "directed program must halt on ecall"
    await tb.backdoor_load(PROG_WORDS)
    await tb.release_reset()
    assert int(dut.core_rst_n.value) == 0, "run leaked before run_to_halt"
    await tb.run_to_halt()
    assert int(dut.core_rst_n.value) == 1, "core_rst_n low after CTRL.run"
    tb.check_halt(expected_cause=golden.halt_cause,
                  expected_halt_pc=golden.halt_pc)
    tb.check_first_pc()
    tb.check_order_sequence()
    tb.check_x0_rd_zero()
    tb.check_trace(golden.trace)
    tb.check_trap_beat()

    # Core-side store observed back through the loader's AXIL read port in
    # run mode, plus the loaded instruction visible at imem word 0.
    assert await tb.axil_read(PROG_STORE_AXIL) == 0x123, \
        "core store not visible through the AXIL read port"
    assert await tb.axil_read(0x0) == PROG_WORDS[0]

    # Core->dmem cross-mux (review finding 2): the second store/load pair
    # targets byte 0x10020 (addr[16] set), so the store lands in the dmem
    # array via core_wr_dmem and the load's dmem_rdata selects the dmem
    # array on dmem_addr[16]; the jal'd code at 0x10000 is fetched from the
    # dmem array through the imem port's imem_addr[16] select.  The golden
    # diff above already pins every beat; these pin the cross-mux fields
    # explicitly and close the loop through the AXIL read port.
    loads = [b for b in tb.trace if b["mem_rmask"] == 0xF]
    assert len(loads) == 2, f"expected 2 load beats, got {len(loads)}"
    hi_load = loads[1]
    assert hi_load["mem_addr"] == PROG_HIMEM_ADDR, \
        f"high load at 0x{hi_load['mem_addr']:x}, expected 0x{PROG_HIMEM_ADDR:x}"
    assert hi_load["rd_addr"] == 4 and hi_load["rd_wdata"] == 0x123, \
        "high load did not return the stored value through the dmem array"
    assert any(b["pc"] == PROG_HICODE_AXIL and b["insn"] == PROG_HICODE_INSN
               for b in tb.trace), \
        "no beat fetched from the dmem region through the imem port"
    assert await tb.axil_read(PROG_HIMEM_AXIL) == 0x123, \
        "core store to the dmem array not visible through the AXIL read port"
    assert await tb.axil_read(PROG_HICODE_AXIL) == PROG_HICODE_INSN

    # Run-mode write rejection (ML-09): with CTRL.run already 1, an AXIL
    # write into the memory window must not touch the arrays --
    # ld_wr_fire = w_fire && !addr[CTRL] && !run_q gates the loader's write
    # client off in run mode.  The core is halted with its fetch parked on
    # the ecall word (pc freezes at halt_pc), so poison aimed at that very
    # word is observable on the core-side read port: if the write landed,
    # imem_rdata would flip while imem_addr holds.
    halt_pc = golden.halt_pc
    halt_word = PROG_WORDS[halt_pc >> 2]
    poison_axil = halt_pc & AXIL_ADDR_MASK   # ecall word, dmem array (addr[16]=1)
    resp = await tb.axil_write(poison_axil, 0xDEAD_BEEF)
    assert resp == 0, \
        "run-mode write B response not OKAY (leaf slaves always answer OKAY)"
    assert await tb.axil_read(poison_axil) == halt_word, \
        "run-mode AXIL write landed in the array"
    for _ in range(4):
        assert int(dut.imem_addr.value) == halt_pc, \
            "core fetch address moved after halt"
        assert int(dut.imem_rdata.value) == halt_word, \
            "run-mode AXIL write visible on the core-side fetch port"
        await FallingEdge(dut.clk)

    dut._log.info("AXIL window + run-release checks PASSED")


async def _isolation(dut):
    """Load-mode isolation: core_rst_n asserted, no retirement, PC parked
    at RESET_ADDR, and core-side reads return the pre-load image until the
    loader writes (the loader owns the ports; the core never runs)."""
    tb = KestrelLoaderTB(dut, reset_addr=0x0000_0000)
    await tb.ensure_clock()
    await tb.assert_reset()
    assert int(dut.core_rst_n.value) == 0, "core_rst_n high during reset"

    await tb.enter_load_mode_only()
    assert int(dut.core_rst_n.value) == 0, "core_rst_n high in load mode"

    # Pre-load image: imem[RESET_ADDR] reads as 0; the held core parks its
    # fetch address at RESET_ADDR and retires nothing.  (halt may read 1
    # here -- a held core still decodes, and 0x00000000 is illegal; that is
    # a combinational artifact, rvfi_valid is reset-gated so nothing
    # retires and halt_q cannot latch while the core is in reset.)
    for _ in range(4):
        assert int(dut.imem_addr.value) == 0, "pc moved in load mode"
        assert int(dut.imem_rdata.value) == 0, "pre-load image not zeroed"
        assert int(dut.rvfi_valid.value) == 0, "retired in load mode"
        assert int(dut.core_rst_n.value) == 0
        await FallingEdge(dut.clk)

    # Load one word WITHOUT releasing run: the write is visible on the
    # core-side read port, the core is still held, still nothing retires.
    await tb.axil_write(0x0, PROG_WORDS[0])
    for _ in range(4):
        assert int(dut.core_rst_n.value) == 0, "run leaked before CTRL.run"
        assert int(dut.imem_addr.value) == 0, "pc moved before run"
        assert int(dut.imem_rdata.value) == PROG_WORDS[0], \
            "loader write invisible on the core-side read port"
        assert int(dut.rvfi_valid.value) == 0
        await FallingEdge(dut.clk)

    assert await tb.axil_read(CTRL_ADDR) == 0, "CTRL.run set without write"
    dut._log.info("load-mode isolation checks PASSED")


# Cycles s_axil_bready / s_axil_rready are held low mid-transaction while
# the loader's response beat is asserting.
BACKPRESSURE_HOLD_CYCLES = 8
# Bound the wait for a response beat so a broken hold fails instead of
# hanging the sim.
BACKPRESSURE_WAIT_CYCLES = 100


async def _backpressure(dut):
    """AXIL backpressure: hold bready low with a B beat pending, then
    rready low with an R beat pending.  The loader must hold bvalid/rvalid
    (stable, OKAY) for the whole stall, assert the leaf busy taps, and
    deliver each transaction exactly once once ready returns."""
    tb = KestrelLoaderTB(dut, reset_addr=0x0000_0000)
    await tb.ensure_clock()
    await tb.assert_reset()
    await tb.enter_load_mode_only()
    assert int(dut.core_rst_n.value) == 0, "core_rst_n high in load mode"

    # --- write channel: B beat held under a bready stall ---
    # A couple of settle cycles after each policy flip: the BFM's channel
    # monitor can be up to a cycle behind applying it, and a response beat
    # that lands on that stale cycle is consumed with ready high before
    # the stall is visible on the pin.
    tb.master["write"].b_channel.set_ready_policy("stall")
    for _ in range(2):
        await RisingEdge(dut.clk)
    writer = cocotb.start_soon(tb.axil_write(0x100, 0xA5A5_5A5A))
    for _ in range(BACKPRESSURE_WAIT_CYCLES):
        if int(dut.s_axil_bvalid.value) == 1:
            break
        await FallingEdge(dut.clk)
    else:
        raise AssertionError("bvalid never asserted under bready stall")
    held = 0
    for _ in range(BACKPRESSURE_HOLD_CYCLES):
        assert int(dut.s_axil_bvalid.value) == 1, \
            "bvalid dropped while bready held low"
        assert int(dut.s_axil_bresp.value) == 0, \
            "bresp changed while bready held low"
        assert int(dut.dbg_busy_wr.value) == 1, \
            "busy tap low while the B beat is held"
        await FallingEdge(dut.clk)
        held += 1
    # Release just after a rising edge: the held beat then sees bready=1 for
    # a full cycle, so the monitor observes valid&&ready mid-cycle and the
    # handshake completes on the next rising edge.  (Releasing mid-cycle
    # would let a registered bvalid pop at the intervening rising edge
    # before the monitor ever samples it.)
    await RisingEdge(dut.clk)
    tb.master["write"].b_channel.set_ready_policy("always")
    resp = await writer
    assert resp == 0, "B response not OKAY after bready release"
    assert held == BACKPRESSURE_HOLD_CYCLES

    # The stalled write landed exactly once; the pipeline still drains in
    # order (a neighbor write is untouched, a follow-up write works).
    assert await tb.axil_read(0x100) == 0xA5A5_5A5A, \
        "backpressured write lost or duplicated"
    await tb.axil_write(0x104, 0x1234_5678)
    assert await tb.axil_read(0x104) == 0x1234_5678
    assert await tb.axil_read(0x100) == 0xA5A5_5A5A

    # --- read channel: R beat held under an rready stall ---
    tb.master["read"].r_channel.set_ready_policy("stall")
    for _ in range(2):
        await RisingEdge(dut.clk)
    reader = cocotb.start_soon(tb.axil_read(0x100))
    for _ in range(BACKPRESSURE_WAIT_CYCLES):
        if int(dut.s_axil_rvalid.value) == 1:
            break
        await FallingEdge(dut.clk)
    else:
        raise AssertionError("rvalid never asserted under rready stall")
    held_data = int(dut.s_axil_rdata.value)
    for _ in range(BACKPRESSURE_HOLD_CYCLES):
        assert int(dut.s_axil_rvalid.value) == 1, \
            "rvalid dropped while rready held low"
        assert int(dut.s_axil_rresp.value) == 0, \
            "rresp changed while rready held low"
        assert int(dut.s_axil_rdata.value) == held_data, \
            "rdata changed while rvalid held without rready"
        assert int(dut.dbg_busy_rd.value) == 1, \
            "busy tap low while the R beat is held"
        await FallingEdge(dut.clk)
    await RisingEdge(dut.clk)
    tb.master["read"].r_channel.set_ready_policy("always")
    data = await reader
    assert data == 0xA5A5_5A5A, "read data wrong after rready release"

    # And the read channel still works normally afterwards.
    assert await tb.axil_read(0x104) == 0x1234_5678
    dut._log.info("AXIL backpressure checks PASSED")


async def _golden(dut):
    """Golden-trace board path: battery images streamed through the AXIL
    port; the battery's golden interpreter diff + spike lockstep are reused
    unchanged via RV32UIBattery(tb_class=KestrelLoaderTB)."""
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    log_dir = os.path.dirname(os.environ.get("LOG_PATH", "."))
    work_dir = os.path.join(log_dir, "rv32ui_battery_loader")
    tests = ("add",) if level == "gate" else ("simple", "add", "addi")
    battery = RV32UIBattery(dut, repo_root=repo_root, level=level,
                            work_dir=work_dir,
                            tb_class=KestrelLoaderTB, tests=tests)
    await battery.run()


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_kestrel_mem_loader_window(dut):
    """AXIL window over both regions, wstrb partials, CTRL.run release, and
    a tiny preloaded program observed to halt through the core's RVFI."""
    await _window(dut)


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_kestrel_mem_loader_isolation(dut):
    """While the loader owns the memory (load mode): core_rst_n asserted,
    core-side reads return the pre-load image, no retirement, PC parked."""
    await _isolation(dut)


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_kestrel_mem_loader_backpressure(dut):
    """AXIL backpressure: bready/rready held low mid-transaction -- the
    loader holds bvalid/rvalid stable (OKAY) and no beat is lost or
    duplicated once the stall releases."""
    await _backpressure(dut)


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_kestrel_mem_loader_golden(dut):
    """Battery images through the AXIL board path: golden interpreter diff
    + spike lockstep (func level), gate = rv32ui-p-add only."""
    await _golden(dut)


# ---------------------------------------------------------------------------
# pytest wrappers
# ---------------------------------------------------------------------------

# The golden case boots the core at the battery link base exactly like the
# Task-8 battery; the directed cases boot at 0x0 (the loader default).
CASES = {
    "cocotb_test_kestrel_mem_loader_window": 0x0000_0000,
    "cocotb_test_kestrel_mem_loader_isolation": 0x0000_0000,
    "cocotb_test_kestrel_mem_loader_backpressure": 0x0000_0000,
    "cocotb_test_kestrel_mem_loader_golden": LINK_BASE,
}


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"kestrel_mem_loader {lvl}")
                          for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_kestrel_mem_loader(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: one Verilator build per (case, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    reset_addr = CASES[cocotb_testcase]

    test_name_plus_params = f"{cocotb_testcase}_{test_level}"
    log_path = os.path.join(log_dir, f"{test_name_plus_params}.log")
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f"results_{test_name_plus_params}.xml")

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/kestrel-rv32i/dv/filelists/kestrel_tb.f",
    )

    extra_env = {
        "DUT": "kestrel_loader_tb_top",
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        **level_env(test_level),
    }

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "--timescale", "1ns/1ps",
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="kestrel_loader_tb_top",
        module=module,
        testcase=cocotb_testcase,
        sim_build=sim_build,
        extra_env=extra_env,
        parameters={"RESET_ADDR": str(reset_addr)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
