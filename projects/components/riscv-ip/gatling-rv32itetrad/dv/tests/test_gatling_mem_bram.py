# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gatling_mem_bram
# Purpose: gatling_core behind gatling_mem_bram over AXIL (the board path):
#          the address map and per-context banks, the loader rules (a running
#          context's bank is write-protected, reads always served), per-context
#          status registers, reloading one context while another runs, and the
#          rv32ui battery loaded and run entirely through AXIL.
#
# Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32itetrad
#
# Created: 2026-10-21

"""gatling_mem_bram tests (AXIL path, as the board host drives it)."""

import os

import cocotb
import pytest

import gatling_sim
from TBClasses.shared.test_levels import reg_level_grid

from gatling.gatling_battery import GatlingBattery                     # noqa: E402
from gatling.gatling_bram_tb import (                                   # noqa: E402
    BUILD_ID, REG_BUILD_ID, REG_CTRL, GatlingBramTB, hart_reg, mem_addr)
from gatling.gatling_tb import ALL_HARTS, CPI, NUM_HARTS                # noqa: E402
from tbclasses.kestrel.rv32i_interpreter import RV32IInterpreter       # noqa: E402
from tbclasses.kestrel.rv32ui_battery import GATE_TESTS, LINK_BASE     # noqa: E402
from test_gatling_core import counted_loop                              # noqa: E402

# func: a cross-section (ALU, branches, every load/store width, self-modifying
# code, the expected misaligned halt); full: all 42.
FUNC_IMAGES = ("simple", "add", "beq", "jalr", "lb", "lhu", "sb", "sw", "fence_i", "ma_data")


async def _start(dut, reset_addr=0):
    tb = GatlingBramTB(dut, reset_addr=reset_addr)
    await tb.ensure_clock()
    await tb.assert_reset()
    await tb.release_reset()
    return tb


def _golden(words):
    g = RV32IInterpreter(words, reset_addr=0)
    g.run()
    return g


def _check(tb, c, words):
    g = _golden(words)
    h = tb.harts[c]
    h.check_halt(expected_cause=g.halt_cause, expected_halt_pc=g.halt_pc)
    h.check_first_pc()
    h.check_order_sequence()
    h.check_trace(g.trace)
    tb.check_window(c)
    return g


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_gatling_mem_map(dut):
    """BUILD_ID, CTRL, four distinct banks at the same offset, byte strobes,
    the addr[16] alias, and per-context status reading zero after reset."""
    tb = await _start(dut)
    assert await tb.axil_read(REG_BUILD_ID) == BUILD_ID, "BUILD_ID"
    assert await tb.axil_read(REG_CTRL) == 0, "CTRL after reset"
    for c in range(NUM_HARTS):
        await tb.axil_write(mem_addr(c, 0x100), 0xA000_0000 | (c << 16) | 0xBEEF)
    for c in range(NUM_HARTS):
        got = await tb.axil_read(mem_addr(c, 0x100))
        assert got == 0xA000_0000 | (c << 16) | 0xBEEF, f"bank {c}: 0x{got:08x}"
        assert await tb.axil_read(mem_addr(c, 0x100) | 0x1_0000) == got, \
            f"bank {c}: addr[16] must alias"
    await tb.axil_write(mem_addr(2, 0x200), 0x1122_3344)
    await tb.axil_write(mem_addr(2, 0x200), 0x0000_AA00, strb=0b0010)
    assert await tb.axil_read(mem_addr(2, 0x200)) == 0x1122_AA44, "byte strobe"
    for c in range(NUM_HARTS):
        st = await tb.status(c)
        assert st == {"run": 0, "halted": 0, "cause": 0, "cycles": 0, "instret": 0, "gp": 0}, \
            f"ctx {c} status after reset: {st}"
    dut._log.info("mem map: banks distinct, strobes, alias, status -- ok")


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_gatling_mem_reload(dut):
    """Context 0 runs a long loop.  Meanwhile: a write to its bank is
    dropped (acked; the program word stays), its bank still reads; context 1
    is loaded and started, and both finish golden-identical; the status
    registers report each context's halt, gp, instret and CPI 4."""
    tb = await _start(dut)
    long_loop = counted_loop(400, 3)
    short_loop = counted_loop(50, 5)
    await tb.backdoor_load(0, long_loop)
    tb.clear_traces()
    tb.set_run(0b0001)
    marks = {}

    async def meanwhile():
        # Running bank: write dropped, read served.
        word0 = long_loop[0]
        assert await tb.axil_write(mem_addr(0, 0x0), 0xDEAD_BEEF) == 0, "write ack"
        marks["running_read"] = await tb.axil_read(mem_addr(0, 0x0))
        assert marks["running_read"] == word0, \
            f"running bank changed: 0x{marks['running_read']:08x} != 0x{word0:08x}"
        # Load context 1 while 0 runs, then start it alongside.
        await tb.backdoor_load(1, short_loop)
        await tb.write_ctrl(0b0011)
        marks["ctx1_started"] = True

    helper = cocotb.start_soon(meanwhile())
    await tb.run_until_halted(0b0011, max_cycles=200_000)
    await helper
    assert marks.get("ctx1_started"), "context 1 never started"
    g0 = _check(tb, 0, long_loop)
    g1 = _check(tb, 1, short_loop)
    for c, g in ((0, g0), (1, g1)):
        st = await tb.status(c)
        assert st["halted"] and st["cause"] == 1 and st["gp"] == 1, f"ctx {c} status {st}"
        assert st["instret"] == len(g.trace), \
            f"ctx {c}: INSTRET {st['instret']} != {len(g.trace)} retirements"
        cpi = st["cycles"] / st["instret"]
        assert CPI <= cpi < CPI + 0.1, f"ctx {c}: CPI {cpi:.3f}, expected ~{CPI}"
        dut._log.info(f"ctx {c}: instret {st['instret']} cycles {st['cycles']} cpi {cpi:.3f}")
    assert not tb.harts[2].trace and not tb.harts[3].trace, "held contexts retired"
    dut._log.info("reload: running bank protected, context loaded and started live -- ok")


@cocotb.test(timeout_time=600_000, timeout_unit="ms")
async def cocotb_test_gatling_mem_battery(dut):
    """The rv32ui battery loaded and run entirely through AXIL, all four
    contexts at once."""
    level = os.environ.get("TEST_LEVEL", "gate")
    tests = {"gate": GATE_TESTS, "func": FUNC_IMAGES}.get(level)       # full: all 42
    log_dir = os.path.dirname(os.environ.get("LOG_PATH", "."))
    battery = GatlingBattery(dut, repo_root=os.environ["REPO_ROOT"], level=level,
                             work_dir=os.path.join(log_dir, "gatling_mem_battery"),
                             tests=list(tests) if tests else None, tb_class=GatlingBramTB)
    battery.title = "gatling AXIL battery"
    await battery.run()


CASES = {"cocotb_test_gatling_mem_map": 0, "cocotb_test_gatling_mem_reload": 0,
         "cocotb_test_gatling_mem_battery": LINK_BASE}


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_mem_bram {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_gatling_mem_bram(request, cocotb_testcase, test_level, description):
    gatling_sim.run_cell(
        module="test_gatling_mem_bram", testcase=cocotb_testcase,
        toplevel="gatling_bram_tb_top", filelist=gatling_sim.TB_FILELIST,
        cell=f"{cocotb_testcase}_{test_level}", test_level=test_level,
        parameters={"RESET_ADDR": str(CASES[cocotb_testcase])})
