# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_g_regpath
# Purpose: rapids-g (rapids TASK-034): each half's gatling reads and writes its
#          own half's registers through the host's command queue
#          (rapids_g_reg_arb), while the host uses the same queue.
#
# Author: sean galloway
# Created: 2026-10-21

"""The gatling register path, end to end on rapids_g_top.

A small test program replaces the scheduler firmware in both gatlings' ROMs
(loaded during reset). Every hart loops: it reads SCHED_TIMEOUT_CYCLES of its
own half through the register mailbox, records the value and a pass count in
its scratch, and writes SCHED_TIMEOUT_LIMIT. Meanwhile the host programs a
different SCHED_TIMEOUT_CYCLES into SRC and SNK and reads both registers over
APB, hard, through the same queue.

Checks: every hart of the SRC gatling sees the SRC value and every hart of the
SNK gatling the SNK value (the same offset, so each is pinned to its half);
the gatling writes land in their own half; no mailbox access reported an
error; every host read during the contention returned what the host expects.
"""

import os
import sys
import tempfile
from pathlib import Path

import cocotb
import pytest
from cocotb.triggers import Timer

from TBClasses.shared.test_levels import reg_level_grid

from rapids_g_rehost import make_runner

REPO = os.environ.get('REPO_ROOT', str(Path(__file__).resolve().parents[7]))
sys.path.insert(0, REPO)
sys.path.insert(0, os.path.join(REPO, 'projects/components/dma-ip/rapids/bin'))

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_top_tb import RapidsTopTB  # noqa: E402

# what the gatlings write into SCHED_TIMEOUT_LIMIT: chosen by the gatling's own
# direction (CFG.EN_READ of its window), so a write that reached the other half
# would show
LIMIT_W = {'src': 0x0B, 'snk': 0x0C}
# the per-channel scratch bits: each gatling writes CH_SCRATCH3, the host
# writes CH_SCRATCH5 and each gatling reads it back
SCR_G = {'src': 0x5A, 'snk': 0xA5}
SCR_H = {'src': 0x3C, 'snk': 0xC3}
SCRATCH_WORDS = 128     # rapids_seq_g default: hart h's scratch starts at h * 128

PROGRAM = """
        .equ MBOX,    0x10003000
        .equ SCRATCH, 0x20000000
        .globl _start
_start:
        li      s0, MBOX
        li      s2, SCRATCH
        li      s3, 0                   # passes
        li      t0, 0x10000000          # slot 0 window: CFG [20] = EN_READ (the SOURCE half)
        lw      t0, 56(t0)
        srli    t0, t0, 20
        andi    t0, t0, 1
        li      s4, {val_snk}
        li      s5, {scr_snk}
        beqz    t0, 0f
        li      s4, {val_src}
        li      s5, {scr_src}
0:
loop:
        li      t0, {off_r}             # read SCHED_TIMEOUT_CYCLES
        sw      t0, 0(s0)
        li      t0, 1                   # go, read
        sw      t0, 8(s0)
1:      lw      t1, 12(s0)
        andi    t2, t1, 2               # done
        beqz    t2, 1b
        andi    t2, t1, 4               # error
        lw      t1, 16(s0)
        sw      t1, 0(s2)               # the value
        lw      t4, 8(s2)
        or      t4, t4, t2
        sw      t4, 8(s2)               # sticky error
        li      t0, {off_w}             # write SCHED_TIMEOUT_LIMIT
        sw      t0, 0(s0)
        sw      s4, 4(s0)
        li      t0, 3                   # go, write
        sw      t0, 8(s0)
2:      lw      t1, 12(s0)
        andi    t2, t1, 2
        beqz    t2, 2b
        andi    t2, t1, 4
        lw      t4, 8(s2)
        or      t4, t4, t2
        sw      t4, 8(s2)
        li      t0, {off_s3}            # write CH_SCRATCH3
        sw      t0, 0(s0)
        sw      s5, 4(s0)
        li      t0, 3
        sw      t0, 8(s0)
4:      lw      t1, 12(s0)
        andi    t2, t1, 2
        beqz    t2, 4b
        li      t0, {off_s5}            # read CH_SCRATCH5 (the host's)
        sw      t0, 0(s0)
        li      t0, 1
        sw      t0, 8(s0)
5:      lw      t1, 12(s0)
        andi    t2, t1, 2
        beqz    t2, 5b
        lw      t1, 16(s0)
        sw      t1, 12(s2)
        addi    s3, s3, 1
        sw      s3, 4(s2)               # passes
        j       loop
"""


def _seq(dut, half):
    return getattr(dut.u_base.u_core, f"u_{half}").u_scheduler_group_array.g_shared.u_seq


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_regpath(dut):
    import gen_rapids_g_fw as fw
    tb = RapidsTopTB(dut)
    off_r = tb._src_off['SCHED_TIMEOUT_CYCLES']
    off_w = tb._src_off['SCHED_TIMEOUT_LIMIT']
    assert off_r == tb._snk_off['SCHED_TIMEOUT_CYCLES'] and off_w == tb._snk_off['SCHED_TIMEOUT_LIMIT'], \
        "the two halves should place these registers at the same offset"
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / 'regpath.S'
        src.write_text(PROGRAM.format(off_r=off_r, off_w=off_w, val_src=LIMIT_W['src'], val_snk=LIMIT_W['snk'],
                                      off_s3=tb._src_off['CH_SCRATCH3_SCRATCH'], off_s5=tb._src_off['CH_SCRATCH5_SCRATCH'],
                                      scr_src=SCR_G['src'], scr_snk=SCR_G['snk']))
        words = fw.build_words(src, Path(os.environ.get('RISCV_TOOLCHAIN', fw.TOOLCHAIN_DEFAULT)))

    await tb.start_clock(tb.clk_name, freq=tb.CLK_PERIOD, units='ns')
    await tb.assert_reset()
    await tb.wait_clocks(tb.clk_name, 5)
    await Timer(1, 'ns')
    for half in ('src', 'snk'):
        rom = _seq(dut, half).r_rom
        for i, w in enumerate(words):
            rom[i].value = w
        rom[len(words)].value = 0x0000_006F               # j . (never reached)
    await tb.wait_clocks(tb.clk_name, 10)
    await tb.deassert_reset()
    await tb.wait_clocks(tb.clk_name, 15)
    tb._create_bfms()
    await tb.init_apb4_master()

    want = {'src': 0x0001_2345, 'snk': 0x0006_789A}
    for half, v in want.items():
        await tb.write_reg(half, 'SCHED_TIMEOUT_CYCLES', v)
        await tb.write_reg(half, 'CH_SCRATCH5_SCRATCH', SCR_H[half])
    # the host hammers the same queue while the harts loop
    bad_host = 0
    for _ in range(40):
        for half, v in want.items():
            got = await tb.read_reg(half, 'SCHED_TIMEOUT_CYCLES')
            bad_host += int(got != v)
    # each hart issues every NUM_HARTS clocks, so the loop's pass count scales
    # with the window: 500 clocks per hart gives every hart > 10 passes
    await tb.wait_clocks(tb.clk_name, 500 * len(_seq(dut, 'src').hart_halted))

    ok = bad_host == 0
    tb.log.info(f"host reads under contention: {80 - bad_host}/80 right")
    for half, v in want.items():
        scr = _seq(dut, half).r_scratch
        for h in range(len(_seq(dut, half).hart_halted)):     # every hart of this gatling
            val = int(scr[h * SCRATCH_WORDS + 0].value)
            passes = int(scr[h * SCRATCH_WORDS + 1].value)
            err = int(scr[h * SCRATCH_WORDS + 2].value)
            hs = int(scr[h * SCRATCH_WORDS + 3].value)
            good = (val == v) and passes > 10 and err == 0 and hs == SCR_H[half]
            ok &= good
            tb.log.info(f"{half} hart {h}: read 0x{val:08x} (want 0x{v:08x}), {passes} passes, "
                        f"error {err} -> {'ok' if good else 'FAIL'}")
        gs = await tb.read_reg(half, 'CH_SCRATCH3_SCRATCH')
        good = gs == SCR_G[half]
        ok &= good
        tb.log.info(f"{half}: CH_SCRATCH3 0x{gs:02x} from its gatling, CH_SCRATCH5 read back by the harts "
                    f"-> {'ok' if good else 'FAIL'}")
        lim = await tb.read_reg(half, 'SCHED_TIMEOUT_LIMIT')
        good = (lim & 0xFF) == LIMIT_W[half]
        ok &= good
        tb.log.info(f"{half}: SCHED_TIMEOUT_LIMIT 0x{lim:08x} after the gatling writes -> {'ok' if good else 'FAIL'}")
    assert ok, "gatling register path: see the FAIL lines"


_run_top = make_runner('test_rapids_g_regpath', {
    'DATA_WIDTH': 512, 'ADDR_WIDTH': 64, 'AXI_ID_WIDTH': 8, 'SRAM_DEPTH': 512,
    'APB_ADDR_WIDTH': 13, 'APB_DATA_WIDTH': 32,
})


@pytest.mark.top
@pytest.mark.rapids_g
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_g_regpath(request, test_level):
    """Both gatlings use their half's registers through the shared command queue."""
    _run_top("cocotb_test_regpath", "test_rapids_regpath", test_level=test_level, dut='rapids_top')
