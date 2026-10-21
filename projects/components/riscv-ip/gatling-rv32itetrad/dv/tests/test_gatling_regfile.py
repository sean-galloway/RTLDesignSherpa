# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gatling_regfile
# Purpose: Unit tests for gatling_regfile: the four context register files
#          (registered read, x0 reads zero in every context, contexts
#          isolated, two read ports independent of the write port).
#
# Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32itetrad
#
# Created: 2026-10-21

"""gatling_regfile unit tests.

The contract under test: an address presented before a rising edge reads
out after it (one cycle, both ports); entry 0 of every context reads zero
whatever was written to it; a write to one context never disturbs another;
and the barrel's real access pattern -- read context D while writing context
W != D on the same edge -- returns the pre-existing value of the read
context.  gate: directed sweep; func/full add seeded random traffic against
a Python model.
"""

import os
import random

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge

import gatling_sim  # noqa: F401  (paths)
from TBClasses.shared.test_levels import reg_level_grid

N_CTX = 4
N_REG = 32
RANDOM_OPS = {"gate": 0, "func": 2_000, "full": 20_000}


class RegfileModel:
    def __init__(self):
        self.regs = {}

    def write(self, ctx, addr, data):
        self.regs[(ctx, addr)] = data

    def read(self, ctx, addr):
        return 0 if addr == 0 else self.regs.get((ctx, addr))


async def _cycle(dut, rs=None, wr=None):
    """One clock: present a read {ctx, rs1, rs2} and/or a write {ctx, rd,
    data}; return the two read ports AFTER the edge (the registered data)."""
    await FallingEdge(dut.clk)
    if rs is not None:
        dut.rs_ctx.value, dut.rs1_addr.value, dut.rs2_addr.value = rs
    if wr is not None:
        dut.rd_ctx.value, dut.rd_addr.value, dut.rd_data.value = wr
        dut.rd_wen.value = 1
    else:
        dut.rd_wen.value = 0
    await RisingEdge(dut.clk)
    await FallingEdge(dut.clk)
    dut.rd_wen.value = 0
    return int(dut.rs1_data.value), int(dut.rs2_data.value)


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_gatling_regfile(dut):
    level = os.environ.get("TEST_LEVEL", "gate")
    seed = int(os.environ.get("SEED", "1"))
    rng = random.Random(seed)
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    for sig in (dut.rs_ctx, dut.rs1_addr, dut.rs2_addr, dut.rd_ctx, dut.rd_addr,
                dut.rd_data, dut.rd_wen):
        sig.value = 0
    model = RegfileModel()

    # Every entry of every context, a distinct value (entry 0 included).
    for ctx in range(N_CTX):
        for r in range(N_REG):
            value = (0xC0DE_0000 | (ctx << 8) | r) ^ (r << 20)
            await _cycle(dut, wr=(ctx, r, value))
            model.write(ctx, r, value)

    # Read back on both ports: registered, contexts isolated, x0 zero.
    for ctx in range(N_CTX):
        for r in range(N_REG):
            r2 = (N_REG - 1) - r
            got1, got2 = await _cycle(dut, rs=(ctx, r, r2))
            assert got1 == model.read(ctx, r), \
                f"rs1 ctx{ctx} x{r}: 0x{got1:08x} expected 0x{model.read(ctx, r):08x}"
            assert got2 == model.read(ctx, r2), \
                f"rs2 ctx{ctx} x{r2}: 0x{got2:08x} expected 0x{model.read(ctx, r2):08x}"

    # The barrel's pattern: read context D while W writes context D+2 on the
    # same edge -- the read sees D's value, the write lands in W's context.
    for ctx in range(N_CTX):
        w_ctx = (ctx + 2) % N_CTX
        got1, _ = await _cycle(dut, rs=(ctx, 7, 0), wr=(w_ctx, 7, 0x5A5A_0000 | w_ctx))
        assert got1 == model.read(ctx, 7), f"read ctx{ctx} during a write to ctx{w_ctx}"
        model.write(w_ctx, 7, 0x5A5A_0000 | w_ctx)
    for ctx in range(N_CTX):
        got1, _ = await _cycle(dut, rs=(ctx, 7, 0))
        assert got1 == model.read(ctx, 7), f"ctx{ctx} x7 after the cross-context writes"

    # Seeded random traffic against the model (func/full).  A read of a
    # never-written entry is unspecified (no reset) and skipped.
    for _ in range(RANDOM_OPS.get(level, 0)):
        rs = (rng.randrange(N_CTX), rng.randrange(N_REG), rng.randrange(N_REG))
        wr = None
        if rng.random() < 0.5:
            w_ctx = rng.choice([c for c in range(N_CTX) if c != rs[0]])
            wr = (w_ctx, rng.randrange(N_REG), rng.getrandbits(32))
        expect = (model.read(rs[0], rs[1]), model.read(rs[0], rs[2]))
        got = await _cycle(dut, rs=rs, wr=wr)
        if wr is not None:
            model.write(*wr)
        for port, (g, e) in enumerate(zip(got, expect), start=1):
            if e is not None:
                assert g == e, f"random: rs{port} ctx{rs[0]}: 0x{g:08x} expected 0x{e:08x}"

    dut._log.info(f"gatling_regfile PASSED ({level}, {RANDOM_OPS.get(level, 0)} random ops)")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_regfile {lvl}") for lvl in reg_level_grid()])
def test_gatling_regfile(request, test_level, description):
    gatling_sim.run_cell(
        module="test_gatling_regfile", testcase="cocotb_test_gatling_regfile",
        toplevel="gatling_regfile",
        filelist="projects/components/riscv-ip/gatling-rv32itetrad/rtl/filelists/fub/gatling_regfile.f",
        cell=f"test_gatling_regfile_{test_level}", test_level=test_level)
