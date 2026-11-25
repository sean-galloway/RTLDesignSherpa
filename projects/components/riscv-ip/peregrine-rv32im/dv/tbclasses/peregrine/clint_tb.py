# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: clint_tb
# Purpose: Unit TB for peregrine_clint (PRD P7, TASK-001 stage 4).
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine_clint unit TB.

The CLINT port is a one-cycle register access (valid, always ready, the
response the next cycle), the D-side wrapper's request beat; there is no
ready to handshake, so the TB drives it directly at the falling edge.  A
cycle model of the CLINT runs alongside: every response, irq_software and
irq_timer are compared with it on every cycle.
"""

import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge, Timer

MSIP, CMP_LO, CMP_HI, TIME_LO, TIME_HI = 0x0000, 0x4000, 0x4004, 0xBFF8, 0xBFFC
M32, M64 = (1 << 32) - 1, (1 << 64) - 1


def _merge(old: int, new: int, strb: int) -> int:
    out = old
    for b in range(4):
        if (strb >> b) & 1:
            out = (out & ~(0xFF << (8 * b))) | (new & (0xFF << (8 * b)))
    return out


class ClintModel:
    def __init__(self, div: int) -> None:
        self.div = div
        self.cnt = 0
        self.msip = 0
        self.cmp = M64
        self.time = 0
        self.irq_timer = 0
        self.rsp = None          # (valid, data) after this edge

    def edge(self, req):
        """Advance one clock; req = None or (addr, we, strb, wdata)."""
        tick = self.cnt == self.div - 1
        self.cnt = 0 if tick else self.cnt + 1
        old_time, old_cmp, old_msip = self.time, self.cmp, self.msip
        time = old_time
        wrote_time = False
        rdata = 0
        if req is not None:
            addr, we, strb, wdata = req
            off = addr & 0xFFFC
            if we:
                if off == TIME_LO:
                    time = (old_time & ~M32) | _merge(old_time & M32, wdata, strb)
                    wrote_time = True
                elif off == TIME_HI:
                    time = (old_time & M32) | (_merge(old_time >> 32, wdata, strb) << 32)
                    wrote_time = True
                elif off == MSIP and strb & 1:
                    self.msip = wdata & 1
                elif off == CMP_LO:
                    self.cmp = (old_cmp & ~M32) | _merge(old_cmp & M32, wdata, strb)
                elif off == CMP_HI:
                    self.cmp = (old_cmp & M32) | (_merge(old_cmp >> 32, wdata, strb) << 32)
            else:
                rdata = {MSIP: old_msip, CMP_LO: old_cmp & M32, CMP_HI: old_cmp >> 32,
                         TIME_LO: old_time & M32, TIME_HI: old_time >> 32}.get(off, 0)
        if not wrote_time and tick:
            time = (old_time + 1) & M64
        self.time = time
        self.irq_timer = int(old_time >= old_cmp)
        self.rsp = (int(req is not None), rdata)


class ClintTB:
    def __init__(self, dut, div: int = 1, seed: int = 1) -> None:
        self.dut = dut
        self.rng = random.Random(seed)
        self.model = ClintModel(div)
        self.checks = 0

    async def setup_clocks_and_reset(self) -> None:
        cocotb.start_soon(Clock(self.dut.clk, 10, unit="ns").start())
        self._drive(None)
        await self.assert_reset()
        for _ in range(4):
            await RisingEdge(self.dut.clk)
        await self.deassert_reset()

    async def assert_reset(self) -> None:
        self.dut.rst_n.value = 0

    async def deassert_reset(self) -> None:
        await FallingEdge(self.dut.clk)
        self.dut.rst_n.value = 1

    def _drive(self, req) -> None:
        d = self.dut
        if req is None:
            d.req_valid.value = 0
            d.req_addr.value = 0
            d.req_we.value = 0
            d.req_wstrb.value = 0
            d.req_wdata.value = 0
        else:
            addr, we, strb, wdata = req
            d.req_valid.value = 1
            d.req_addr.value = addr
            d.req_we.value = we
            d.req_wstrb.value = strb
            d.req_wdata.value = wdata

    async def step(self, req=None) -> None:
        """Drive ``req`` for one cycle, then check the DUT against the model
        in the following cycle."""
        d = self.dut
        self._drive(req)
        await RisingEdge(d.clk)
        self.model.edge(req)
        await Timer(1, unit="ps")
        await ReadOnly()
        valid, data = self.model.rsp
        assert int(d.rsp_valid.value) == valid, "rsp_valid differs from the model"
        if valid and not (req and req[1]):
            got = int(d.rsp_rdata.value)
            assert got == data, f"read 0x{req[0]:04x}: 0x{got:08x}, model 0x{data:08x}"
        assert int(d.irq_software.value) == self.model.msip, "irq_software differs"
        assert int(d.irq_timer.value) == self.model.irq_timer, "irq_timer differs"
        self.checks += 1
        await FallingEdge(d.clk)

    def random_req(self):
        r = self.rng
        if r.random() < 0.4:
            return None
        off = r.choice([MSIP, CMP_LO, CMP_HI, TIME_LO, TIME_HI, 0x0008, 0x8000])
        we = int(r.random() < 0.4)
        strb = r.choice([0xF, 0xF, 0x1, 0x3, 0xC, 0x8])
        # Keep mtimecmp near mtime so the comparator flips both ways.
        if we and off == CMP_LO:
            wdata = (self.model.time + r.randint(-20, 40)) & M32
        elif we and off in (CMP_HI, TIME_HI):
            wdata = r.choice([0, 0, self.model.time >> 32, M32])
        else:
            wdata = r.getrandbits(32)
        return (off, we, strb, wdata)
