# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: mdu_tb
# Purpose: cocotb TB class for peregrine_mdu (the iterative M unit) and the
#          M-extension reference model the core-level tests share.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""peregrine_mdu TB and the RV32M reference model.

``m_ref`` is the unprivileged spec's definition, written from the division
table (PRD §3) rather than from the RTL's algorithm: Python integers, signed
interpretation by explicit two's-complement conversion, truncating division.
The TB drives the unit's start / cancel / consume handshake the way
peregrine_core does and measures the stall cycles of every operation.
"""

from dataclasses import dataclass

from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge

from TBClasses.shared.tbbase import TBBase

MASK32 = 0xFFFF_FFFF
INT_MIN = 0x8000_0000

M_OPS = ("mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu")

# Stall cycles the core spends with an M instruction in EX (PRD P8).
ITERATIVE_STALL = 33      # start + 32 radix-2 steps
EARLY_OUT_STALL = 1       # divide by zero, signed overflow
DSP_MUL_STALL = 2         # start + one registered product


def _signed(x: int) -> int:
    return x - (1 << 32) if x & INT_MIN else x


def _trunc_div(n: int, d: int) -> int:
    """Integer division rounding toward zero (the RISC-V definition)."""
    q = abs(n) // abs(d)
    return q if (n >= 0) == (d >= 0) else -q


def m_ref(funct3: int, a: int, b: int) -> int:
    """RV32M result of funct3 on 32-bit rs1=a, rs2=b (unprivileged spec)."""
    sa, sb = _signed(a), _signed(b)
    if funct3 == 0:
        return (a * b) & MASK32
    if funct3 == 1:
        return ((sa * sb) >> 32) & MASK32
    if funct3 == 2:
        return ((sa * b) >> 32) & MASK32
    if funct3 == 3:
        return ((a * b) >> 32) & MASK32
    if funct3 == 4:
        if b == 0:
            return MASK32
        if a == INT_MIN and b == MASK32:
            return INT_MIN
        return _trunc_div(sa, sb) & MASK32
    if funct3 == 5:
        return MASK32 if b == 0 else a // b
    if funct3 == 6:
        if b == 0:
            return a
        if a == INT_MIN and b == MASK32:
            return 0
        return (sa - sb * _trunc_div(sa, sb)) & MASK32
    if funct3 == 7:
        return a if b == 0 else a % b
    raise ValueError(f"funct3 {funct3}")


def expected_stall(funct3: int, b: int, a: int, mul_dsp: bool) -> int:
    """Stall cycles the unit should take for this operation."""
    if funct3 & 4:
        early = b == 0 or (not (funct3 & 1) and a == INT_MIN and b == MASK32)
        return EARLY_OUT_STALL if early else ITERATIVE_STALL
    return DSP_MUL_STALL if mul_dsp else ITERATIVE_STALL


@dataclass(frozen=True)
class OpResult:
    result: int
    stall: int


class MduTB(TBBase):
    """Drive peregrine_mdu's handshake as peregrine_core does."""

    # A runaway guard, not a latency expectation: the longest legal
    # operation is ITERATIVE_STALL.
    _MAX_WAIT = 64

    def __init__(self, dut) -> None:
        super().__init__(dut)
        dut.start.value = 0
        dut.cancel.value = 0
        dut.consume.value = 0
        dut.funct3.value = 0
        dut.a.value = 0
        dut.b.value = 0

    async def setup_clocks_and_reset(self) -> None:
        await self.start_clock("clk", 10, "ns")
        await self.assert_reset()
        await self.wait_clocks("clk", 5)
        await self.deassert_reset()
        await self.wait_clocks("clk", 2)

    async def assert_reset(self) -> None:
        self.dut.rst_n.value = 0

    async def deassert_reset(self) -> None:
        self.dut.rst_n.value = 1

    async def _sample(self) -> tuple:
        await ReadOnly()
        d = self.dut
        return int(d.idle.value), int(d.done.value), int(d.result.value)

    async def start_op(self, funct3: int, a: int, b: int) -> None:
        """Present an operation with start high for one edge."""
        await FallingEdge(self.dut.clk)
        self.dut.funct3.value = funct3
        self.dut.a.value = a
        self.dut.b.value = b
        self.dut.start.value = 1
        await RisingEdge(self.dut.clk)
        await FallingEdge(self.dut.clk)
        self.dut.start.value = 0
        # The core changes the operands once the producers drain; the unit
        # must have latched them.
        self.dut.a.value = (~a) & MASK32
        self.dut.b.value = (~b) & MASK32

    async def wait_done(self) -> tuple:
        """(stall cycles, result): the start edge plus every edge until done.

        Returns inside the ReadOnly phase of the cycle done was seen in.
        """
        stall = 1
        while True:
            _, done, result = await self._sample()
            if done:
                return stall, result
            assert stall < self._MAX_WAIT, "M unit never finished"
            await RisingEdge(self.dut.clk)
            stall += 1

    async def run_op(self, funct3: int, a: int, b: int, hold: int = 0) -> OpResult:
        """One operation; ``hold`` cycles of done-without-consume first."""
        await self.start_op(funct3, a, b)
        stall, result = await self.wait_done()
        for _ in range(hold):
            await FallingEdge(self.dut.clk)
            self.dut.start.value = 1          # a start while done is ignored
            await RisingEdge(self.dut.clk)
            idle, done, held = await self._sample()
            assert done and not idle and held == result, \
                "done result not held while unconsumed"
        await FallingEdge(self.dut.clk)
        self.dut.start.value = 0
        self.dut.consume.value = 1
        await RisingEdge(self.dut.clk)
        await FallingEdge(self.dut.clk)
        self.dut.consume.value = 0
        idle, done, _ = await self._sample()
        assert idle and not done, "unit not idle after consume"
        return OpResult(result=result, stall=stall)

    async def cancel_after(self, funct3: int, a: int, b: int, cycles: int) -> None:
        """Start an operation and cancel it ``cycles`` edges later."""
        await self.start_op(funct3, a, b)
        for _ in range(cycles):
            await RisingEdge(self.dut.clk)
        await FallingEdge(self.dut.clk)
        self.dut.cancel.value = 1
        await RisingEdge(self.dut.clk)
        await FallingEdge(self.dut.clk)
        self.dut.cancel.value = 0
        idle, done, _ = await self._sample()
        assert idle and not done, f"unit not idle after a cancel at +{cycles}"
