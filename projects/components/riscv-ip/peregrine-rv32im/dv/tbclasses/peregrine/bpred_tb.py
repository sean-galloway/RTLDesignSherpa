# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: bpred_tb
# Purpose: cocotb TB class for peregrine_bpred, driven in lock with
#          BpredModel one cycle at a time.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine_bpred TB: each cycle presents one lookup and at most one
update, checks the lookup against the model's pre-update state (the RTL
reads before the edge), then applies the update to both."""

from dataclasses import dataclass

from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge

from TBClasses.shared.tbbase import TBBase


@dataclass(frozen=True)
class Update:
    pc: int
    cond: bool
    uncond: bool
    taken: bool
    target: int
    pred_taken: bool


class BpredTB(TBBase):
    """Drive peregrine_bpred's lookup and update ports."""

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self._idle_update()
        dut.lookup_pc.value = 0

    def _idle_update(self) -> None:
        d = self.dut
        d.upd_valid.value = 0
        d.upd_pc.value = 0
        d.upd_cond.value = 0
        d.upd_uncond.value = 0
        d.upd_taken.value = 0
        d.upd_target.value = 0
        d.upd_pred_taken.value = 0

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

    async def cycle(self, lookup_pc: int, update) -> tuple:
        """One cycle: returns the (taken, target) the RTL predicted for
        ``lookup_pc`` before ``update`` (or None) is written."""
        d = self.dut
        await FallingEdge(d.clk)
        d.lookup_pc.value = lookup_pc
        if update is None:
            self._idle_update()
        else:
            d.upd_valid.value = 1
            d.upd_pc.value = update.pc
            d.upd_cond.value = int(update.cond)
            d.upd_uncond.value = int(update.uncond)
            d.upd_taken.value = int(update.taken)
            d.upd_target.value = update.target
            d.upd_pred_taken.value = int(update.pred_taken)
        await ReadOnly()
        got = (bool(int(d.pred_taken.value)), int(d.pred_target.value))
        await RisingEdge(d.clk)
        return got
