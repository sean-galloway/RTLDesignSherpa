# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: gatling_bram_tb
# Purpose: cocotb TB class for gatling_core behind gatling_mem_bram: images
#          load and contexts run through the AXIL port (the board's path),
#          with the same per-context RVFI capture and checks as GatlingTB.
#
# Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32i
#
# Author: sean galloway
# Created: 2026-10-21

"""GatlingTB on gatling_bram_tb_top.

The register map is gatling_mem_bram's (its RTL header is the authority):
memory at addr[17] = 0 with the context bank in addr[15:14], registers at
addr[17] = 1 -- CTRL (run per context), BUILD_ID, and per context c at
0x2_0100 + 0x10*c: STATUS, CYCLES, INSTRET, GP.

Run control is a CTRL write, which takes cycles to reach the memory system,
and a context fetches RESET_ADDR the cycle the write commits.  So, as in
kestrel's loader TB, ``run_until_halted`` starts the RVFI sampler first and
issues the CTRL write from inside it.
"""

import logging

import cocotb
from cocotb.triggers import RisingEdge

from gatling.gatling_tb import ALL_HARTS, GatlingTB

AXIL_ADDR_MASK = 0x0003_FFFF
REG_CTRL = 0x2_0000
REG_BUILD_ID = 0x2_0004
BUILD_ID = 0x4741_544C            # "GATL"
BANK_SHIFT = 14                   # addr[15:14] = context bank
BANK_BYTES = 1 << BANK_SHIFT      # 16 KB per context


def hart_reg(ctx, name):
    return 0x2_0100 + 0x10 * ctx + {"STATUS": 0x0, "CYCLES": 0x4,
                                    "INSTRET": 0x8, "GP": 0xC}[name]


def mem_addr(ctx, byte_addr):
    """AXIL address of a byte address in context ``ctx``'s bank."""
    return (ctx << BANK_SHIFT) | (byte_addr % BANK_BYTES)


class GatlingBramTB(GatlingTB):
    """GatlingTB with loading and run control moved onto the AXIL port."""

    def __init__(self, dut, reset_addr=0, master=None):
        super().__init__(dut, reset_addr=reset_addr)
        if master is None:
            from CocoTBFramework.components.axil4.axil4_factories import create_axil4_master
            master = create_axil4_master(dut=dut, clock=dut.clk, prefix="s_axil_",
                                         addr_width=18, data_width=32, multi_sig=True,
                                         log=logging.getLogger("axil_gatling"))
        self.master = master
        self._run_mask = 0
        self._pending_run = None

    # ---- AXIL -------------------------------------------------------------
    async def axil_write(self, addr, data, strb=None):
        return await self.master["write_register"](addr & AXIL_ADDR_MASK, data, strb)

    async def axil_read(self, addr):
        return await self.master["read_register"](addr & AXIL_ADDR_MASK)

    async def status(self, ctx):
        st = await self.axil_read(hart_reg(ctx, "STATUS"))
        return {"run": st & 1, "halted": (st >> 1) & 1, "cause": (st >> 4) & 0xF,
                "cycles": await self.axil_read(hart_reg(ctx, "CYCLES")),
                "instret": await self.axil_read(hart_reg(ctx, "INSTRET")),
                "gp": await self.axil_read(hart_reg(ctx, "GP"))}

    async def write_ctrl(self, mask):
        self._run_mask = mask & ALL_HARTS
        await self.axil_write(REG_CTRL, self._run_mask)

    # ---- GatlingTB contract -------------------------------------------------
    async def assert_reset(self):
        self._run_mask = 0
        self.dut.rst_n.value = 0
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def release_reset(self):
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def backdoor_load(self, ctx, words):
        """Load through the AXIL port (the context must be held)."""
        for idx, word in sorted(words.items()):
            await self.axil_write(mem_addr(ctx, idx << 2), word & 0xFFFF_FFFF)

    def set_run(self, mask):
        """Deferred: the CTRL write is issued from run_until_halted, once the
        sampler is live."""
        self._pending_run = mask & ALL_HARTS

    def run_mask(self):
        return self._run_mask

    async def run_until_halted(self, mask, **kwargs):
        if self._pending_run is None:
            return await super().run_until_halted(mask, **kwargs)
        sampler = cocotb.start_soon(super().run_until_halted(mask, **kwargs))
        run, self._pending_run = self._pending_run, None
        await self.write_ctrl(run)
        await sampler
