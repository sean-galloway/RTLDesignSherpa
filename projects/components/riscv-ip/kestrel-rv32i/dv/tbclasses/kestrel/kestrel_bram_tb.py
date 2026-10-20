# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: kestrel_bram_tb
# Purpose: cocotb TB class for kestrel_core behind kestrel_mem_bram (the
#          registered-read block-RAM path).  The loader TB's contract carries
#          over unchanged -- same AXIL map, same load/run sequencing, same
#          RVFI lockstep -- with a cycle budget scaled for CPI 2-3 and the
#          wrapper's status registers.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-20
"""KestrelLoaderTB on kestrel_bram_tb_top.

The wrapper holds the core with mem_wait for one cycle per fetch and one
more per load, so a program needs up to three clocks per instruction; every
cycle budget the inherited contract passes is scaled by ``CPI_MAX``.
"""

from tbclasses.kestrel.kestrel_loader_tb import CTRL_ADDR, KestrelLoaderTB

CPI_MAX = 3

# kestrel_mem_bram registers (addr[17] = 1, addr[4:2] selects)
REG_CTRL = CTRL_ADDR + 0x0
REG_CYCLES = CTRL_ADDR + 0x4
REG_INSTRET = CTRL_ADDR + 0x8
REG_GP = CTRL_ADDR + 0xC
REG_BUILD_ID = CTRL_ADDR + 0x10
BUILD_ID = 0x4B42_524D   # "KBRM"


class KestrelBramTB(KestrelLoaderTB):
    """KestrelLoaderTB with the block-RAM wrapper's timing and registers."""

    async def run_to_halt(self, max_cycles=20_000, post_halt_cycles=4,
                          watch_tohost=None):
        return await super().run_to_halt(max_cycles=max_cycles * CPI_MAX,
                                         post_halt_cycles=post_halt_cycles,
                                         watch_tohost=watch_tohost)

    async def status(self):
        """{run, halted, cause, cycles, instret, gp} from the wrapper."""
        ctrl = await self.axil_read(REG_CTRL)
        return {"run": ctrl & 1, "halted": (ctrl >> 1) & 1, "cause": (ctrl >> 4) & 0xF,
                "cycles": await self.axil_read(REG_CYCLES),
                "instret": await self.axil_read(REG_INSTRET),
                "gp": await self.axil_read(REG_GP)}

    async def stop(self):
        """CTRL.run = 0: back to load mode, the core held in reset."""
        await self.axil_write(REG_CTRL, 0)
