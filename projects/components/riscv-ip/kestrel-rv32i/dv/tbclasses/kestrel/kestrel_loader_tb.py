# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: kestrel_loader_tb
# Purpose: cocotb TB class for the kestrel_mem_loader board path: the same
#          golden-trace lockstep contract as KestrelTB, but the image streams
#          through the AXIL slave port (CocoTBFramework AXIL4 master) and the
#          core leaves reset only when CTRL.run is written -- not when rst_n
#          releases.  Mutual exclusion is by protocol: while the loader is in
#          load mode (CTRL.run == 0) it owns the RAM write ports and the core
#          is held in reset.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-07

"""cocotb TB class for kestrel_core behind kestrel_mem_loader on
kestrel_loader_tb_top.

Address map driven here (AXIL addr[17:0], fixed by the Task-11 brief):

* ``0x0000_0000 .. 0x0000_FFFF`` -- imem region (64 KB of 32-bit words)
* ``0x0001_0000 .. 0x0001_FFFF`` -- dmem region (64 KB of 32-bit words)
* ``0x0002_0000``                -- CTRL register (bit 0 = run)

The two regions are one unified address space on the core side: the loader
selects imem vs dmem by address bit 16 on every port, so any flat image the
Task-8 direct-load TB accepts (code, .tohost, .data interleaved by address)
loads and executes identically through the board path.

Reset/load sequencing (used by rv32ui_battery through the tb_class hook):

* ``assert_reset``  -- rst_n low: loader run_q resets to 0, core held in
  reset.  Identical to the direct TB.
* ``backdoor_load`` -- the battery calls this while rst_n is still low, but
  the AXIL leaf slaves are in reset then, so the image is stashed here and
  streamed on ``release_reset``.
* ``release_reset`` -- rst_n high, one settle cycle, stream the stashed
  image word-by-word through the AXIL port.  Still load mode: the loader
  owns the write ports and the core stays in reset (core_rst_n == 0).
* ``run_to_halt``   -- starts the trace sampler FIRST, then writes
  CTRL.run = 1.  The core starts fetching the very cycle the run write
  commits -- before the write's B response reaches the master -- so the
  sampler must already be live or the RESET_ADDR beat is gone.  The rest
  of the contract (falling-edge sampling, halt-hold pinning, tohost
  store watch) is inherited unchanged.
"""

import logging

import cocotb
from cocotb.triggers import RisingEdge

from tbclasses.kestrel.kestrel_tb import KestrelTB

# CTRL register offset in the AXIL address map (addr[17] = 1).
CTRL_ADDR = 0x0002_0000
RUN_BIT = 0x1

# The loader decodes addr[17:0]; memory regions live below CTRL_ADDR.
AXIL_ADDR_MASK = 0x0003_FFFF
MEM_MAP_LIMIT = CTRL_ADDR


class KestrelLoaderTB(KestrelTB):
    """KestrelTB with the image-load path moved onto the AXIL port."""

    def __init__(self, dut, master=None, reset_addr=0):
        super().__init__(dut, reset_addr=reset_addr)
        if master is None:
            # The battery constructs the TB with only (dut, reset_addr=...),
            # so the AXIL master is built lazily against dut.clk.
            from CocoTBFramework.components.axil4.axil4_factories import (
                create_axil4_master,
            )
            master = create_axil4_master(dut=dut, clock=dut.clk,
                                         prefix="s_axil_", addr_width=18,
                                         data_width=32, multi_sig=True,
                                         log=logging.getLogger("axil_loader"))
        self.master = master
        self._image = None

    # ------------------------------------------------------------------
    # AXIL register access
    # ------------------------------------------------------------------

    async def axil_write(self, addr, data, strb=None):
        """One AXIL write through the framework master; strb=None = full."""
        await self.master["write_register"](addr & AXIL_ADDR_MASK, data,
                                            strb)

    async def axil_read(self, addr):
        """One AXIL read through the framework master."""
        return await self.master["read_register"](addr & AXIL_ADDR_MASK)

    # ------------------------------------------------------------------
    # Battery contract (assert_reset / backdoor_load / release_reset /
    # run_to_halt)
    # ------------------------------------------------------------------

    async def assert_reset(self):
        """rst_n low for four cycles -- loader and core both in reset."""
        self.dut.rst_n.value = 0
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def backdoor_load(self, words):
        """Stash the image; the AXIL stream happens in ``release_reset``
        because the leaf slaves cannot accept transactions in reset."""
        self._image = dict(words)

    async def release_reset(self):
        """rst_n high, one settle cycle, then stream the stashed image over
        AXIL.  Deliberately does NOT write CTRL.run: the core stays in
        reset (load mode) until ``run_to_halt`` releases it, so the sampler
        is live before the first fetch."""
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        await RisingEdge(self.dut.clk)
        if self._image is not None:
            for idx, word in sorted(self._image.items()):
                byte_addr = (idx << 2) & 0xFFFF_FFFC
                axil_addr = byte_addr & AXIL_ADDR_MASK
                assert axil_addr < MEM_MAP_LIMIT, \
                    f"image word 0x{idx:08x} maps to AXIL 0x{axil_addr:05x}, " \
                    f"past the memory map (CTRL at 0x{CTRL_ADDR:x})"
                await self.axil_write(axil_addr, word & 0xFFFF_FFFF)
            self._image = None

    async def run_to_halt(self, max_cycles=20_000, post_halt_cycles=4,
                          watch_tohost=None):
        """Sampler live first, then CTRL.run = 1, then wait for halt.

        The core fetches RESET_ADDR the cycle the run write commits -- the
        B response only reaches the master a couple of cycles later -- so
        the inherited sampling loop runs as a concurrent task that is
        started BEFORE the run write is issued.
        """
        sampler = cocotb.start_soon(
            super().run_to_halt(max_cycles=max_cycles,
                                post_halt_cycles=post_halt_cycles,
                                watch_tohost=watch_tohost))
        await self.axil_write(CTRL_ADDR, RUN_BIT)
        await sampler

    async def enter_load_mode_only(self):
        """rst_n high without releasing the core: the loader leaves reset
        but stays in load mode (CTRL.run == 0)."""
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        await RisingEdge(self.dut.clk)
