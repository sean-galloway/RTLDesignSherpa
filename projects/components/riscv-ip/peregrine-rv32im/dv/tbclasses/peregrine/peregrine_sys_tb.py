# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: peregrine_sys_tb
# Purpose: PeregrineTB for the cached build (peregrine_sys_tb_top,
#          TASK-001 stage 4).
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""PeregrineTB for the cached build.

The cacheless TB stops a fixed few cycles after the tohost store is issued,
which on a registered-read memory is also when it retires.  On the cached
build a store is accepted in MEM and retires only once its response is back
(the uncached port waits for B), and the riscv-tests epilogue keeps storing
to tohost in a loop.  A fixed window therefore either misses the store's
retire or counts a later loop store that has not retired, and the
memory-side-effect check (requests == retired loads/stores) is off by one
for a reason that is not a defect.

This TB stops on the tohost store's RETIRE beat (RVFI), the cycle every
accepted request has retired: the next loop store cannot be accepted before
the branch that precedes it has left MEM.

It also checks the D-side request contract inside peregrine_top (the one
amber's GAXI port needs): once the request is valid and not ready, it stays
valid with the same address, strobes and data until the handshake.  The
uncached port latches a request only at the handshake, so a dropped or
changed request is invisible in the program results; this monitor is what
sees it (the core's interrupt lock exists for exactly this rule).

``dc_clean`` drives peregrine_top's D$ clean hook: amber writes every dirty
line back, so a result the TB reads from the memory array (an arch-test
signature) is there.  ``ArchSysTB`` cleans after every tohost store.
"""

import cocotb
from cocotb.triggers import FallingEdge, ReadOnly, Timer

from tbclasses.peregrine import peregrine_tb as _base
from tbclasses.peregrine.peregrine_tb import PeregrineTB


class PeregrineSysTB(PeregrineTB):
    """Drive peregrine_sys_tb_top; stop at the tohost store's retire."""

    def __init__(self, dut, reset_addr: int = 0) -> None:
        super().__init__(dut, reset_addr=reset_addr)
        self.dport_violations: list = []
        self.dport_waits = 0
        self._dport_started = False
        dut.tb_dc_clean_req.value = 0

    async def dc_clean(self, max_cycles: int = 200_000) -> int:
        """Clean amber through the hook; return the cycles it took."""
        d = self.dut
        d.tb_dc_clean_req.value = 1
        for cycle in range(1, max_cycles + 1):
            await FallingEdge(d.clk)
            if int(d.tb_dc_clean_done.value):
                d.tb_dc_clean_req.value = 0
                await FallingEdge(d.clk)
                return cycle
        raise AssertionError(f"D$ clean not done after {max_cycles} cycles")

    def start_dport_monitor(self) -> None:
        if not self._dport_started:
            cocotb.start_soon(self._dport_monitor())
            self._dport_started = True

    async def _dport_monitor(self) -> None:
        top = self.dut.u_top
        held = None
        cycle = 0
        while True:
            await FallingEdge(self.dut.clk)
            await Timer(1, unit="ps")
            await ReadOnly()
            cycle += 1
            if not int(self.dut.rst_n.value):
                held = None
                continue
            valid = int(top.w_dvalid.value)
            ready = int(top.w_dready.value)
            req = (int(top.w_daddr.value), int(top.w_dwstrb.value), int(top.w_dwdata.value))
            if held is not None:
                if not valid:
                    self.dport_violations.append(f"cycle {cycle}: request 0x{held[0]:x} "
                                                 f"dropped before its handshake")
                elif req != held:
                    self.dport_violations.append(f"cycle {cycle}: request changed "
                                                 f"while waiting ({held} -> {req})")
            held = req if (valid and not ready) else None
            if held is not None:
                self.dport_waits += 1

    def check_dport(self) -> None:
        assert not self.dport_violations, \
            f"{len(self.dport_violations)} D-side request violations: {self.dport_violations[:3]}"

    async def run_to_tohost(self, tohost: int, max_cycles: int = 100_000,
                            irq_driver=None, mem_wait_driver=None) -> int:
        saved = _base._POST_TOHOST_CYCLES
        _base._POST_TOHOST_CYCLES = 0
        try:
            return await super().run_to_tohost(tohost, max_cycles=max_cycles,
                                               irq_driver=irq_driver,
                                               mem_wait_driver=mem_wait_driver)
        finally:
            _base._POST_TOHOST_CYCLES = saved

    def _tohost_store(self, tohost: int) -> bool:
        d = self.dut
        if not (int(d.rvfi_valid.value) and int(d.rvfi_mem_wmask.value)):
            return False
        if (int(d.rvfi_mem_addr.value) & ~0x3 & 0xFFFF_FFFF) != (tohost & ~0x3):
            return False
        mask = int(d.rvfi_mem_wmask.value)
        data = int(d.rvfi_mem_wdata.value)
        value = 0
        for b in range(4):
            if (mask >> b) & 1:
                value |= ((data >> (8 * b)) & 0xFF) << (8 * b)
        if value == 0:
            return False
        self.tohost_writes.append(value)
        return True


class ArchSysTB(PeregrineSysTB):
    """PeregrineSysTB for riscv-arch-test: the signature is read from the
    memory array after the tohost store, so clean the D$ first."""

    async def run_to_tohost(self, tohost: int, max_cycles: int = 100_000,
                            irq_driver=None, mem_wait_driver=None) -> int:
        value = await super().run_to_tohost(tohost, max_cycles=max_cycles,
                                            irq_driver=irq_driver,
                                            mem_wait_driver=mem_wait_driver)
        self.clean_cycles = await self.dc_clean()
        return value
