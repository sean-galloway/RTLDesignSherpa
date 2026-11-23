# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: peregrine_tb
# Purpose: cocotb TB class for peregrine_core on peregrine_tb_top: clock,
#          reset, backdoor image load, interrupt pins, and the RVFI retire
#          trace up to the riscv-tests tohost store.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""cocotb TB class for peregrine_core.

peregrine has no halt: ecall, ebreak and every other exception trap to
mtvec.  A program ends when it stores to the riscv-tests ``tohost``
mailbox; the TB watches the store port for that write and keeps running a
few cycles so the store itself retires on RVFI.
"""

from typing import Callable, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge

# Cycles to keep sampling after the tohost store is seen in MEM, so the
# store (and anything already in the pipe) retires into the trace.
_POST_TOHOST_CYCLES = 4

IrqDriver = Callable[[object, int, list], tuple]


class PeregrineTB:
    """Drive peregrine_tb_top and capture the core's RVFI retire trace."""

    def __init__(self, dut, reset_addr: int = 0) -> None:
        self.dut = dut
        self.reset_addr = reset_addr
        self.trace: list = []
        self.tohost_writes: list = []
        self._clock_started = False
        dut.tb_mem_we.value = 0
        dut.mem_wait.value = 0
        self.set_irqs(0, 0, 0)

    def set_irqs(self, software: int, timer: int, external: int) -> None:
        self.dut.irq_software.value = software
        self.dut.irq_timer.value = timer
        self.dut.irq_external.value = external

    async def ensure_clock(self) -> None:
        if not self._clock_started:
            cocotb.start_soon(Clock(self.dut.clk, 10, unit="ns").start())
            self._clock_started = True

    async def assert_reset(self) -> None:
        self.dut.rst_n.value = 0
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def release_reset(self) -> None:
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1

    async def backdoor_load(self, words: dict) -> None:
        """Write a {word_index: word} image through the TB backdoor port."""
        dut = self.dut
        for idx, word in sorted(words.items()):
            await FallingEdge(dut.clk)
            dut.tb_mem_we.value = 1
            dut.tb_mem_addr.value = (idx << 2) & 0xFFFF_FFFC
            dut.tb_mem_wdata.value = word
        await FallingEdge(dut.clk)
        dut.tb_mem_we.value = 0

    async def run_to_tohost(self, tohost: int, max_cycles: int = 100_000,
                            irq_driver: Optional[IrqDriver] = None,
                            mem_wait_driver: Optional[Callable] = None) -> int:
        """Run until the first non-zero store to ``tohost``; return its value.

        Each cycle: at the falling edge the TB drives the interrupt pins and
        mem_wait; in the ReadOnly phase that follows it samples RVFI and the
        data port, so every sample is the value the memory sees at the next
        rising edge (sampling right after the writes would read the stale
        pre-write values).

        ``irq_driver(dut, cycle, trace) -> (msi, mti, mei)`` is called in the
        ReadOnly phase, observing this cycle; its result drives the pins from
        the next falling edge, so the pins are registered like a real CLINT.
        ``mem_wait_driver(dut, cycle) -> bool`` asserts mem_wait for a cycle.
        """
        dut = self.dut
        self.trace = []
        self.tohost_writes = []
        self.mem_requests = 0
        stop_at = None
        pins = (0, 0, 0)
        for cycle in range(max_cycles):
            await FallingEdge(dut.clk)
            self.set_irqs(*pins)
            dut.mem_wait.value = int(bool(mem_wait_driver and
                                          mem_wait_driver(dut, cycle)))
            await ReadOnly()
            if irq_driver is not None:
                pins = irq_driver(dut, cycle, self.trace)
            if int(dut.rvfi_valid.value):
                self.trace.append(self._sample_beat(cycle))
            if int(dut.dmem_req.value):
                self.mem_requests += 1
            if stop_at is None and self._tohost_store(tohost):
                stop_at = cycle + _POST_TOHOST_CYCLES
            if stop_at is not None and cycle >= stop_at:
                await FallingEdge(dut.clk)      # leave the ReadOnly phase
                return self.tohost_writes[-1]
        last_pc = self.trace[-1]["pc"] if self.trace else 0
        raise AssertionError(
            f"no tohost write after {max_cycles} cycles "
            f"(last pc=0x{last_pc:x}, {len(self.trace)} beats)")

    def _tohost_store(self, tohost: int) -> bool:
        dut = self.dut
        if not (int(dut.dmem_req.value) and int(dut.dmem_wstrb.value)):
            return False
        if (int(dut.dmem_addr.value) & ~0x3 & 0xFFFF_FFFF) != (tohost & ~0x3):
            return False
        strobe = int(dut.dmem_wstrb.value)
        data = int(dut.dmem_wdata.value)
        value = 0
        for b in range(4):
            if (strobe >> b) & 1:
                value |= ((data >> (8 * b)) & 0xFF) << (8 * b)
        if value == 0:
            return False
        self.tohost_writes.append(value)
        return True

    def _sample_beat(self, cycle: int) -> dict:
        d = self.dut
        return {
            "order": int(d.rvfi_order.value),
            "pc": int(d.rvfi_pc_rdata.value),
            "insn": int(d.rvfi_insn.value),
            "trap": int(d.rvfi_trap.value),
            "trap_cause": int(d.rvfi_trap_cause.value),
            "rd_addr": int(d.rvfi_rd_addr.value),
            "rd_wdata": int(d.rvfi_rd_wdata.value),
            "pc_wdata": int(d.rvfi_pc_wdata.value),
            "mem_addr": int(d.rvfi_mem_addr.value),
            "mem_rmask": int(d.rvfi_mem_rmask.value),
            "mem_wmask": int(d.rvfi_mem_wmask.value),
            "cycle": cycle,
        }

    # ------------------------------------------------------------------
    # Trace checks shared by every peregrine test
    # ------------------------------------------------------------------

    def check_order_sequence(self) -> None:
        for i, beat in enumerate(self.trace):
            assert beat["order"] == i, \
                f"beat {i}: rvfi_order={beat['order']} expected {i}"

    def check_x0_rd_zero(self) -> None:
        for i, beat in enumerate(self.trace):
            if beat["rd_addr"] == 0:
                assert beat["rd_wdata"] == 0, \
                    f"beat {i}: rd_addr=0 but rd_wdata=0x{beat['rd_wdata']:x}"

    def check_mem_side_effects(self) -> None:
        """Every data-memory request belongs to a retired, non-trapping
        load or store: a trapped or interrupted instruction issues none.

        The program's own checks cannot see a doubled store (writing the
        same value twice is idempotent); this count can.
        """
        retired = sum(1 for b in self.trace if b["mem_rmask"] or b["mem_wmask"])
        assert self.mem_requests == retired, \
            f"{self.mem_requests} data-memory requests, {retired} retired " \
            f"loads/stores: a squashed instruction touched memory"

    def check_trap_beats(self) -> None:
        """A trap beat writes nothing, and the next beat is at its target."""
        for i, beat in enumerate(self.trace):
            if not beat["trap"]:
                continue
            assert beat["rd_addr"] == 0 and beat["mem_rmask"] == 0 and \
                beat["mem_wmask"] == 0, \
                f"beat {i} (trap at 0x{beat['pc']:x}) reports a write/access"
            if i + 1 < len(self.trace):
                nxt = self.trace[i + 1]["pc"]
                assert nxt == beat["pc_wdata"], \
                    f"beat {i}: trap target 0x{beat['pc_wdata']:x}, next " \
                    f"beat at 0x{nxt:x}"
