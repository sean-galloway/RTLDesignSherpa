# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: gatling_tb
# Purpose: cocotb TB class for gatling_core on gatling_tb_top: per-context
#          image loading and run control, the RVFI stream demultiplexed into
#          one trace per context, and the barrel's own checks (rotation,
#          one retirement per context per four-cycle window, halted contexts
#          retire nothing).
#
# Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32itetrad
#
# Author: sean galloway
# Created: 2026-10-21

"""cocotb TB class for the gatling barrel.

Each context's architectural behavior is exactly a kestrel's (PRD 3), so a
context's trace is checked with kestrel's own trace checks: ``HartTrace``
carries one context's beats, halt cause and halt pc, and inherits
``KestrelTB``'s check methods (they read only those attributes).  The golden
interpreter and spike lockstep are kestrel's too.

Sampling model: RVFI beats come from the W stage, at most one per cycle,
tagged with ``rvfi_ctx``.  Sampling on the falling edge sees a settled cycle.
A context's halt is recorded from its trap beat (``rvfi_trap``) -- the same
cycle its ``halted`` bit rises.
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge, Timer

from tbclasses.kestrel.kestrel_tb import KestrelTB

NUM_HARTS = 4
ALL_HARTS = (1 << NUM_HARTS) - 1
CPI = NUM_HARTS          # one retirement per context per rotation window


class HartTrace(KestrelTB):
    """One context's retire trace, checked with KestrelTB's methods.

    Deliberately does not call ``KestrelTB.__init__``: there is no per-hart
    DUT to drive, only the attributes the inherited checks read.
    """

    def __init__(self, ctx, reset_addr):          # pylint: disable=super-init-not-called
        self.ctx = ctx
        self.reset_addr = reset_addr
        self.trace = []
        self.cycles = []          # sample cycle of each beat
        self.halt_cause = None
        self.halt_pc = None
        self.tohost_writes = []


class GatlingTB:
    """Drive gatling_tb_top: load per context, run a context mask, collect."""

    def __init__(self, dut, reset_addr=0):
        self.dut = dut
        self.reset_addr = reset_addr
        self.harts = [HartTrace(c, reset_addr) for c in range(NUM_HARTS)]
        self.retire_ctx = []      # ctx of every beat, in order (rotation check)
        self._clock_started = False
        # gatling_tb_top drives run and the backdoor from here; on
        # gatling_bram_tb_top both belong to the memory system (AXIL).
        if hasattr(dut, "tb_mem_we"):
            dut.tb_mem_we.value = 0
            dut.hart_run.value = 0

    # ------------------------------------------------------------------
    # Clock / reset / loading / run control
    # ------------------------------------------------------------------

    async def ensure_clock(self):
        if not self._clock_started:
            cocotb.start_soon(Clock(self.dut.clk, 10, units="ns").start())
            self._clock_started = True

    async def assert_reset(self):
        """Global reset and every context held."""
        self.dut.hart_run.value = 0
        self.dut.rst_n.value = 0
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def release_reset(self):
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        # reset_sync N=3: let the core leave reset before anything starts.
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def backdoor_load(self, ctx, words):
        """Write a {word_index: word} image into context ``ctx``'s bank, one
        word per cycle.  The context must be held."""
        dut = self.dut
        for idx, word in sorted(words.items()):
            await FallingEdge(dut.clk)
            dut.tb_mem_we.value = 1
            dut.tb_mem_ctx.value = ctx
            dut.tb_mem_addr.value = (idx << 2) & 0xFFFF_FFFC
            dut.tb_mem_wdata.value = word
        await FallingEdge(dut.clk)
        dut.tb_mem_we.value = 0

    def set_run(self, mask):
        self.dut.hart_run.value = mask & ALL_HARTS

    def run_mask(self):
        return int(self.dut.hart_run.value)

    # ------------------------------------------------------------------
    # Trace capture
    # ------------------------------------------------------------------

    def clear_traces(self, mask=ALL_HARTS):
        for c in range(NUM_HARTS):
            if (mask >> c) & 1:
                self.harts[c] = HartTrace(c, self.reset_addr)
        self.retire_ctx = []

    def halted_mask(self):
        return int(self.dut.halted.value)

    async def run_until_halted(self, mask, max_cycles=400_000,
                               post_halt_cycles=8, watch_tohost=None,
                               on_cycle=None):
        """Sample every cycle until every context in ``mask`` has halted.

        ``watch_tohost`` maps ctx -> tohost byte address; committed stores to
        that word are recorded per context.  ``on_cycle(cycle)`` is awaited
        each cycle (run-control tests use it to stop/start contexts); the
        sample then waits 1 ns so it sees the combinational effect of what
        the hook drove -- a read in the same timestep as the write returns
        the pre-write value, which would let a leaked beat pass as stale.
        After the last halt, ``post_halt_cycles`` more cycles pin that a
        halted context neither retires nor drops its halt.
        """
        dut = self.dut
        done = 0
        cycle = 0
        for cycle in range(max_cycles):
            await FallingEdge(dut.clk)
            if on_cycle is not None:
                await on_cycle(cycle)
                await Timer(1, units="ns")
            self._sample(cycle, watch_tohost)
            for c in range(NUM_HARTS):
                if (mask >> c) & 1 and self.harts[c].halt_cause is not None:
                    done |= 1 << c
            if done == mask:
                break
        else:
            pending = [c for c in range(NUM_HARTS) if (mask >> c) & 1 and not (done >> c) & 1]
            last = {c: hex(self.harts[c].trace[-1]["pc"]) if self.harts[c].trace else None
                    for c in pending}
            raise AssertionError(
                f"contexts {pending} not halted after {max_cycles} cycles (last pc {last})")

        for _ in range(post_halt_cycles):
            await FallingEdge(dut.clk)
            cycle += 1
            for c in range(NUM_HARTS):
                if (mask >> c) & 1:
                    assert (self.halted_mask() >> c) & 1, f"ctx {c}: halt dropped"
                    if int(dut.rvfi_valid.value):
                        assert int(dut.rvfi_ctx.value) != c, \
                            f"ctx {c} retired after its halt"
            self._sample(cycle, watch_tohost)

    def _sample(self, cycle, watch_tohost):
        dut = self.dut
        if watch_tohost and int(dut.dmem_req.value) and int(dut.dmem_wstrb.value):
            c = int(dut.dmem_ctx.value)
            addr = watch_tohost.get(c)
            if addr is not None and (int(dut.dmem_addr.value) & 0xFFFC) == (addr & 0xFFFC):
                strobe = int(dut.dmem_wstrb.value)
                data = int(dut.dmem_wdata.value)
                value = 0
                for b in range(4):
                    if (strobe >> b) & 1:
                        value |= ((data >> (8 * b)) & 0xFF) << (8 * b)
                self.harts[c].tohost_writes.append(value)
        if not int(dut.rvfi_valid.value):
            return
        c = int(dut.rvfi_ctx.value)
        hart = self.harts[c]
        beat = self._sample_beat()
        hart.trace.append(beat)
        hart.cycles.append(cycle)
        self.retire_ctx.append(c)
        if beat["trap"]:
            hart.halt_pc = beat["pc"]
            hart.halt_cause = (int(dut.halt_cause.value) >> (4 * c)) & 0xF

    def _sample_beat(self):
        d = self.dut
        return {
            "order": int(d.rvfi_order.value),
            "pc": int(d.rvfi_pc_rdata.value),
            "insn": int(d.rvfi_insn.value),
            "trap": int(d.rvfi_trap.value),
            "rs1_addr": int(d.rvfi_rs1_addr.value),
            "rs2_addr": int(d.rvfi_rs2_addr.value),
            "rs1_rdata": int(d.rvfi_rs1_rdata.value),
            "rs2_rdata": int(d.rvfi_rs2_rdata.value),
            "rd_addr": int(d.rvfi_rd_addr.value),
            "rd_wdata": int(d.rvfi_rd_wdata.value),
            "pc_wdata": int(d.rvfi_pc_wdata.value),
            "mem_addr": int(d.rvfi_mem_addr.value),
            "mem_rmask": int(d.rvfi_mem_rmask.value),
            "mem_wmask": int(d.rvfi_mem_wmask.value),
            "mem_rdata": int(d.rvfi_mem_rdata.value),
            "mem_wdata": int(d.rvfi_mem_wdata.value),
        }

    # ------------------------------------------------------------------
    # Barrel checks
    # ------------------------------------------------------------------

    def check_window(self, ctx):
        """A running context retires exactly once per rotation window: its
        consecutive beats are CPI cycles apart."""
        cycles = self.harts[ctx].cycles
        for i in range(1, len(cycles)):
            gap = cycles[i] - cycles[i - 1]
            assert gap == CPI, \
                f"ctx {ctx} beat {i}: {gap} cycles after the previous, expected {CPI}"

    def check_rotation(self):
        """While several contexts run, retirements follow the rotation: each
        beat's context is the previous one's plus the cycle distance."""
        flat = sorted((cyc, c) for c in range(NUM_HARTS)
                      for cyc in self.harts[c].cycles)
        for (c0_cyc, c0), (c1_cyc, c1) in zip(flat, flat[1:]):
            assert (c1 - c0) % NUM_HARTS == (c1_cyc - c0_cyc) % NUM_HARTS, \
                f"rotation broken: ctx {c0} at cycle {c0_cyc}, ctx {c1} at {c1_cyc}"
