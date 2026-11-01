# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: merlin_tb
# Purpose: cocotb TB class for the merlin_core golden-trace lockstep test.
#          Drives clk/reset/mem_wait, records every RVFI beat at WB retire,
#          runs to halt, and diffs the recorded trace against the golden
#          interpreter imported from the kestrel testbench library.
#
# Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
# Subsystem: riscv-ip/merlin-rv32i
#
# Author: sean galloway
# Created: 2026-11-01

"""cocotb TB class for merlin_core running on merlin_tb_top.

The golden RV32IInterpreter is reused from the kestrel-rv32i testbench
library; merlin implements the same ISA and halt contract, so the model
is identical.  RVFI beats are sampled on the falling edge while
rvfi_valid is high; the pipelined core retires at most one instruction
per cycle at WB.
"""

import importlib.util
import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge

# Load the kestrel golden model directly from its source file to avoid the
# tbclasses namespace collision between merlin-rv32i and kestrel-rv32i.
_KESTREL_INTERPRETER = (
    Path(__file__).resolve().parents[3]   # merlin-rv32i
    .parent / "kestrel-rv32i" / "dv" / "tbclasses" / "kestrel" / "rv32i_interpreter.py"
).resolve()

_spec = importlib.util.spec_from_file_location(
    "kestrel_rv32i_interpreter", str(_KESTREL_INTERPRETER))
_kestrel_interp = importlib.util.module_from_spec(_spec)
sys.modules["kestrel_rv32i_interpreter"] = _kestrel_interp
_spec.loader.exec_module(_kestrel_interp)

RV32IInterpreter = _kestrel_interp.RV32IInterpreter
load_verilog_hex = _kestrel_interp.load_verilog_hex

# RVFI trace field set, kept identical to the kestrel TB contract.
TRACE_FIELDS = (
    "order", "pc", "insn", "trap",
    "rs1_addr", "rs2_addr", "rs1_rdata", "rs2_rdata",
    "rd_addr", "rd_wdata", "pc_wdata",
    "mem_addr", "mem_rmask", "mem_wmask", "mem_rdata", "mem_wdata",
)

# gp is TESTNUM in the riscv-tests p-env.
GP_RD_ADDR = 3


class MerlinTB:
    """Drive merlin_tb_top and capture the core's RVFI retire trace."""

    def __init__(self, dut, reset_addr=0):
        self.dut = dut
        self.reset_addr = reset_addr
        self.trace = []
        self.halt_cause = None
        self.halt_pc = None
        self.tohost_writes = []
        self._clock_started = False
        # Park the backdoor loader and the mem_wait seam idle.
        if hasattr(dut, "tb_mem_we"):
            dut.tb_mem_we.value = 0
        if hasattr(dut, "mem_wait"):
            dut.mem_wait.value = 0

    # ------------------------------------------------------------------
    # Clock / reset / image loading
    # ------------------------------------------------------------------

    async def ensure_clock(self):
        """Start the 100 MHz clock once."""
        if not self._clock_started:
            clock = Clock(self.dut.clk, 10, units="ns")
            cocotb.start_soon(clock.start())
            self._clock_started = True

    async def assert_reset(self):
        """Drive rst_n low for four cycles."""
        self.dut.rst_n.value = 0
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def release_reset(self):
        """Release reset right after a posedge."""
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1

    async def backdoor_load(self, words):
        """Write a {word_index: word} image through the TB backdoor port."""
        dut = self.dut
        for idx, word in sorted(words.items()):
            await FallingEdge(dut.clk)
            dut.tb_mem_we.value = 1
            dut.tb_mem_addr.value = (idx << 2) & 0xFFFF_FFFC
            dut.tb_mem_wdata.value = word
        await FallingEdge(dut.clk)
        dut.tb_mem_we.value = 0

    async def run(self, max_cycles=40_000, post_halt_cycles=4,
                  watch_tohost=None, pulse_mem_wait=None):
        """Reset the core, run to halt, and record every RVFI beat."""
        await self.ensure_clock()
        await self.assert_reset()
        await self.release_reset()
        await self.run_to_halt(max_cycles, post_halt_cycles,
                               watch_tohost=watch_tohost,
                               pulse_mem_wait=pulse_mem_wait)

    # ------------------------------------------------------------------
    # Trace capture
    # ------------------------------------------------------------------

    async def run_to_halt(self, max_cycles=40_000, post_halt_cycles=4,
                          watch_tohost=None, pulse_mem_wait=None):
        """Run to halt, recording every RVFI beat.

        ``watch_tohost`` is the byte address of the riscv-tests tohost
        mailbox; every committed store to that word is recorded in
        ``self.tohost_writes``.

        ``pulse_mem_wait`` is an optional callable ``f(dut, cycle) -> bool``.
        When it returns True the model asserts mem_wait for that falling-edge
        sample.  Used by the mem_wait-pulse test to hold the pipeline mid-load.
        """
        dut = self.dut
        self.trace = []
        self.halt_cause = None
        self.halt_pc = None
        self.tohost_writes = []
        tohost_mask = 0x0003_FFFF

        for cycle in range(max_cycles):
            await FallingEdge(dut.clk)

            if pulse_mem_wait is not None and pulse_mem_wait(dut, cycle):
                dut.mem_wait.value = 1
            else:
                dut.mem_wait.value = 0

            if watch_tohost is not None and int(dut.dmem_req.value) and \
                    int(dut.dmem_wstrb.value) != 0:
                if (int(dut.dmem_addr.value) & tohost_mask) == \
                        (watch_tohost & tohost_mask):
                    strobe = int(dut.dmem_wstrb.value)
                    data = int(dut.dmem_wdata.value)
                    value = 0
                    for b in range(4):
                        if (strobe >> b) & 1:
                            value |= ((data >> (8 * b)) & 0xFF) << (8 * b)
                    self.tohost_writes.append(value)

            if int(dut.halt.value):
                self.halt_cause = int(dut.halt_cause.value)
                self.halt_pc = int(dut.rvfi_pc_rdata.value)
                if int(dut.rvfi_valid.value):
                    self.trace.append(self._sample_beat())
                break

            dut._log.info(
                f"cycle {cycle}: rvfi_valid={int(dut.rvfi_valid.value)} "
                f"halt={int(dut.halt.value)} mem_wait={int(dut.mem_wait.value)} "
                f"imem_addr=0x{int(dut.imem_addr.value):x}")
            if int(dut.rvfi_valid.value) == 0:
                continue
            beat = self._sample_beat()
            dut._log.info(
                f"RVFI beat {len(self.trace)}: pc=0x{beat['pc']:x} "
                f"insn=0x{beat['insn']:08x} rd={beat['rd_addr']} "
                f"rd_wdata=0x{beat['rd_wdata']:x} pc_wdata=0x{beat['pc_wdata']:x}")
            self.trace.append(beat)
        else:
            last_pc = self.trace[-1]["pc"] if self.trace else 0
            raise AssertionError(
                f"no halt after {max_cycles} cycles (last pc=0x{last_pc:x})")

        post_halt_imem_addr = int(dut.imem_addr.value)
        for _ in range(post_halt_cycles):
            await FallingEdge(dut.clk)
            dut.mem_wait.value = 0
            assert int(dut.halt.value) == 1, "halt deasserted after halt"
            assert int(dut.rvfi_valid.value) == 0, \
                "rvfi_valid high during halt"
            assert int(dut.imem_addr.value) == post_halt_imem_addr, \
                "imem_addr moved during halt (fetch must be frozen)"  

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
    # Checks
    # ------------------------------------------------------------------

    def gp_at_halt(self):
        """riscv-tests p-env pass/fail code: TESTNUM (gp, x3) at halt."""
        for beat in reversed(self.trace):
            if beat["rd_addr"] == GP_RD_ADDR:
                return beat["rd_wdata"]
        return 0

    def check_halt(self, expected_cause, expected_halt_pc=None):
        assert self.halt_cause is not None, "never reached halt"
        assert self.halt_cause == expected_cause, \
            f"halt_cause: core={self.halt_cause:#x} expected={expected_cause:#x}"
        if expected_halt_pc is not None:
            assert self.halt_pc == expected_halt_pc, \
                f"halt pc: core=0x{self.halt_pc:x} golden=0x{expected_halt_pc:x}"

    def check_trap_beat(self):
        """The final recorded beat must be the rvfi_trap beat."""
        assert self.trace, "no RVFI beats recorded"
        last = self.trace[-1]
        assert last["trap"] == 1, \
            f"final beat is not a trap beat (trap={last['trap']}, " \
            f"pc=0x{last['pc']:x} insn=0x{last['insn']:08x})"
        assert last["pc"] == self.halt_pc, \
            "trap beat pc does not match the halt pc"
        assert last["rd_addr"] == 0 and last["rd_wdata"] == 0, \
            "trap beat must not report a register write"
        assert last["mem_rmask"] == 0 and last["mem_wmask"] == 0, \
            "trap beat must not report a memory access"

    def check_first_pc(self):
        assert self.trace, "no RVFI beats recorded"
        assert self.trace[0]["pc"] == self.reset_addr, \
            f"first pc: core=0x{self.trace[0]['pc']:x} " \
            f"expected RESET_ADDR=0x{self.reset_addr:x}"

    def check_order_sequence(self):
        for i, beat in enumerate(self.trace):
            assert beat["order"] == i, \
                f"beat {i}: rvfi_order={beat['order']} expected {i}"

    def check_pc_sequential(self):
        """For straight-line programs every retired insn advances pc by 4."""
        for i, beat in enumerate(self.trace):
            assert beat["pc_wdata"] == (beat["pc"] + 4) & 0xFFFFFFFF, \
                f"beat {i}: pc_wdata=0x{beat['pc_wdata']:x} " \
                f"expected pc+4=0x{(beat['pc'] + 4) & 0xFFFFFFFF:x}"

    def check_x0_rd_zero(self):
        """riscv-formal rule: rd_wdata must be zero whenever rd_addr is zero."""
        for i, beat in enumerate(self.trace):
            if beat["rd_addr"] == 0:
                assert beat["rd_wdata"] == 0, (
                    f"beat {i}: rd_addr=0 but rd_wdata=0x{beat['rd_wdata']:x} "
                    f"(pc=0x{beat['pc']:x} insn=0x{beat['insn']:08x})")

    def check_trace(self, golden_trace):
        """Instruction-by-instruction diff against the golden interpreter."""
        assert len(self.trace) == len(golden_trace), \
            f"trace length: core={len(self.trace)} golden={len(golden_trace)}"
        for i, (got, want) in enumerate(zip(self.trace, golden_trace)):
            for field in TRACE_FIELDS:
                if want[field] is None:
                    continue
                assert got[field] == want[field], (
                    f"beat {i} field {field}: core=0x{got[field]:x} "
                    f"golden=0x{want[field]:x} "
                    f"(pc=0x{want['pc']:x} insn=0x{want['insn']:08x})")
