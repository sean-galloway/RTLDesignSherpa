# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: kestrel_tb
# Purpose: cocotb TB class for the kestrel_core golden-trace lockstep test:
#          drives clk/reset, records every RVFI beat, runs to halt, and
#          diffs the recorded trace against the golden interpreter's trace.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

"""cocotb TB class for kestrel_core running on kestrel_tb_top.

Sampling model: the core is single-cycle, so a falling-edge sample sees a
fully settled cycle (no register updates on negedge). Reset is released
right after a posedge, which makes the following full cycle — the
RESET_ADDR instruction — the first one sampled. One RVFI beat is recorded
per cycle while ``rvfi_valid`` is high; the cycle decode raises ``halt``
is never recorded, matching the golden interpreter (which records no beat
for the halting instruction).
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge

TRACE_FIELDS = (
    "order", "pc", "insn", "trap",
    "rs1_addr", "rs2_addr", "rs1_rdata", "rs2_rdata",
    "rd_addr", "rd_wdata", "pc_wdata",
    "mem_addr", "mem_rmask", "mem_wmask", "mem_rdata", "mem_wdata",
)


class KestrelTB:
    """Drive kestrel_tb_top and capture the core's RVFI retire trace."""

    def __init__(self, dut, reset_addr=0):
        self.dut = dut
        self.reset_addr = reset_addr
        self.trace = []
        self.halt_cause = None
        self.halt_pc = None

    async def run(self, max_cycles=20_000, post_halt_cycles=4):
        """Reset the core, run to halt (or timeout), record every RVFI beat.

        After halt, sample a few more cycles to pin the halt-hold behavior:
        halt stays raised, no further RVFI beat retires, and the PC freezes.
        """
        clock = Clock(self.dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        self.dut.rst_n.value = 0
        for _ in range(4):
            await RisingEdge(self.dut.clk)
        # Release right after a posedge: the following full cycle is the
        # first post-reset cycle, so the RESET_ADDR fetch is the first
        # beat sampled below.
        self.dut.rst_n.value = 1

        for _ in range(max_cycles):
            await FallingEdge(self.dut.clk)
            if int(self.dut.halt.value):
                self.halt_cause = int(self.dut.halt_cause.value)
                self.halt_pc = int(self.dut.rvfi_pc_rdata.value)
                break
            # Cross-word L/S retires over two cycles: rvfi_valid is low on the
            # first (retry) beat and high only on the final beat.  Skip the
            # retry cycles; the trace-length diff catches missing retire beats.
            if int(self.dut.rvfi_valid.value) == 0:
                continue
            self.trace.append(self._sample_beat())
        else:
            last_pc = self.trace[-1]["pc"] if self.trace else 0
            raise AssertionError(
                f"no halt after {max_cycles} cycles (last pc=0x{last_pc:x})")

        for _ in range(post_halt_cycles):
            await FallingEdge(self.dut.clk)
            assert int(self.dut.halt.value) == 1, "halt deasserted after halt"
            assert int(self.dut.rvfi_valid.value) == 0, \
                "rvfi_valid high during halt"
            assert int(self.dut.rvfi_pc_rdata.value) == self.halt_pc, \
                "pc moved during halt (halt must hold the fetch address)"

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

    def check_halt(self, expected_cause, expected_halt_pc=None):
        assert self.halt_cause is not None, "never reached halt"
        assert self.halt_cause == expected_cause, \
            f"halt_cause: core={self.halt_cause:#x} expected={expected_cause:#x}"
        if expected_halt_pc is not None:
            assert self.halt_pc == expected_halt_pc, \
                f"halt pc: core=0x{self.halt_pc:x} golden=0x{expected_halt_pc:x}"

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
        """Task-5 programs have no B/J: every retired insn advances pc by 4."""
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
                assert got[field] == want[field], (
                    f"beat {i} field {field}: core=0x{got[field]:x} "
                    f"golden=0x{want[field]:x} "
                    f"(pc=0x{want['pc']:x} insn=0x{want['insn']:08x})")
