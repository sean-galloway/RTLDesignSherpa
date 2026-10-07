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

Task 8 (system layer) extends the contract:

* The halting instruction now retires as an RVFI **trap beat**
  (``rvfi_valid=1``, ``rvfi_trap=1``) on the halt cycle; the core then
  freezes with ``rvfi_valid=0`` forever.  ``run()`` samples that final
  beat before breaking, so recorded traces include it and the golden
  interpreter appends the matching beat.
* Reset/clock are factored so the rv32ui battery can run many programs
  through one Verilator build: ``assert_reset`` + ``backdoor_load`` +
  ``release_reset`` + ``run_to_halt`` per image.
* ``run_to_halt`` can watch the data-memory store port for a write to the
  riscv-tests ``tohost`` word (the battery pass/fail mailbox).
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

# gp is TESTNUM in the riscv-tests p-env: the pass/fail code at the ecall.
GP_RD_ADDR = 3


class KestrelTB:
    """Drive kestrel_tb_top and capture the core's RVFI retire trace."""

    def __init__(self, dut, reset_addr=0):
        self.dut = dut
        self.reset_addr = reset_addr
        self.trace = []
        self.halt_cause = None
        self.halt_pc = None
        self.tohost_writes = []
        self._clock_started = False
        # The Task-8 TB top has a backdoor image-load port; park it idle.
        if hasattr(dut, "tb_mem_we"):
            dut.tb_mem_we.value = 0

    # ------------------------------------------------------------------
    # Clock / reset / image loading
    # ------------------------------------------------------------------

    async def ensure_clock(self):
        """Start the 100 MHz clock once (battery reuses it across tests)."""
        if not self._clock_started:
            clock = Clock(self.dut.clk, 10, units="ns")
            cocotb.start_soon(clock.start())
            self._clock_started = True

    async def assert_reset(self):
        """Drive rst_n low for four cycles (async assert, sync deassert)."""
        self.dut.rst_n.value = 0
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def release_reset(self):
        """Release right after a posedge: the following full cycle is the
        first post-reset cycle, so the RESET_ADDR fetch is the first beat
        sampled by ``run_to_halt``."""
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1

    async def backdoor_load(self, words):
        """Write a {word_index: word} image through the TB top's backdoor
        port, one word per cycle, while the core is held in reset."""
        dut = self.dut
        for idx, word in sorted(words.items()):
            await FallingEdge(dut.clk)
            dut.tb_mem_we.value = 1
            dut.tb_mem_addr.value = (idx << 2) & 0xFFFF_FFFC
            dut.tb_mem_wdata.value = word
        await FallingEdge(dut.clk)
        dut.tb_mem_we.value = 0

    async def run(self, max_cycles=20_000, post_halt_cycles=4):
        """Reset the core, run to halt (or timeout), record every RVFI beat.

        This is the original single-program contract used by the +imem
        directed tests: start clock, reset, release, run to halt.
        """
        await self.ensure_clock()
        await self.assert_reset()
        await self.release_reset()
        await self.run_to_halt(max_cycles, post_halt_cycles)

    # ------------------------------------------------------------------
    # Trace capture
    # ------------------------------------------------------------------

    async def run_to_halt(self, max_cycles=20_000, post_halt_cycles=4,
                          watch_tohost=None):
        """Run to halt (or timeout), recording every RVFI beat.

        After halt, sample a few more cycles to pin the halt-hold behavior:
        halt stays raised, no further RVFI beat retires, and the PC freezes.
        ``watch_tohost`` is the byte address of the riscv-tests tohost
        mailbox; every committed store to that word is recorded in
        ``self.tohost_writes`` as the byte-masked store data.
        """
        dut = self.dut
        self.trace = []
        self.halt_cause = None
        self.halt_pc = None
        self.tohost_writes = []
        tohost_mask = 0x0003_FFFF  # tb_top memory is 64 Ki words, word-indexed

        for _ in range(max_cycles):
            await FallingEdge(dut.clk)
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
                # Task 8: the halting instruction retires as a trap beat
                # (rvfi_valid=1, rvfi_trap=1) on this cycle; sample it.
                if int(dut.rvfi_valid.value):
                    self.trace.append(self._sample_beat())
                break
            # Cross-word L/S retires over two cycles: rvfi_valid is low on the
            # first (retry) beat and high only on the final beat.  Skip the
            # retry cycles; the trace-length diff catches missing retire beats.
            if int(dut.rvfi_valid.value) == 0:
                continue
            self.trace.append(self._sample_beat())
        else:
            last_pc = self.trace[-1]["pc"] if self.trace else 0
            raise AssertionError(
                f"no halt after {max_cycles} cycles (last pc=0x{last_pc:x})")

        for _ in range(post_halt_cycles):
            await FallingEdge(dut.clk)
            assert int(dut.halt.value) == 1, "halt deasserted after halt"
            assert int(dut.rvfi_valid.value) == 0, \
                "rvfi_valid high during halt"
            assert int(dut.rvfi_pc_rdata.value) == self.halt_pc, \
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

    # ------------------------------------------------------------------
    # Checks
    # ------------------------------------------------------------------

    def gp_at_halt(self):
        """riscv-tests p-env pass/fail code: TESTNUM (gp, x3) at the halt.

        The core halts on the ecall before the trap vector can store gp to
        tohost, so gp's last writeback value is the tohost-equivalent
        verdict (1 = pass, odd >1 = fail code).
        """
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
        """The final recorded beat must be the Task-8 rvfi_trap beat."""
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
