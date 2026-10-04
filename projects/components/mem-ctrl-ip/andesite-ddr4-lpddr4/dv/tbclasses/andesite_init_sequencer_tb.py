# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Testbench + order checker for `andesite_init_sequencer`.

The checker is the HAS ch06 item-1 instrument: it records every issued init
command and, on init_done, asserts the MAS-anchor order (RESET# window, CKE
discipline, MR3->MR6->MR5->MR4->MR2->MR1->MR0, ZQCL close, tDLLK+tZQinit).
It is a pure Python function so the negative case (fabricated wrong-order
events must raise) runs without a simulation.
"""

import subprocess
import sys

from cocotb.triggers import RisingEdge

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = _repo_root + "/bin"
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

# dram_op_e
OP_MRS = 0x0A
OP_ZQCL = 0x0C

# MAS ch02 02_init_sequencer.md DDR4 FSM fence: the MR order is a citation.
MR_ORDER = [3, 6, 5, 4, 2, 1, 0]


class SeqError(AssertionError):
    pass


def check_init_order(events, cke_cycle, reset_release_cycle, csrs, done_cycle):
    """events: list of (cycle, op, bank, addr) at cmd_req&cmd_ack.

    csrs: dict with tinit1/3/4, tmrd, tmod, tdllk, tzqinit. Raises SeqError
    on any deviation from the anchored order.
    """
    mrs = [e for e in events if e[1] == OP_MRS]
    others = [e for e in events if e[1] != OP_MRS]
    if [e[2] for e in mrs] != MR_ORDER:
        raise SeqError(f"MRS order {[e[2] for e in mrs]} != anchor {MR_ORDER}")
    if [e[1] for e in others] != [OP_ZQCL]:
        raise SeqError(f"post-MRS commands {[e[1] for e in others]} != [ZQCL]")
    if others[0][0] <= mrs[-1][0]:
        raise SeqError("ZQCL must follow the last MRS")
    if cke_cycle is None or cke_cycle < reset_release_cycle + csrs['tinit3']:
        raise SeqError("CKE raised before tINIT3 elapsed after RESET# release")
    if reset_release_cycle < csrs['tinit1']:
        raise SeqError("RESET# released before tINIT1 elapsed")
    if mrs[0][0] < cke_cycle + csrs['tinit4']:
        raise SeqError("first MRS before tINIT4 elapsed after CKE")
    for a, b in zip(mrs, mrs[1:]):
        if b[0] - a[0] < csrs['tmrd']:
            raise SeqError(f"tMRD gap violated between MR{a[2]} and MR{b[2]}")
    if others[0][0] - mrs[-1][0] < csrs['tmod']:
        raise SeqError("tMOD gap violated before ZQCL")
    if done_cycle - others[0][0] < max(csrs['tdllk'], csrs['tzqinit']):
        raise SeqError("init_done before tDLLK/tZQinit expired from ZQCL")


class AndesiteInitSequencerTB:
    def __init__(self, dut):
        self.dut = dut
        self.events = []
        self.parity_at_events = []
        self.cke_cycle = None
        self.reset_release_cycle = None
        self._cycle = 0

    async def setup_clock(self, period_ns=10):
        import cocotb
        from cocotb.clock import Clock
        self._clk = Clock(self.dut.clk, period_ns, units="ns")
        await cocotb.start(self._clk.start())

    async def reset(self, csrs):
        d = self.dut
        d.reset_n.value = 0
        d.csr_init_trigger.value = 0
        d.csr_memtype.value = 0x2          # MEMTYPE_DDR4
        d.csr_geardown_en.value = 0
        d.csr_parity_en.value = 0
        for name, val in csrs.items():
            getattr(d, f"{name}_csr").value = val
        for m in range(7):
            getattr(d, f"csr_mr{m}_image").value = 0x10 + m
        for _ in range(3):
            await RisingEdge(d.clk)
        d.reset_n.value = 1

    async def run(self, stall_at=None, max_cycles=2000):
        """Run until init_done (return done cycle) or max_cycles (return None).
        stall_at: cycle index at which cmd_ack is held low for one cycle."""
        d = self.dut
        d.cmd_ack.value = 1
        self._cycle = 0
        while self._cycle < max_cycles:
            if stall_at is not None and self._cycle == stall_at:
                d.cmd_ack.value = 0
            elif stall_at is not None and self._cycle == stall_at + 1:
                d.cmd_ack.value = 1
            await RisingEdge(d.clk)
            self._cycle += 1
            if int(d.reset_n_out.value) == 1 and self.reset_release_cycle is None:
                self.reset_release_cycle = self._cycle
            if int(d.cke_out.value) == 1 and self.cke_cycle is None:
                self.cke_cycle = self._cycle
            if int(d.cmd_req.value) == 1 and int(d.cmd_ack.value) == 1:
                self.events.append((self._cycle, int(d.cmd_op.value),
                                    int(d.cmd_bank.value), int(d.cmd_addr.value)))
                self.parity_at_events.append(int(d.parity_enable_out.value))
            if int(d.init_done.value) == 1:
                return self._cycle
        return None
