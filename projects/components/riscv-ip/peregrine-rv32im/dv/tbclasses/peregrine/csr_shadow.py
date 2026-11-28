# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: csr_shadow
# Purpose: The shadow trap-CSR model for peregrine's RVFI trace (riscv-ip/
#          peregrine-rv32im TASK-005): mepc, mcause and mtval predicted from
#          the retire stream, and every CSR instruction's read of them held
#          to the prediction.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-27

"""Shadow model of peregrine's trap CSRs, checked from RVFI.

peregrine's RVFI has no ``rvfi_csr_*`` (PRD §4.7), so the trap CSRs are
checked the other way round: the model applies every trap beat (mepc = its
PC, mcause = ``rvfi_trap_cause``, mtval = what the privileged spec requires
for that cause) and every CSR instruction's write, and each CSR
instruction that reads mepc, mcause or mtval must return the modelled
value in ``rvfi_rd_wdata``.  A handler's ``csrr a0, mcause`` is then a
check of the trap the core took, not only of what the program compares.

mtval is predicted for the causes whose value is fixed by the trap:
instruction access fault (the fetch PC), load / store access fault (the
access's byte address, rs1 + imm from RVFI) and interrupts (0).  Any other
exception leaves mtval unknown until the program writes it, and a read of
an unknown value is not checked (counted, so a test can require reads).
"""

from typing import Optional

from tbclasses.peregrine.battery import expected_tval

CSR_MEPC = 0x341
CSR_MCAUSE = 0x342
CSR_MTVAL = 0x343
TRAP_CSRS = (CSR_MEPC, CSR_MCAUSE, CSR_MTVAL)

_OPC_SYSTEM = 0x73


def _csr_fields(insn: int) -> Optional[tuple]:
    """(csr, funct3, rs1/zimm field, rd) of a Zicsr instruction, else None."""
    f3 = (insn >> 12) & 0x7
    if (insn & 0x7F) != _OPC_SYSTEM or (f3 & 0x3) == 0:
        return None
    return insn >> 20, f3, (insn >> 15) & 0x1F, (insn >> 7) & 0x1F


class TrapCsrShadow:
    """Run over a trace; ``check`` raises AssertionError on a mismatch."""

    def __init__(self) -> None:
        self.csr = {CSR_MEPC: 0, CSR_MCAUSE: 0, CSR_MTVAL: 0}   # reset values
        self.reads_checked = {c: 0 for c in TRAP_CSRS}
        self.reads_unknown = 0
        self.traps = 0

    def _trap(self, beat: dict) -> None:
        self.traps += 1
        cause = beat["trap_cause"]
        self.csr[CSR_MEPC] = beat["pc"] & ~0x3
        self.csr[CSR_MCAUSE] = cause
        if cause >> 31:
            self.csr[CSR_MTVAL] = 0
        else:
            self.csr[CSR_MTVAL] = expected_tval(beat)     # None: not modelled

    def _csr_insn(self, i: int, beat: dict, fields: tuple) -> None:
        csr, f3, src, rd = fields
        if csr not in TRAP_CSRS:
            return
        old = self.csr[csr]
        if rd != 0:
            if old is None:
                self.reads_unknown += 1
            else:
                assert beat["rd_wdata"] == old, (
                    f"beat {i} pc=0x{beat['pc']:x}: CSR 0x{csr:03x} read "
                    f"0x{beat['rd_wdata']:08x}, the shadow model holds 0x{old:08x}")
                self.reads_checked[csr] += 1
        value = src if f3 & 0x4 else beat["rs1_rdata"]
        op = f3 & 0x3
        if op == 1:                                       # csrrw(i)
            new = value
        elif src == 0:                                    # csrrs/c with x0: no write
            return
        elif old is None:
            new = None
        elif op == 2:
            new = old | value
        else:
            new = old & ~value
        if new is not None and csr == CSR_MEPC:
            new &= ~0x3                                    # IALIGN = 32
        self.csr[csr] = None if new is None else new & 0xFFFF_FFFF

    def check(self, trace: list) -> dict:
        for i, beat in enumerate(trace):
            if beat["trap"]:
                self._trap(beat)
                continue
            fields = _csr_fields(beat["insn"])
            if fields is not None:
                self._csr_insn(i, beat, fields)
        return {"traps": self.traps,
                "mepc_reads": self.reads_checked[CSR_MEPC],
                "mcause_reads": self.reads_checked[CSR_MCAUSE],
                "mtval_reads": self.reads_checked[CSR_MTVAL],
                "unknown_reads": self.reads_unknown}
