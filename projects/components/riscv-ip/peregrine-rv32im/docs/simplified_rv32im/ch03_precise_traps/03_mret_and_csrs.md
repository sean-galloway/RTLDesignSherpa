# mret and the CSRs

## The CSR set

peregrine implements the machine-mode CSRs a trap needs and little else
(PRD P6): `mstatus` (MIE, MPIE; MPP fixed at M), `mie`, `mip`, `mtvec`
(direct mode only), `mepc`, `mcause`, `mscratch`, `mtval`, the read-only
identity CSRs (`misa`, `mhartid` = 0, and the vendor, architecture and
implementation IDs), and zero-entry PMP CSRs that read 0 and ignore
writes. There are no counters (no Zicntr); cycle counts come from the
test bench.

## Read in EX, write in MEM

A CSR instruction reads the CSR file in EX and writes it in MEM, at the
commit point. A CSR write therefore never lands under an older trap: if
an older instruction traps, the CSR instruction is flushed before MEM.

There is no CSR forwarding. Instead, a CSR instruction waits in ID while
an older CSR instruction is still in ID/EX or EX/MEM: up to 2 cycles.
Only CSR instructions read CSRs, so no other hazard exists.

| Mechanism | Cost | Why |
|-----------|------|-----|
| CSR serialization interlock | Up to 2 cycles, only for back-to-back CSR instructions | Simpler than forwarding every CSR, and CSR instructions are rare |
| Write at MEM | 0 | The commit point; precise for free |

: CSR read-after-write (PRD P6)

## mret

`mret` is decoded in ID and acts in MEM, like a trap in reverse: the PC
goes to `mepc`, `mstatus.MIE` is restored from `MPIE`, and the three
younger instructions are flushed: 3 bubbles. Because `mret` and a trap
both redirect from MEM and both write `mstatus`, MEM commits at most one
of them per cycle.

## Why the PRD said "ID"

The PRD first placed the CSR read in ID. The RTL reads in EX, and the PRD
was amended to match (2026-11-25). Reading in EX means the old value
travels with the instruction to WB, where it is written to `rd`, and the
serialization interlock in ID is the whole hazard story.
