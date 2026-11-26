# Conventions

## Notation

- Stages are IF, ID, EX, MEM and WB. "Leaves EX" means the clock edge at
  which an instruction moves from ID/EX to EX/MEM.
- Cycle labels in the waveforms are relative: `n`, `n+1`, ... A stage
  holding a bubble shows `-`.
- A *bubble* is a lost retire slot, measured at WB.
- `mem_wait` is the global hold: while it is high nothing moves and
  nothing commits.
- Signal names are the RTL's (`ex_mispredict`, `mem_trap`,
  `ex_m_stall`), so the MAS and the source can be searched for them.

## Machine mode, not supervisor mode (COD gap G8)

COD's exception example (§4.10) uses supervisor-mode names: SEPC for the
exception PC and SCAUSE for the cause. peregrine implements machine mode
only, as the RISC-V privileged specification defines it, so the same
registers are `mepc` and `mcause`, the vector is `mtvec`, and the return
is `mret`. The mechanism is COD's: stop the offending instruction, save
its PC and the cause, and branch to a prearranged address. Only the names
and the privilege level differ. COD does not document the privileged CSR
map; the privileged specification is the authority for it.

| COD §4.10 | peregrine | Meaning |
|-----------|-----------|---------|
| SEPC | `mepc` | PC of the instruction that trapped or was interrupted |
| SCAUSE | `mcause` | The cause code (bit 31 set for an interrupt) |
| (fixed entry point) | `mtvec` | The handler address, direct mode only |
| `sret` | `mret` | Return to `mepc`, restore the interrupt enable |

: COD's supervisor names and peregrine's machine-mode names

## Citations

The PRD is cited by section (§4.3) or decision row (P13). The
implementation record is cited as TASK-001 with its stage number. The
MAS is cited by chapter title.
