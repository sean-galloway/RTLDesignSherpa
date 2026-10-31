# MERLIN PRD — 5-Stage Pipelined RV32I

**Version:** 0.1 (2026-10-30 — initial scaffold from the approved
falcon-suite design spec, rung 2)
**Date:** 2026-10-30
**Design source:** [riscv-falcon-suite design spec](../../../../docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md),
rung 2. Where this PRD narrows a choice the spec left open, the row says
so and waits for the owner's name and date.

---

## 1. Purpose

The working falcon: the rung where hazards appear and we learn to live
with them. Merlin is **kestrel's ISA, pipelined** — the same RV32I, the
same halt contract, the same rv32ui battery and spike lockstep — so the
student diffs *behavior*, not ISA, when moving up the ladder. The lesson
is the pipeline itself: pipeline registers, RAW hazards, operand
forwarding, the load-use bubble, and control-hazard flushes.

Merlin is also the structural foundation everything above it inherits:
peregrine's spec is "merlin's pipeline extended" (predictor, traps, M
unit), so merlin's stage boundaries, hazard unit, and RVFI retire point
are chosen to survive that extension.

## 2. Non-goals

- **No branch prediction** — predict-not-taken only; the predictor study
  is peregrine's (rung 3).
- **No traps/exceptions subsystem** — kestrel's halt contract carries
  unchanged (ecall/ebreak/illegal/misaligned halt with cause). Machine
  CSRs are peregrine's.
- **No M/A/F extensions, no caches, no MMU** — flat Harvard memory;
  the cache slot is peregrine's (amber, per the cache-ip client ruling
  of 2026-10-30).
- **No superscalar, no OoO** — single-issue, in-order. That is
  gyrfalcon's lesson, two rungs up.
- **No Zicntr** — gatling's removal precedent (2026-10-21) applies:
  no counter CSRs.

## 3. ISA — RV32I, identical to kestrel

Same opcode map, same encodings, same decode tables. Reuses the
`common-rv32i` fubs unchanged: `rv32i_decode`, `rv32i_imm_gen`,
`rv32i_alu`, `rv32i_pkg`. The CSR stub carries over (every CSR reads 0,
writes drop) so the rv32ui p-env preamble runs.

Halt contract carried from kestrel: `halt` + `halt_cause[3:0]` —
ecall, ebreak, illegal instruction, instruction-address-misaligned,
load/store-misaligned. The halting instruction is the last to retire
(RVFI-visible).

## 4. Microarchitecture

### 4.1 The pipeline

Classic 5-stage RISC, single issue, in order:

```
  IF : imem_addr = PC; registered-read instruction memory
  ID : decode (rv32i_decode), regfile read (rs1/rs2), imm_gen
  EX : ALU (rv32i_alu); branch decision + target; forwarding muxes
  MEM: data memory access (registered-read BRAM, byte-strobe write)
  WB : regfile write (rd)
```

Pipeline registers between every stage: `if_id`, `id_ex`, `ex_mem`,
`mem_wb`. Each carries the PC, the instruction word (debug + RVFI), and
its stage's control bundle — the book's "the pipeline register is the
contract between stages" lesson made literal.

### 4.2 Hazards and forwarding (the rung's reason to exist)

- **EX/MEM → EX and MEM/WB → EX forwarding**, explicit priority
  (EX/MEM wins — it is the newer value), on both ALU operands.
- **Load-use interlock**: a load in EX whose rd matches either ID source
  stalls IF/ID one cycle and injects a bubble into EX — the one bubble
  the student must be able to point at on a waveform.
- **Control hazard**: branches and JALR resolve in EX;
  predict-not-taken; a taken branch flushes IF/ID and ID/EX (2 bubbles).
  JAL/JALR link (PC+4) forwards through the same path as ALU results.
- **Write-read regfile timing**: WB writes on the leading edge, ID reads
  combinationally — the classic "write first half, read second half"
  split, documented in the HAS with its timing diagram.

### 4.3 Memory contract

Harvard at the core ports (`imem_*`, `dmem_*`), unified von Neumann in
the TB wrapper — kestrel's arrangement, so self-modifying-code and
`fence.i` tests behave identically across rungs. Memories are
registered-read block RAM, no wait states in v1. A `mem_wait` hold input
(all stages stall, kestrel semantics) is carried as the documented seam
peregrine's cache slot will drive.

### 4.4 RVFI / retire

RVFI valid at WB, in order, one per cycle maximum. `rvfi_order` counts
retired instructions. The pipelined-machine adaptation of kestrel's
riscv-formal checks binds at this interface (see §5).

## 5. Verification

- **riscv-formal**, pipelined adaptation: the retire-interface checks
  (PC transition, rd writeback, memory side effects) run against WB,
  not against a single-cycle whole-machine model. The insn_* checks
  from kestrel carry where they still apply at retire.
- **rv32ui battery** (42/42 precedent), same images as kestrel, via the
  TB backdoor loader pattern (kestrel Task 8).
- **Directed hazard suite** — the rung's signature DV:
  forwarding matrix (every producer stage × consumer operand),
  load-use matrix (load → dependent at every distance 0/1/2),
  branch flush cases (taken/back-to-back/flush-vs-forward collision).
- **Spike lockstep** in the rds-dv cocotb flow, as kestrel/gatling.
- **Waves**: house GTKW save file at `dv/tests/GTKW/` from day one
  (kestrel/gatling precedent, 2026-10-30) — the load-use bubble and the
  2-bubble branch flush are the two waveforms the book needs.

## 6. Decision rows

| # | Decision | Status | What it drives |
|---|---|---|---|
| M1 | Pipeline shape | **DECIDED (falcon-suite spec, rung 2):** IF/ID/EX/MEM/WB, single issue, in order | everything |
| M2 | Branch resolution | **DECIDED (spec):** EX, predict-not-taken, flush on taken (2 bubbles) | control hazard logic, IPC lesson |
| M3 | Forwarding | **DECIDED (spec):** EX/MEM→EX and MEM/WB→EX, EX/MEM priority, both operands | forwarding unit |
| M4 | Load-use | **DECIDED (spec):** 1-cycle interlock stall | hazard unit |
| M5 | Memory contract | **PROPOSED (default chosen, needs owner):** Harvard core ports, unified TB wrapper, registered-read BRAM, `mem_wait` seam carried for peregrine | tb_top, peregrine transition |
| M6 | Halt/CSR contract | **PROPOSED (default: carry kestrel unchanged):** halt+causes, CSR stub, no Zicntr | decode, rv32ui compat |
| M7 | Regfile write/read split | **PROPOSED (default: WB leading-edge write, ID combinational read)** — the alternative (ID reads via WB forward) costs a mux and hides the classic lesson | regfile, timing |

## 7. Deliverables & sequencing

1. This PRD (owner review).
2. `merlin_has` + `merlin_mas` book skeletons (hazard/forwarding
   chapters are the heart; GTKW waveforms embedded per §5).
3. RTL: `merlin_core` (pipeline registers, hazard/forward unit,
   branch/flush control) over the shared `common-rv32i` fubs +
   `kestrel_regfile` idiom; `merlin_tb_top` (kestrel tb_top pattern:
   unified behavioral memory, backdoor loader, tohost mailbox).
4. DV: rv32ui battery → directed hazard suite → spike lockstep;
   GTKW save file alongside.
5. riscv-formal pipelined adaptation.
6. Book: *Simplified RV32I: merlin — pipelining*.

## 8. History

- 2026-10-30: PRD 0.1 scaffold. Scope and M1–M4 from the approved
  falcon-suite design spec (rung 2); M5–M7 proposed with defaults
  awaiting owner ruling.
