# TASK-001: implement merlin per PRD v0.2 (5-stage pipelined RV32I)

**Priority:** P2
**Status:** closed
**Owner:** seang

Filed 2026-10-31 on the owner's M5–M7 rulings. All seven PRD decision rows
are DECIDED (`projects/components/riscv-ip/merlin-rv32i/PRD.md` v0.2); the
falcon-suite design spec (rung 2) is the design source. Implementation
completed 2026-11-01.

## Closure

- Core RTL, DV, riscv-formal, GTKW save file, and doc skeletons committed.
- DV: 36/36 tests green (rv32ui 42/42, spike lockstep, fuzz).
- riscv-formal: 42/42 retire checks green.
- GTKW verified against a real `WAVES=1` FST dump (83 signals cross-checked).
- Vault gates clean (link ratchet, task IDs, filelist registry).
- Full HAS/MAS book prose is a follow-on task; this task delivered skeletons only.

## Scope (PRD §7 sequencing)

1. `merlin_has` / `merlin_mas` book skeletons (hazard/forwarding chapters
   carry the book; GTKW waveforms embedded — kestrel/gatling precedent).
2. RTL: `merlin_core` — if_id / id_ex / ex_mem / mem_wb pipeline registers,
   hazard + forwarding unit (EX/MEM→EX and MEM/WB→EX, EX/MEM priority),
   load-use interlock, branch resolve in EX with 2-bubble flush — over the
   shared `common-rv32i` fubs (decode / imm_gen / alu / pkg, unchanged) and
   the kestrel regfile idiom; `merlin_tb_top` on the kestrel pattern
   (unified behavioral memory, backdoor loader, tohost mailbox,
   `mem_wait` seam tied off).
3. DV: rv32ui battery → directed hazard suite (forwarding matrix,
   load-use matrix, branch-flush cases) → spike lockstep; GTKW save file
   from day one.
4. riscv-formal retire-interface (WB) adaptation of kestrel's checks.

## Done when

- rv32ui battery green, directed hazard suite green, spike lockstep green.
- riscv-formal retire checks pass at the pipelined WB interface.
- GTKW save file committed and verified against a real FST dump (the
  load-use bubble and the branch flush are the two waveforms the book
  needs).
- Vault gates clean (`check_task_ids`, link ratchet, filelist registry).
