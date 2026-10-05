# TASK-016: andesite macro integration + training/dfi/axi4 layer births

> Source: P3 close-out follow-on; owner direction 2026-10-04 ("finish 1/2/3 on
> andesite"). Plan: `docs/superpowers/plans/2026-10-04-andesite-macro-integration.md`.
> Spec: `.superpowers/sdd/2026-10-04-andesite-rtl-bootstrap-p3/progress.md` (P3
> ledger punch list).

**Priority:** P2
**Status:** open
**Owner:** seang

Execute the P3-recorded follow-on work, native inline on main, per-task
commits:

1. Rewire the scheduler macro's `u_init`/`u_mode_reg` to the P1
   `init_sequencer`/`mode_register` (the macro does not fully elaborate
   today: 49 PINNOTFOUND at the carried scoria DDR3 pin names).
2. Re-derive the parked macro suite against the P1 DDR4 init sequence and
   un-park it (tracked).
3. Land `andesite_dfi_cmd_path` around the P1 single-shot formatter;
   widen the scheduler command word with `bg[1:0]`.
4. Birth `andesite_training_layer` (holds wrlvl/rdlvl/ca_train, owns the
   DFI training pins + one-active mux; wrlvl moves out of the scheduler
   macro) per the owner ruling recorded in MC-001.
5. Deferred review minors M-1…M-9 from the P3 whole-branch review.
6. Birth `andesite_dfi_layer` (CDC → cmd_path → serializer/aligner, DBI
   wired, three CS-qualified lanes) and `andesite_axi4_layer` (scoria
   rename-carry + logic-parity gate).
7. Assemble `andesite_core` + the 4-test top suite; final gate, doc 0.5
   rows, whole-branch review on a fresh agent.

Out of scope (recorded, not this task): the LPDDR4 CA-path formatter
submodule (TASK-008 follow-on), any CSR block generation (PeakRDL),
multi-rank, basalt.

Closes when Task 9 of the plan lands: every andesite suite green,
registry `--check` PASS, doc rows reconciled, review verdict recorded.
