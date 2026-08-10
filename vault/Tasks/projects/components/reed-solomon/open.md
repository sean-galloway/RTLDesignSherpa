<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# reed-solomon — Open (accepted, not started)

---

## RS-001 — Stand up the Reed-Solomon component
**Status:** open 2026-08-09 (created when COMMON-009 was dropped — Sean's
call: R/S is component work, not rtl/common library work)
**Priority:** P3 — waits on a real consumer (NAND flash, comms, storage)

Library ECC is Hamming SECDED only. BCH/Reed-Solomon was tracked as a
common-library enhancement (COMMON-009) and dropped: an R/S codec brings a
GF(2^m) arithmetic layer, syndrome/Berlekamp-Massey/Chien machinery and
configuration surface that belongs in its own component with its own PRD,
DV area and task pages — the shape of `projects/components/bridge/` or the
dmas, not a single-file primitive.

When a consumer appears:
- PRD first: symbol width m, t (correctable symbols), shortened codes,
  encoder-only vs full decoder, throughput target — and whether BCH (the
  binary special case, previously tracked alongside R/S and also ended with
  COMMON-009) is in scope here or stays out.
- Location: `projects/components/reed-solomon/` (rtl/, dv/, PRD.md),
  filelists registered per [[filelists]] from day one.
- Reuse survey per CLAUDE.md before any new RTL: `dataint_ecc_*` shows the
  house ECC interface conventions; the GF layer is new ground.

History: a docs-only `projects/components/bch/` placeholder (PRD/README/
TASKS, no RTL, no tests) was deleted 2026-07-23. Do not recreate
placeholder collateral — this task page IS the placeholder; the component
directory gets created when work actually starts.
