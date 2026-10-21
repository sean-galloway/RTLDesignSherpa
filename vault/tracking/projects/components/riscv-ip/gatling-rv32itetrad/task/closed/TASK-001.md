# TASK-001 — Tetrad compute FSM: kestrel-evaluation answered by gatling; PRD §7 decisions + alu-infer interface

**Status:** closed -- 2026-10-21 · **Priority:** high · **Filed:** 2026-10-17 · **Area:** projects/components/riscv-ip/gatling-rv32itetrad

## The original todo

"See if something like kestrel would work for the compute FSM for each
tetrad." Owner answered it directly the same day with the
[gatling PRD](../../../../../../../../projects/components/riscv-ip/gatling-rv32itetrad/PRD.md)
v0.1: **yes — kestrel-lineage, but barrel**: one RV32I+Xcell engine per
tetrad, 4 contexts = the 4 cells, F/D/X/W rotation (1 IPC per context per
4-cycle window), replacing the cell PRD's four ALU+FSM pairs. POP/PUSH/CFG/
ECTX custom-0 instructions; fixed hardware owns the credit/grant handshake,
the program owns policy.

This task now tracks what must be DECIDED/RECONCILED before or during
gatling bring-up.

## Owner decisions carried from gatling PRD §7 (open items)

1. **Context visibility** — implicit (hardware-only `sel`) vs explicit
   (CFG[2] returns context ID). Owner leaning implicit.
2. **Program image placement** — self-contained in input memory vs separate
   program region (second read port). Owner leaning separate-is-cleaner.
3. **Illegal-instruction policy** — context-lock vs tetrad-lock. Owner
   leaning context-lock.
4. **Xcell toolchain** — hand-assembled hex for bring-up; binutils fragment
   later. Non-blocking.

## Cross-document conflicts to resolve (flagged 2026-10-17)

5. **Where the bf16 alu-infer block lives in the gatling world.** Gatling's
   X state is a kestrel-derived INTEGER RV32I ALU (no M/A/F per PRD
   non-goals). The alu-infer block (bf16 function array + fp32 MAC,
   implemented + verified in `cell/rtl/` 2026-10-17, PRD v0.9 / MAS v0.5)
   has no slot in gatling as written. Options: (a) gatling supersedes
   alu-infer entirely (inference via integer ops — slow but honest);
   (b) alu-infer becomes an X-state coprocessor reached by reserved Xcell
   funct3 (needs an owner ruling — touches the ISA table);
   (c) alu-infer stays as the standalone v1 ALU block and gatling targets
   the CGRA-replacement boundary later. **Owner ruling needed.**
6. **Element model conflict.** Gatling PRD §5 cites cell PRD 0.1's
   B4/8/16/32 integer widths ("stands; width read via CFG"). The alu-infer
   PRD is normative for the ALU block: bf16-only (2×bf16 lanes per 32-bit
   line), B4–B32 explicitly superseded, cell PRD reconciled 2026-10-17.
   One of these must move — likely gatling §5 adopts the bf16 ruling or the
   CFG element-width field re-opens the integer mode.

## Owner ruling 2026-10-18

Owner: "the lowest module is cell. That will contain: the alu, a delta
node, some config registers, some ALU registers (A, B, C, D), a data-in
memory, a data-out memory. Once cell is fully defined and working then we
can figure out what gatling/tetrad needs to look like."

- **Item 5 answered in direction (c):** the bf16 alu-infer **stays** as the
  cell's ALU. Gatling does not displace it, and there is no integer-X
  coprocessor question to settle now — the final seam (Xcell-coprocessor
  vs replacement) is decided when gatling/tetrad is designed, after the
  cell works.
- **Item 6 moot while deferred:** gatling §5's B4–B32 citation remains a
  tracked conflict to fix when gatling work resumes; alu-infer's bf16
  model is normative in the meantime (cell PRD v0.3 §4, alu-infer PRD
  v0.50).
- **Recorded in:** cell PRD v0.3 (§1 owner direction 2026-10-18, §10),
  alu-infer PRD v0.50 (§5 deferral bullet), TILE_SPEC v1.5 (§11.13
  deferral + §10 cell→cell grant item — the `DEST` result-routing
  question surfaced the missing cell→cell grant rules).

## Owner ruling 2026-10-19 (deep-review synthesis — RESOLVES item 5)

Owner: "gatling sequences the four ALUs in its adjacent cells; it is a
barrel riscv with possible custom commands."

- **Item 5 closed, sequencer model:** gatling replaces the cell's exec FSM
  as its DRIVER — each barrel context's POP presents operands to the cell's
  alu-infer issue handshake and PUSH retires a result line. The bf16
  alu-infer ALU remains the datapath in every cell (its elastic valid/ready
  seam and tag-alignment contract unchanged). No integer-X coprocessor
  question, no "gatling supersedes alu-infer" — the program is the schedule.
- **Item 6 closed:** gatling §5's B4/8/16/32 citation replaced — CFG[0] now
  reports the alu-infer element mode (bf16 today; int8/fp32 via
  func_sel[8:7] are the roadmap, alu-infer PRD v0.50 §3 addendum).
- **FLUSH/KICK/WAIT defined:** gatling PRD v0.2 (2026-10-19) adds Xcell
  FLUSH (funct3=011, rs1[14:0] = drain destination coordinate,
  rs1[18:15] = sink-channel tag — programs the cell's FLUSH_DEST/FLUSH_TAG
  and triggers flush-and-send; answers TILE_SPEC 11.14) plus KICK (100) /
  WAIT (101) coordination pair, provisional pending the tetrad MAS.
  The earlier "gatling PRD has no flush instruction" gap in TILE_SPEC is
  closed by the same edit.
- **Remaining before RTL:** PRD 7 leanings to confirm (context visibility,
  program image placement, illegal-instruction policy); then gatling
  TASK-002 (RTL bring-up).

## Sequencing context

- Deliverable 1 of the gatling PRD (`docs/barrel_model/` study chapter)
  "writes first — it is the justification" — the kestrel-cost →
  interleave-fix argument. Scaffold exists, chapter unwritten.
- alu-rv32i / alu-rv32f realizations: **re-sequenced by the owner
  2026-10-18** — the queue is **cell first, then gatling**; the RV ALUs
  (drop-in blocks for the falcon cores' ALU slots; the definitions stay
  home in compute-eng-ip) wait behind both. The earlier "all three ALUs
  tested together on the board" goal stands, later. Gatling does not
  change that queue; it changes what consumes the ALU at the cell seam.

## References

- `projects/components/riscv-ip/gatling-rv32itetrad/PRD.md` (v0.1, authority)
- `projects/components/compute-eng-ip/alu-infer/PRD.md` (v0.50 — owns the
  ALU block + element model; §5 records the 2026-10-18 deferral)
- `projects/components/compute-eng-ip/cell/docs/PRD.md` (v0.3 — the cell is
  the lowest module; §4 reconciled to the elastic pipeline and the A–D/T
  register file)
- `projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md` §11.13
  (v1.5 — tetrad core deferred; §10 carries the cell→cell grant item)

## Resolution (2026-10-21)

The last open items were settled by the owner when the RTL started, and are
recorded in PRD v0.3 section 7:

- Item 1 (context visibility): implicit. CFG[2] stays reserved.
- Item 2 (program image placement): separate. Each context has its own
  program/data region (gatling_mem_bram, one 16 KB bank per context); the
  cell's POP input memory is separate and arrives with Xcell.
- Item 3 (illegal-instruction policy): context-lock. Every halt locks only
  its context; built and tested (test_gatling_core context_lock and
  xcell_locks).
- Item 4 (toolchain): non-blocking, unchanged; bring-up programs are
  hand-encoded in the DV.
- Items 5-6 were already closed by the 2026-10-19 ruling.

The RTL itself is gatling TASK-002.

