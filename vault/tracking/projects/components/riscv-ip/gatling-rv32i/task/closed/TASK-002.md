# TASK-002 — gatling RTL bring-up: barrel model chapter, RTL, HAS/MAS

**Status:** CLOSED 2026-11-26 · **Priority:** high · **Filed:** 2026-10-19 · **Area:** projects/components/riscv-ip/gatling-rv32i

## Why

Gatling is PRD-only (v0.2): no RTL, and `docs/gatling_has/`,
`docs/gatling_mas/`, `docs/barrel_model/` are stubs. It is on the critical
path for tile milestone M1 (tetrad on the FPGA — tile TASK-002). Per the
2026-10-19 owner ruling, gatling sequences the four alu-infer ALUs of its
adjacent cells via POP/PUSH/FLUSH; the program is the schedule.

## What

1. `docs/barrel_model/` study chapter first (PRD 8.1: "writes first — it is
   the justification"): the kestrel-cost -> interleave-fix argument for the
   4-context barrel.
2. Gatling RTL: 4-state F/D/X/W barrel, 4 context PCs + register files,
   shared ALU/decoder/Xcell unit, POP/PUSH/CFG/ECTX/FLUSH/KICK/WAIT
   (custom-0 0x0B, PRD 3.1 v0.2), per-context MonBus status (active, stall
   reason, done).
3. HAS + MAS stubs fill in as the RTL lands (PRD 8.2/8.3).
4. Hand-assembled hex for bring-up programs; binutils fragment later
   (PRD 7, non-blocking).

## Done when

Gatling RTL runs a hand-assembled tetrad program in DV: four contexts POP
operands into the cell ALU issue handshake, PUSH results, FLUSH drains to a
programmed destination; func+gate green; HAS/MAS no longer stubs.

## Notes

Sequenced after the cell works standalone (cell TASK-001/002) — the cell is
the lowest module, owner direction 2026-10-18. Confirm the PRD 7 leanings
(gatling TASK-001) before the RTL freezes them.

## Progress (2026-10-21)

Owner scope for the first pass: the RV32I barrel first, four harts on the
Nexys A7; Xcell after. Done in that pass:

- RTL: gatling_core (F/D/X/W over four contexts, kestrel's decode/imm_gen/ALU
  unchanged, context-lock halts, per-context run control), gatling_regfile
  (four context files in one block RAM), gatling_mem_bram (one bank per
  context, AXIL loader, per-context status). Custom-0 decodes as illegal.
- DV (dv/tests, make/tests.mk rails, full level from clean-all): rv32ui
  168/168 (42 images x 4 contexts, four different at once, spike + golden
  lockstep), fuzz 200/200 streams dual-golden, AXIL battery 168/168,
  directed barrel tests, regfile unit; mutation-checked.
- Formal: formal/gatling/riscv-formal 42/42 on context 0 with contexts 1-3
  free (proves isolation); mutation-checked (reg, pc_fwd, liveness fail on
  planted cross-context bugs).
- Board: projects/fpga-systems/NexysA7/riscv-ip/gatling.

Still open for "Done when": Xcell (POP/PUSH/CFG/ECTX/FLUSH/KICK/WAIT) against
the cell's alu-infer issue handshake, a hand-assembled tetrad program in DV,
and the HAS/MAS growing with it.

## Decision (2026-10-21): WAIT covers WFI

A review against the RISC-V books in the library (PRD 3.3) found `WFI` decodes as illegal and halts the
context, where the spec allows a no-op. Owner: keep that, deliberately; the Xcell `WAIT` is the context's
way to wait, because it has an event to wait on. Design `WAIT` so a context that waits gives nothing up
but its own slot (the rotation is fixed).


## Resolution (2026-11-26): Xcell built, the tetrad program runs in DV

The RV32I barrel was done in October (above); this closes the rest of "Done
when". Owner decisions this pass (2026-11-26): CFG on funct3 110 with an
I-type index (the PRD 0.2 drawing made a CFG of index 0 encode exactly as
POP); register x0 is the ALU port (`POP x0` issues the cell's function,
`PUSH x0` retires its result; any other register moves a line between the
memory and the program); KICK / WAIT a one-shot barrier; DV on the real cell
blocks. Not asked, decided here and recorded in the MAS: acc_ctrl rides in
POP x0's insn[21:20] (zero is HOLD, the 0.2 encoding's zeros).

- **RTL.**
  - `gatling_core`: `XCELL_EN` (default 0, so the barrel-only builds,
    rapids-g and the Nexys A7 board are unchanged and custom-0 stays
    illegal there). With 1, the seven instructions go to an `xc_*` port in
    X; `xc_ok = 0` is an interlock stall: no retirement, no write, PC kept,
    so the context refetches the same instruction next window. ECTX halts
    with cause 8 and raises `done`.
  - `gatling_xcell` (new): per context the input-memory head, result-memory
    tail, the two-line issue stager, the FLUSH latch and the event bit.
  - `gatling_tetrad` (new): the core, the Xcell unit and per context
    compute-eng-ip's `cell_mem_in`, `alu_infer_top` and `cell_mem_out`; the
    rest of the cell (rx, packetizer, credit, cfg; cell TASK-001/002) is
    its ports. `cell_mem_in.f` / `cell_mem_out.f` added in the cell area
    (cell_top.f now includes them).
- **DV** (`dv/tests`, rails): `test_gatling_xcell` (7 directed cases:
  CFG, POP/PUSH through a register with both interlocks, four ALU row
  families and a MAC chain against alu-infer's golden, FLUSH backpressure,
  KICK/WAIT barrier and done, a context stalled while three finish) and
  `test_gatling_tetrad` -- the hand-assembled tetrad program: one binary
  on four contexts over a MAC, ADD, RELU and COMPARE cell, CLEAR + N
  ACCUMULATE, KICK, WAIT on all four, FLUSH, ECTX, with random gaps on the
  fill, drain and drain controller. Six planted RTL bugs each fail the
  suite (one was missed at first; the ALU cases now hold one cell's input
  back).
- **Implementation** (xc7a100t-1 OOC, 10 ns, 0.2 ns uncertainty):
  `gatling_xcell` 383 LUT / 687 FF, +4.002 ns; `gatling_tetrad` with the
  bf16-only ALU and the ALU's internal endpoints excluded, +0.144 ns.
- **Docs:** PRD 0.5 (3.1 encoding and semantics, 4.2, history); HAS ch02
  Xcell table and timing, ch03 tetrad seams; MAS core chapter (port and
  stall), new gatling_xcell and gatling_tetrad chapters with Figure 2.3,
  rotation, verification, configuration; both books rebuilt at v0.1.

- **Regression** (2026-11-26, `make clean-all && make run-all-full-parallel`):
  gatling-rv32i 69/69, no reruns; riscv-formal gatling 42/42 PASS
  (XCELL_EN = 0 harness); rapids fub_g / macro_g / top_g 270 + 183 PASS
  (rapids_seq_g tie-off); Nexys A7 gatling board lint + sim 3/3. The
  compute-eng-ip cell suite passes gate and func on the split filelists;
  its full cell fails before simulating because `test_cell.py` has no
  `full` level (KeyError at module load), a cell-area test defect.

Findings outside gatling, not fixed here (compute-eng-ip's):
- alu-infer's bf16 rows are combinational at their default latencies: a
  211-level path, -128.8 ns at 10 ns. Four full ALUs are 95.6k LUT as logic
  and do not fit the xc7a100t (63.4k).
- `cell_mem_in` / `cell_mem_out` write their arrays inside a reset block,
  so each 32-line memory is ~1,060 flops, not a distributed RAM.

Not done here: a formal deadlock-freedom proof of the interlock (PRD 6,
"where it pays"); the tetrad on a board (no tetrad build target exists).
