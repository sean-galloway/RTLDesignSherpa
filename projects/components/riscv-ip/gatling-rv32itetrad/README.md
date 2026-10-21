# gatling — Tetrad Compute Engine (barrel RV32I + Xcell)

**Directory:** `compute-eng-ip/gatling/` — the compute-eng-ip family
(alongside `cell/`, `tile/`, `hive-serv/`).
**Codename:** gatling — the barrel machine; one datapath, four barrels.
**ISA:** RV32I base + `Xcell` non-standard extension (custom-0/custom-1 space).
**Status:** PRD 0.3; the RV32I barrel is built and verified (rv32ui 168/168
across four contexts with spike lockstep, riscv-formal 42/42 on context 0),
and runs four harts on the Nexys A7. Xcell is next.

Gatling is the per-tetrad compute engine of the tile: one barrel
RV32I processor with **4 architectural contexts**, one context per
cell of the tetrad. Owner ruling 2026-10-19: gatling sequences the
four ALUs of its adjacent cells. The barrel core is the programmable
sequencer for the tetrad — each context runs a small program whose
POP presents operands to the cell's alu-infer issue handshake and
whose PUSH retires a result line — while the bf16 ALU datapath in
every cell stays in place. The earlier owner decision (2026-10-17):
*"Instructions"* over MMIO for fabric handshake, and a mini RV per
tetrad over per-cell ALUs.

Derived from `riscv-ip/kestrel-rv32i` (single-cycle RV32I): same ISA
base, same fub vocabulary (alu / decode / imm_gen / regfile), same
verification doctrine (spike lockstep, rv32ui battery, cocotb on the
rds-dv rails). The delta is the microarchitecture: single-cycle →
multi-cycle FSM → 4-context barrel interleave, so the multi-cycle CPI
cost is amortized to ~1 IPC per context.

## Documents

- **PRD.md** — product requirements: ISA (incl. Xcell encoding table),
  barrel model, cell-PRD contract fit, verification, open items.
- `docs/gatling_has/` — hardware architecture spec (arrives with RTL).
- `docs/gatling_mas/` — micro-architecture spec (arrives with RTL).
- `docs/barrel_model/` — the barrel-processor study chapter: kestrel's
  single-cycle cost as motivation, the interleave that hides it.

## Layout

- `rtl/top/gatling_core.sv` — the barrel: F/D/X/W rotation over four
  contexts (four PCs, halt per context, per-context run control, RVFI).
- `rtl/fub/gatling_regfile.sv` — the four context register files, one
  block RAM ({context, register}), registered read.
- `rtl/fub/gatling_mem_bram.sv` — one 16 KB program/data bank per context,
  AXIL loader, per-context run/status registers (the board's memory).
- decode / immediates / ALU are kestrel's (`kestrel_decode`,
  `kestrel_imm_gen`, `kestrel_alu`, `kestrel_pkg`), used unchanged through
  kestrel's filelists: one ISA, one source.
- `rtl/includes/gatling_pkg.sv`; `rtl/filelists/` per repo convention.
- `dv/` — cocotb on the `make/tests.mk` rails: regfile unit, directed
  barrel tests, the rv32ui battery and the fuzz battery on all four
  contexts at once (kestrel's golden interpreter and spike lockstep),
  and the AXIL memory system.
- `formal/gatling/riscv-formal` — riscv-formal on context 0 with the
  other three contexts free.
- Board: `projects/fpga-systems/NexysA7/riscv-ip/gatling`.
- Xcell (`gatling_xcell.sv`, `gatling_xcell_pkg.sv`) lands with the cell
  seam; until then custom-0 decodes as illegal and locks its context.

## Relationship to cell / tile / hive-serv

- `cell/` PRD 0.1 blocks stand; gatling **drives** the execution FSM
  slot, upgraded to a programmable sequencer. The bf16 ALU datapath
  remains in each cell; input memory, result memory, packetizer, and
  credit/grant contracts are unchanged. Gatling never originates config
  traffic; cell configuration arrives in-band over delta.
- `tile/` TILE_SPEC §11 hierarchy stands: 4 gatlings per tile (one per
  tetrad), tetrad MonBus merge observes all four contexts.
- `hive-serv/` stays the control plane; gatling is data plane, like cell.

Naming note: gatling is **not** a falcon-suite rung (see
`riscv-ip/README.md` — "the ladder again, nothing more"). It consumes
kestrel's ISA base but teaches the tile, not the pipeline.
