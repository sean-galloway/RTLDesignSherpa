# gatling — Tetrad Compute Engine (barrel RV32I + Xcell)

**Directory:** `compute-eng-ip/gatling/` — the compute-eng-ip family
(alongside `cell/`, `tile/`, `hive-serv/`).
**Codename:** gatling — the barrel machine; one datapath, four barrels.
**ISA:** RV32I base + `Xcell` non-standard extension (custom-0/custom-1 space).
**Status:** PRD 0.1 (this document set); no RTL yet.

Gatling is the per-tetrad compute engine of the tile: one barrel
RV32I processor with **4 architectural contexts**, one context per
cell of the tetrad. It replaces the per-cell ALU + execution FSM of
the cell PRD 0.1 datapath decision with a programmable engine — the
owner decision recorded in the PRD (2026-10-17): *"Instructions"* over
MMIO for fabric handshake, and a mini RV per tetrad over per-cell ALUs.

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

## Layout (RTL lands per PRD §8)

- `rtl/top/gatling_top.sv` — barrel engine: shared fetch/decode/execute
  FSM + 4 context files (PC + regfile) + Xcell unit.
- `rtl/fub/` — `gatling_alu.sv`, `gatling_decode.sv`, `gatling_imm_gen.sv`,
  `gatling_regfile.sv` (context-file wrapper), `gatling_xcell.sv`.
- `rtl/includes/` — Xcell encoding header (`gatling_xcell_pkg.sv`).
- `rtl/filelists/` — flist per repo convention.
- `dv/` — cocotb, repo-wide `make/tests.mk` rails; spike lockstep on the
  RV32I subset; Xcell unit tests + tetrad integration TB.

## Relationship to cell / tile / hive-serv

- `cell/` PRD 0.1 blocks stand; gatling **is** the ALU + execution FSM
  slot, upgraded to a processor. Input memory, result memory, packetizer,
  credit/grant contracts are unchanged.
- `tile/` TILE_SPEC §11 hierarchy stands: 4 gatlings per tile (one per
  tetrad), tetrad MonBus merge observes all four contexts.
- `hive-serv/` stays the control plane; gatling is data plane, like cell.

Naming note: gatling is **not** a falcon-suite rung (see
`riscv-ip/README.md` — "the ladder again, nothing more"). It consumes
kestrel's ISA base but teaches the tile, not the pipeline.
