# GATLING PRD — Tetrad Compute Engine

**Version:** 0.3 (2026-10-21 — first RTL: the RV32I barrel, four harts on
the Nexys A7; PRD 7 items 2-4 decided; Xcell deferred to the cell seam.)
**Date:** 2026-10-21
**Owner decision inputs:** "Instructions" (over MMIO) for fabric
handshake; mini RV per tetrad (over per-cell ALU+FSM); codename
gatling (barrel machine).
**Supersedes:** PRD 0.1 wording that described gatling as replacing the
per-cell ALU — the ALU stays; gatling replaces the execution FSM as its
driver.

---

## 1. Purpose

Give each tetrad of the compute tile a programmable engine small
enough to instantiate four times per tile, powerful enough to run
compiled programs over cell input data, and honest enough to teach:
the barrel processor as the kestrel→merlin lesson, inverted — instead
of pipeline stages hiding latency for one stream, N contexts hide the
multi-cycle latency of one shared datapath.

Owner ruling 2026-10-19: gatling sequences the four ALUs of its
adjacent cells. The barrel RV32I core is the programmable sequencer
for its tetrad — each context runs a small program whose POP presents
operands to the cell's alu-infer issue handshake and whose PUSH retires
a result line; the ALU keeps its elastic valid/ready seam and
tag-alignment contract unchanged. *The program is the config*. Mode
bits that remain (element width, credit batch N) move to the CFG read
path. Gatling is also a barrel RISC-V with custom commands (Xcell:
CFG/POP/PUSH/ECTX/FLUSH/KICK/WAIT) — the program is the schedule.
Gatling never originates config traffic; cell configuration arrives
in-band over delta.

## 2. Non-goals

- Not a falcon-suite rung. No performance chase; IPC-per-context ~
  1 is the target, not a benchmark result.
- Not per-cell processors. One engine per tetrad; the four cells
  are the four contexts.
- No caches, no virtual memory, no interrupts/CLINT, no M/A/F.
  (Machine state is 4× {PC, x1..x31} + mode CSR shadow. Full stop.)
- No CSRs as a subsystem — `Zicsr` deliberately absent; config
  reaches the program through the Xcell `CFG` instruction.

## 3. ISA — RV32I + Xcell

Base RV32I exactly as kestrel implements it (same opcode map, same
trap/halt contract) so the spike lockstep flow and rv32ui battery
carry unchanged. The Xcell extension occupies the custom-0 opcode
(`0001011`, 0x0B) — reserved space, zero collision risk with future
standard extensions.

### 3.1 Xcell encoding (custom-0, opcode 0x0B)

```
 31                     15 14   12 11      7 6       0
+-------------------------+-------+---------+--------+
|        imm[31:12]       | funct3|   rd    | 0x0B   |  CFG
|        000000000000     |  000  |   rd    | 0x0B   |  POP
|        000000000000     |  001  |  rs1    | 0x0B   |  PUSH
|        000000000000     |  010  |  00000  | 0x0B   |  ECTX
|        000000000000     |  011  |  rs1    | 0x0B   |  FLUSH
|        000000000000     |  100  |  rs1    | 0x0B   |  KICK
|        000000000000     |  101  |  rs1    | 0x0B   |  WAIT
+-------------------------+-------+---------+--------+
funct3 110/111 : reserved.
funct3 010 (ECTX) and 011/100/101 (FLUSH/KICK/WAIT) added in v0.2.
The v0.1 WAITCD/WAITGT placeholders are superseded by KICK/WAIT pending
the tetrad MAS.
```

| Instr | Action | Blocking behavior |
|---|---|---|
| `CFG rd, imm` | rd ← mode-register[imm]: 0=element mode (0=bf16: 2 bf16 lanes per 32-bit line, fp32 accumulate; other values reserved for the int8/fp32 roadmap per alu-infer PRD `func_sel[8:7]`), 1=credit batch N, 2=context ID (read-only, see §7 open item), 3+=reserved | never blocks |
| `POP rd` | rd ← next element of this context's input memory; head advances; consumed-line credit returned to rapids per credit-batch config | context stalls if input empty — hardware interlock, not a spin |
| `PUSH rs1` | rs1 → this context's result memory; tail advances; grant requested on result path; packetizer batches X flits | context stalls if no grant |
| `ECTX` | context done: freeze PC, raise done status to tetrad MonBus, release datapath share; context restarts on reset/config reload | drains at next context boundary |
| `FLUSH rs1` | rs1[14:0] → cell `FLUSH_DEST` {ext,level,X,Y,Z}; rs1[18:15] → cell `FLUSH_TAG` (RAPIDS sink-channel tag); trigger cell flush-and-send of result memory | context stalls until drain controller accepts command |
| `KICK rs1` | raise tetrad coordination event on the tetrad MonBus with value `rs1`; provisional encoding pending tetrad MAS | non-blocking once event is posted |
| `WAIT rs1` | stall context until the tetrad coordination condition in `rs1` is observed (e.g. group-done bitmask); provisional encoding pending tetrad MAS | context stalls until condition true |

Design note (owner doctrine): fixed hardware owns the line-rate
handshake (credit/grant detection, memory ports); the program owns
policy. POP/PUSH blocking interlocks subsume most waiting — a context
that would wait simply isn't scheduled. WAIT is an explicit escape
hatch for cross-context coordination, not the common case.

Element semantics: with element width < 32, POP zero-extends into rd
and PUSH takes the low bits of rs1; packing/unpacking is the
program's business (one ANDI/SLTI pair, honest and visible).

### 3.2 Assembly mnemonics

`gatling_pop`, `gatling_push`, `gatling_cfg`, `gatling_ectx`,
`gatling_flush`, `gatling_kick`, `gatling_wait` as canonical toolchain
names; assembler aliases `pop/push/cfg/ectx/flush/kick/wait` live in
the Xcell binutils fragment when the flow arrives (§8).

## 4. Barrel microarchitecture

### 4.1 The model

Kestrel's single cycle is PC + regfile-read + ALU + memory in one
combinational path — the teaching point and the timing/area cost.
Gatling splits that into a 4-state FSM:

```
  F  : address = ctx[sel].pc; fetch word from ctx program image
  D  : decode; read ctx[sel] regfile (rs1/rs2 by decoded index)
  X  : ALU / Xcell unit (POP/PUSH/CFG execute here; interlock check)
  W  : writeback to ctx[sel] regfile; pc advance (or branch target)
```

Each FSM state advances context `sel` one step; `sel` rotates
0→1→2→3→0. Steady state: every context retires one instruction per
4-cycle window ⇒ 1 IPC per context, one gatling ALU, one decoder, one
Xcell unit, **four** register files + PCs (the cheap replication) —
replacing the cell PRD's four execution FSMs while each cell keeps its
own bf16 ALU datapath (owner ruling 2026-10-19).

### 4.2 Structural hazards (all resolved by rotation, by construction)

- ALU/decoder/memory-port conflict: impossible — one user per state.
- Input/result memory port conflict across contexts: impossible —
  each context owns its cell's memories, addressed by `sel`.
- Interlock stall (POP empty / PUSH no-grant): only `sel` stalls;
  rotation skips it (bubble) — three contexts keep the datapath busy.

### 4.3 Branch behavior

Resolved in X (kestrel semantics carry: the branch decision is one
comparison) and written to the context's PC at the end of X, two cycles
before that context's next fetch. As built (2026-10-21) a taken branch
therefore costs nothing -- no bubble, no flush machinery, no BTB, no
prediction. The predictor study belongs to peregrine, not here.

### 4.4 Halt/trap

No traps (no exceptions in base scope; illegal instruction →
context-local lock with status bit via MonBus, other contexts
continue — a tetrad is not a CPU, one bad cell must not sink the
tile). `ECTX` is the normal exit. Reset is per-tile from the tile
root; program load via the fabric config path (PKT_CONFIG) into each
cell's program image region — kestrel's `mem_loader`/AXIL pattern
becomes the in-band loader, per the standing in-band-only fabric
decision.

## 5. Contract fit (cell PRD 0.1, unchanged interfaces)

| Cell PRD block | Stand / change |
|---|---|
| delta_mesh_cell node, containment | stands — gatling sits behind the node's local port |
| Input memory, line fill by node from rapids | stands; per-context, addressed by `sel` |
| Result memory, X-flit batching, packetizer, grants | stands |
| Consumed-line credits to rapids, batch N (default 1) | stands; N read via CFG |
| Element widths B4/8/16/32 | superseded — alu-infer's bf16 element model (2 bf16 lanes per 32-bit line, fp32 accumulate) is normative; CFG[0] reports the alu-infer element mode (bf16 today; int8/fp32 modes are a roadmap item in the alu-infer PRD via `func_sel[8:7]`) |
| ALU + execution FSM (config-selected fn) | **replaced by gatling as the execution FSM driver** — the cell's bf16 ALU datapath remains; gatling issues it via POP/PUSH and the alu-infer elastic valid/ready seam (owner ruling 2026-10-19) |
| MonBus observation (per-cell → per-tetrad merge) | stands; gatling adds per-context status (active/stall-reason/done) to the observed set |

Consequences that must not fork: credit counting is in *elements
consumed* (POP), not instructions; grants are in *elements pushed*
(PUSH), not flits — flit batching stays inside the packetizer.

## 6. Verification

- **Base ISA:** spike lockstep on RV32I exactly as kestrel does it —
  reuse the rds-dv flow; rv32ui battery is the gate (42/42 precedent).
- **Xcell unit:** directed cocotb — POP empty-stall / credit batch
  N=1,2,4; PUSH grant/backpressure; CFG read of mode shadow;
  ECTX done/observability; element-width zero-extend and slice.
- **Barrel properties:** cocotb assertions — one retirement per
  context per rotation window; stall of context k never stalls j≠k;
  rotation fairness (round-robin, no starvation with all-runnable).
- **Tetrad integration:** the eventual `tetrad.sv` TB drives four
  input-memory streams, checks per-context result memories and the
  credit/grant ledger against the cell PRD reference model.
- **Formal (where it pays):** deadlock freedom of the interlock
  (POP-empty ∨ PUSH-no-grant ∧ no ECTX ⇒ eventually credit ∨ grant),
  following the repo's targeted-formal doctrine.

## 7. Open items (owner decisions needed)

1. **ALU-infer relationship:** RESOLVED 2026-10-19 — gatling is the
   programmable sequencer for the tetrad's four bf16 ALUs; each
   context runs a small program whose POP presents operands to the
   cell's alu-infer issue handshake and whose PUSH retires a result
   line; the ALU keeps its elastic valid/ready seam and tag-alignment
   contract unchanged. The v0.1 wording that made gatling "the ALU
   + execution FSM" is superseded.
2. **Context visibility:** RESOLVED 2026-10-21 (owner) — implicit.
   Software cannot tell the contexts apart; binaries are uniform. CFG[2]
   stays reserved.
3. **Program image placement:** RESOLVED 2026-10-21 (owner) — separate.
   Each context has its own program/data region (gatling_mem_bram: one
   16 KB bank per context, seen at every address); the cell's POP input
   memory is separate and arrives with Xcell.
4. **Illegal-instruction policy:** RESOLVED 2026-10-21 (owner) —
   context-lock. Any halt (ecall, ebreak, illegal, misaligned target or
   access) locks only its context; the other three keep running.
5. **Xcell binutils/toolchain:** hand-assembled hex for bring-up;
   gcc/binutils fragment later. Non-blocking.

Resolved/added in v0.2: the FLUSH/KICK/WAIT Xcell encodings of §3.1
(answer TILE_SPEC §11.14 and the alu-infer PRD §5 tetrad-coordination
pair). Their exact field layouts and MonBus integration remain
provisional pending the tetrad MAS.

Scope of the first RTL (owner, 2026-10-21): the RV32I barrel first --
four harts running the rv32ui battery on the Nexys A7 -- with the Xcell
custom-0 opcode decoding as illegal (context-lock) until the cell seam
exists. Xcell lands in the next pass.

## 8. Deliverables & sequencing

1. `docs/barrel_model/` study chapter (kestrel cost → interleave fix)
   — writes first, it is the justification.
2. `gatling_has` + ISA appendix (Xcell table as authority).
3. RTL: fubs (kestrel-derived) → `gatling_top` barrel + Xcell unit →
   flists; unit TBs per fub on repo rails.
4. Spike lockstep bring-up of the RV32I subset; then Xcell directeds.
5. Tetrad integration when `tetrad.sv` lands in `tile/`.

## 9. History

- 2026-10-21: PRD 0.3. First RTL (gatling_core, gatling_regfile,
  gatling_mem_bram): the RV32I barrel with kestrel's decode/imm_gen/ALU
  unchanged, every memory a one-stage block-RAM latency, no wait signal;
  four harts on the Nexys A7. Owner decisions: PRD 7 items 2-4 (implicit
  context, separate program regions, context-lock); RV32I barrel before
  Xcell. 4.3 corrected: a taken branch costs no bubble.

- 2026-10-19: PRD 0.2. Owner ruling: gatling sequences the four ALUs
  of its adjacent cells — the barrel core is the programmable
  sequencer for the tetrad, the cell's bf16 ALU remains the datapath,
  and gatling never originates config traffic. Added FLUSH/KICK/WAIT
  Xcell encodings; fixed POP to read `rd`; updated CFG[0] to report
  the alu-infer element mode.
- 2026-10-17: PRD 0.1 scaffold. Owner decisions: instructions over
  MMIO; mini RV per tetrad; codename gatling; four contexts = four
  cells; blocking POP/PUSH interlock; ECTX exit. Cell PRD 0.1
  contracts confirmed unchanged outside the replaced ALU/FSM block.
