# GATLING PRD — Tetrad Compute Engine

**Version:** 0.1 (scaffold)
**Date:** 2026-10-17
**Owner decision inputs:** "Instructions" (over MMIO) for fabric
handshake; mini RV per tetrad (over per-cell ALU+FSM); codename
gatling (barrel machine).
**Supersedes:** nothing — cell PRD 0.1 datapath blocks stand, with the
ALU + execution FSM slot upgraded to gatling (this engine).

---

## 1. Purpose

Give each tetrad of the compute tile a programmable engine small
enough to instantiate four times per tile, powerful enough to run
compiled programs over cell input data, and honest enough to teach:
the barrel processor as the kestrel→merlin lesson, inverted — instead
of pipeline stages hiding latency for one stream, N contexts hide the
multi-cycle latency of one shared datapath.

The cell PRD's fixed `ALU + execution FSM (config-selected fn)`
becomes *the program is the config*. Mode bits that remain
(element width, credit batch N) move to the CFG read path.

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
|        000000000000     |  000  |  rs1    | 0x0B   |  POP
|        000000000000     |  001  |  rs1    | 0x0B   |  PUSH
|        000000000000     |  010  |  00000  | 0x0B   |  ECTX
+-------------------------+-------+---------+--------+
funct3 010+ : reserved (WAITCD/WAITGT live here if blocking-POP/PUSH
            hardware interlock proves insufficient in bring-up)
```

| Instr | Action | Blocking behavior |
|---|---|---|
| `CFG rd, imm` | rd ← mode-register[imm]: 0=element width (B4/8/16/32), 1=credit batch N, 2=context ID (read-only, see §7 open item), 3+=reserved | never blocks |
| `POP rd` | rd ← next element of this context's input memory; head advances; consumed-line credit returned to rapids per credit-batch config | context stalls if input empty — hardware interlock, not a spin |
| `PUSH rs1` | rs1 → this context's result memory; tail advances; grant requested on result path; packetizer batches X flits | context stalls if no grant |
| `ECTX` | context done: freeze PC, raise done status to tetrad MonBus, release datapath share; context restarts on reset/config reload | drains at next context boundary |

Design note (owner doctrine): fixed hardware owns the line-rate
handshake (credit/grant detection, memory ports); the program owns
policy. POP/PUSH blocking interlocks subsume the explicit WAIT
instructions — a context that would wait simply isn't scheduled.
WAIT* opcodes are reserved as an escape hatch, not a plan.

Element semantics: with element width < 32, POP zero-extends into rd
and PUSH takes the low bits of rs1; packing/unpacking is the
program's business (one ANDI/SLTI pair, honest and visible).

### 3.2 Assembly mnemonics

`gatling_pop`, `gatling_push`, `gatling_cfg`, `gatling_ectx` as
canonical toolchain names; assembler aliases `pop/push/cfg/ectx` live
in the Xcell binutils fragment when the flow arrives (§8).

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
4-cycle window ⇒ 1 IPC per context, one ALU, one decoder, one Xcell
unit, **four** register files + PCs (the cheap replication) —
replacing the cell PRD's four ALU+FSM pairs.

### 4.2 Structural hazards (all resolved by rotation, by construction)

- ALU/decoder/memory-port conflict: impossible — one user per state.
- Input/result memory port conflict across contexts: impossible —
  each context owns its cell's memories, addressed by `sel`.
- Interlock stall (POP empty / PUSH no-grant): only `sel` stalls;
  rotation skips it (bubble) — three contexts keep the datapath busy.

### 4.3 Branch behavior

Predict-not-taken, resolved in X (kestrel semantics carry: the branch
decision is one ALU comparison). A taken branch costs the rotating
window one bubble for that context — no flush machinery, no BTB. The
predictor study belongs to peregrine, not here.

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
| Element widths B4/8/16/32 | stands; width read via CFG |
| ALU + execution FSM (config-selected fn) | **replaced by gatling** — this PRD |
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

1. **Context visibility:** implicit (hardware-only `sel`; software
   cannot tell contexts apart — simplest, binaries uniform) vs
   explicit (CFG[2] returns context ID, enabling per-context
   specialization). Leaning implicit; one word settles it.
2. **Program image placement:** input memory holds both program and
   data (self-contained cell, POP-after-code addressing) vs separate
   program region (needs a second read port or F-state fetch from
   program image, D-state POP from data). Separate is cleaner;
   self-contained is cheaper. Open.
3. **Illegal-instruction policy:** context-lock (proposed §4.4) vs
   tetrad-lock. Leaning context-lock.
4. **Xcell binutils/toolchain:** hand-assembled hex for bring-up;
   gcc/binutils fragment later. Non-blocking.

## 8. Deliverables & sequencing

1. `docs/barrel_model/` study chapter (kestrel cost → interleave fix)
   — writes first, it is the justification.
2. `gatling_has` + ISA appendix (Xcell table as authority).
3. RTL: fubs (kestrel-derived) → `gatling_top` barrel + Xcell unit →
   flists; unit TBs per fub on repo rails.
4. Spike lockstep bring-up of the RV32I subset; then Xcell directeds.
5. Tetrad integration when `tetrad.sv` lands in `tile/`.

## 9. History

- 2026-10-17: PRD 0.1 scaffold. Owner decisions: instructions over
  MMIO; mini RV per tetrad; codename gatling; four contexts = four
  cells; blocking POP/PUSH interlock; ECTX exit. Cell PRD 0.1
  contracts confirmed unchanged outside the replaced ALU/FSM block.
