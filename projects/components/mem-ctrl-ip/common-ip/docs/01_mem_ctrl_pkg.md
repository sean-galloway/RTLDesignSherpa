<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# mem_ctrl_pkg — the shared-core design

**Version:** 0.1 (design record; this tranche lands no RTL)
**Date:** 2026-10-04
**Status:** v0.1, filed with the andesite docs tranche. This document owns
the design of the family shared core — the package pumice, scoria and andesite
eventually share — and records why it doesn't exist yet. The migration it
describes is deferred to andesite RTL bring-up; nothing here touches a
shipping controller.

## Why the shared core is family property

Each controller today carries its own package: `pumice_pkg` (DDR2/LPDDR2),
`scoria_pkg` (DDR3/LPDDR3), and `andesite_pkg` (day one, this design's first
consumer). That's three near-identical packages, and it's deliberate —
scoria's header records the reasoning (`scoria_pkg.sv:13-18`): pumice's
`memtype_e` is one bit wide and already spent, widening it would change a CSR
in a measured, shipping design for a controller that had no RTL, and the
shared package becomes worth the migration when the DDR4/LPDDR4 controller
starts. A design that migrates two shipping controllers is family property, so
the design lives here and the controllers cite it.

## The memtype enum

History first. pumice's enum is one bit: `{MEMTYPE_DDR2 = 1'b0,
MEMTYPE_LPDDR2 = 1'b1}` (`pumice_pkg.sv:26-28`). scoria kept the width and
spent its bit on `{DDR3, LPDDR3}` (`scoria_pkg.sv:31-34`). The family enum has
six members — {DDR2, DDR3, DDR4, LPDDR2, LPDDR3, LPDDR4} — and here's the part
that needs saying out loud: **six values don't fit two bits.** scoria's header
anticipates a "two-bit memtype"; the family design honors that as the
generation field and rides the LP/DDR axis on a third bit:

| `memtype_e` | Member | `memtype_e[1:0]` generation | `memtype_e[2]` LP |
|---|---|---|---|
| 3'b000 | MEMTYPE_DDR2 | 2'b00 (generation 2) | 0 |
| 3'b001 | MEMTYPE_DDR3 | 2'b01 (generation 3) | 0 |
| 3'b010 | MEMTYPE_DDR4 | 2'b10 (generation 4) | 0 |
| 3'b100 | MEMTYPE_LPDDR2 | 2'b00 | 1 |
| 3'b101 | MEMTYPE_LPDDR3 | 2'b01 | 1 |
| 3'b110 | MEMTYPE_LPDDR4 | 2'b10 | 1 |
| 3'b011, 3'b111 | reserved | 2'b11 (generation 5, basalt) | — |

: Table 1.0: The family memtype encoding — one LP bit, a two-bit generation field

The generation field is the two-bit memtype scoria anticipated; basalt (DDR5)
takes 2'b11 when it exists. The reserved codes stay illegal — decode them as
an error, don't alias them.

## Shared inventory (named, not fielded)

The shared core carries the types every controller re-implements today.
They're named here, not fielded — the fields get designed at migration time
against the three consumers, and pretending otherwise is how you end up with
a struct nobody can change.

| Name | What it is | Landed precedent |
|---|---|---|
| `memtype_e` | the family enum above | new in this design |
| `decoded_addr_t` | the address-decoder result struct (row / col / bank / channel fields) | `pumice_pkg.sv:119-124` |
| `mem_timing_t` | the runtime timing shadow the core carries beside its CSR block | the `TIMINGS_*` register groups + consumers in pumice (`pumice_csr_pkg.sv`) |
| `mem_opcode_e` | the internal DRAM command opcode enum (4-bit `OP_*`) | carried pumice → scoria unchanged (`scoria_pkg.sv:39-60`) |

: Table 1.1: Shared types the migration owns

## Migration plan, and its conditions

The migration executes once, when andesite RTL bring-up starts (spec §3), and
both shipping controllers move together — that condition is scoria's own,
recorded at `scoria_pkg.sv:13-18`. Concretely:

1. **Neither shipping controller is touched before then.** pumice and scoria
   are measured designs; no CSR field width changes under them in isolation.
2. **The memtype CSR field widens 1 → 3 bits at the migration, in both
   controllers at once.** pumice's `PHY_TIMING.memtype` and scoria's
   equivalent change together, with the RTL that consumes them.
3. **The three near-identical packages are deliberate and time-boxed.**
   scoria recorded the same posture for its own duplication; andesite keeps a
   local `andesite_pkg` from day one (its contents are the andesite HAS ch5's
   business) and folds into `mem_ctrl_pkg` at migration.
4. **Fields are designed against consumers, not in advance.** Table 1.1 names
   the structs; the field layouts are migration-time work, ratified against
   three consumers instead of guessed for one.

## Recorded deferral

The refactor is **deferred to andesite RTL bring-up** (spec §3, settled
2026-10-03). This tranche is docs-only; no package file is created or modified
here. If andesite bring-up slips, this design waits — it isn't a reason to
touch the shipping controllers early.
