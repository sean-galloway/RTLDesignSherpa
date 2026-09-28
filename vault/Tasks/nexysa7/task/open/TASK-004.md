# TASK-004: ddr2-char harness needs TWO bridges, 8 bank-targeted masters each

> Migrated 2026-09-27 from `vault/Tasks/nexysa7/open.md` as **NEXYS-004** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** Medium
**Status:** [x] RTL + DV + host LANDED 2026-08-31; read/write mix sweep still open

**What landed (2026-08-31):**
- `chargen_regs` -- a GENERATED PeakRDL block (229 registers) holding all
  sixteen generators' config: `WR_GEN[8]` / `RD_GEN[8]` on a 0x40 stride, plus
  a global `GO` (sixteen singlepulse bits, so one write starts any subset on
  one cycle), `DONE` / `ERRORS` roll-ups and a `GEN_CONFIG` identity register
  driven from the harness's own parameters.
- `chargen_apb` slave at 0x000A0000; the config bridge regenerated 1x5 -> 1x6.
- `bridge_ddr2_char_wr` / `bridge_ddr2_char_rd` -- 8x1 AXI4 each, feeding
  pumice's AW/W/B and AR/R channel groups respectively.
- `ddr2_char_macro` rebuilt around a generate loop of 8 writers + 8 readers,
  both bridges, and run-level aggregates (`gen_wr_done` over LAUNCHED
  generators only, `gen_any_error`, `gen_crc_match` over launched pairs).
- `harness_csr`'s single-engine `WR_*`/`RD_*` window (0x100..0x1AF), its CTRL
  start bits, and the single CRC pair are RETIRED; the hole reads 0 and is
  deliberately not re-used.
- DV: `ChargenDriver` (dv/tbclasses) programs by register name over APB --
  the same path the board uses, so the register decode is now exercised in
  simulation instead of being bypassed by poked ports. New `bank_parallel`
  test drives all sixteen concurrently.
- Host: `DDR2CharDriver` gained a `chargen` Device and a `go(wr_mask, rd_mask)`;
  `program_wr_engine` / `start_wr` / `crc` kept their signatures with `gen=0`
  defaults, so the nine bring-up scripts were untouched.

**Two reserved-name traps found, both worth knowing before the next RDL:**
an RDL field named `value` generates `REG.value.value`, which the
declaration-order gate reports as use-before-declaration; a field named
`count` collides with RegisterMap's array-count metadata key and makes the
whole regmap fail to construct. Neither is caught by review -- the first
by `make lint`, the second only by loading the generated regmap.

**Still open:** the read/write mix sweep described below (the measurement the
split exists for), and the synthesis/timing check -- the previous build closed
at WNS +0.050 ns and this adds sixteen generators plus two crossbars.

**Original description follows.**
**Source:** Sean, 2026-08-30 — "the harness will need two bridges, one for
writes and one for reads. On each will be 8 masters each targeting a
different bank."

**Goal:** Restructure the DDR2 characterization harness so read and write
traffic are generated independently and every bank is driven concurrently.

- **Two bridges, split by direction** — one write, one read, rather than
  today's single shared path. Independent direction pressure is what lets a
  test hold one direction saturated while sweeping the other, and it stops
  read/write turnaround from being an accidental variable in every number.
- **8 masters per bridge, one per bank** — bank-parallel by construction, so
  the stimulus exercises the concurrency the scheduler is built around.
  Today's single-stream harness cannot reach the corner that separates the
  paging modes: the sim sweep shows every mode reading 100% with 8-way
  rotation and only `static_close`/`rbl_static` dropping (to 27.79%) once
  traffic is confined to ONE bank. A per-bank master array makes that a
  property of the harness rather than a hand-built address pattern.

**Why it matters for the numbers:** the flat ~12.7 MB/s board result was
traced to a fallback pinned on a single oldest bank (serialised ACT -> tRCD
-> access). A harness that cannot drive banks concurrently cannot tell that
apart from a controller that will not.

**Relation to existing work:** the harness bridge is already generated
(`bridge_ddr2_char_axil`, 1x5 after the obs_apb slot was added 2026-08-28) —
see `ddr2_char_framework/rtl/bridges/configs/`. Splitting it in two is a
config + regen job under CRITICAL RULE #0 (delete ALL generated output, then
regenerate), plus the harness rewire. Pairs with [[TASK-002]]
characterization. (It used to pair with [[PUMICE-016]] observer adoption —
"decide whether each bridge gets its own observer instance before wiring".
016 was dropped 2026-09-23, so there is no observer instance to place and
that decision is moot.)

**Once enabled — read/write mix sweep.** With the two bridges independent,
sweep the direction mix from 100% write / 0% read to 0% write / 100% read in
**5% increments** (21 points). This is the measurement the split exists for:
read/write turnaround (tWTR, tRTW, bus turnaround) is paid at the DRAM and is
invisible to any single-direction test, so the interesting shape is the middle
of the curve, not the endpoints. A single shared path cannot produce it
because direction ratio and offered load are not separable there.

Hold everything else fixed across the sweep — same total offered load, same
address pattern, same page policy — so the only moving variable is the mix.
Every burst stays a whole DFI BL8 transaction (a sub-burst is illegal in the
generators; see `_check_full_burst`), otherwise the mix curve is confounded
by partial-burst overhead.

Endpoints are the sanity check: 100/0 and 0/100 should reproduce the existing
single-direction numbers. A dip that is deeper than turnaround alone explains
points at scheduler behaviour rather than at the device.
