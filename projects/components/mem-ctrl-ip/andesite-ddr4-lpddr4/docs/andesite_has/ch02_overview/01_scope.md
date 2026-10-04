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

# Scope and Goals

## What andesite is

A memory controller presenting an AXI4 slave to the host and a DFI v4.0 master
to the PHY, supporting DDR4 SDRAM and LPDDR4 SDRAM from one parameterized
design. It is the third member of a family: pumice covers DDR2/LPDDR2 and is
built, measured and running on hardware; scoria covers DDR3/LPDDR3 with RTL
verified in simulation (221 tests, 9 formal blocks at last measure). andesite
inherits from scoria the same way scoria inherited from pumice.

## Goals

1. **Reuse the scoria architecture, and its evidence with it.** The front end,
   scheduler, timing enforcement and data paths are inherited. Reuse here is
   not laziness; those blocks carry simulation verification and formal proofs
   that a rewrite would discard.
2. **Change only what the standards force.** Ten areas change, and the
   modified set is a dozen blocks, not a rewrite. Chapter 3 is that list, and
   it is short on purpose.
3. **Keep the DFI boundary clean.** No PHY responsibilities migrate into the
   controller — including every training *search*, which DDR4 and LPDDR4 make
   tempting and decision D2's precedent rules out.
4. **Every enforced timing a runtime CSR.** Geometry alone is build-time
   (Chapter 2.4); everything that varies — including the long/short timing
   pairs that DDR4's bank-group structure introduces — is a runtime register.
   Inherited from the family doctrine, and the precondition for
   characterization.
5. **Verifiable before hardware.** The target is a DFI v4.0 bus functional
   model in simulation. No board is named, because the 7-series targets this
   repo's boards carry do not support DDR4; naming one would promise what
   this generation can't keep.

## Non-goals

**Performance parity with a vendor controller at DDR4 speeds.** andesite's
design point is architectural clarity and measurability, the same posture
scoria took. No throughput target is set in this edition.

**The DDR5 surface of DFI v4.x.** The 4.x revision family carries DDR5
features andesite has no use for. They are named in Chapter 4 so their absence
is a decision on the record, then left unimplemented, as scoria left v3.1's
DDR4 surface.

**Write CRC.** DDR4 defines it; this edition excludes it with a named
unblock condition (Chapter 3.5). It is a datapath addition, not an
architecture change.

**LPDDR4 DVFS and deep-sleep states.** Named and deferred with the condition
recorded in Chapter 6.

**Multi-rank beyond scoria's parameterization.** `NUM_RANKS` is inherited;
the practical limit is the board, not the controller.

## What makes DDR4/LPDDR4 easier than it looks

Three things reduce the work, and stating them keeps the project from being
over-scoped:

- **LPDDR4 is not a protocol break from LPDDR3.** It stays a per-bank-refresh,
  CA-bus family; the deltas are the 6-bit DDR CA bus, MPC, and training — not
  a new command philosophy. scoria already handles per-bank refresh for
  LPDDR3; LPDDR4 makes that the commodity default.
- **scoria was written expecting this.** Its package note names the shared
  `mem_ctrl_pkg` migration as the DDR4/LPDDR4 controller's job (family doc
  01), and its refresh policy base (elastic refresh, TCR, ZQCS placement —
  scoria TASK-001's landed Modes A/B/C) is exactly what FGR wants to sit on.
- **Bank groups are a scheduling change, not a datapath change.** They add a
  decode dimension and long/short timing pairs; the data paths don't care.

## What is genuinely harder

- **Bank-group scheduling.** tCCD_L/S and tRRD_L/S make the arbiter and the
  global timers aware of which bank group a command targets — the one
  structural change DDR4 forces on the scheduler.
- **Dynamic ODT.** RTT_NOM/WR/PARK and the ODT latencies are new machinery
  with a new block (`odt_ctrl`), and scoria's static handling is insufficient.
- **Read leveling and LPDDR4 CA training.** New interfaces spanning
  controller, DRAM mode registers and PHY — the write-leveling lesson a
  generation later.
- **The init sequence.** Reset procedure, MR0-MR6, gear-down entry and parity
  enable in one ordered sequence; pumice's init-order correction (an
  EMRS3-first sequence, benign but wrong) is the precedent for treating the
  order as JEDEC's, not ours.
