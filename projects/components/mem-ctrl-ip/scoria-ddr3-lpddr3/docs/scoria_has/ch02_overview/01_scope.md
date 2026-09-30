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

## What scoria is

A memory controller presenting an AXI4 slave to the host and a DFI v3.1 master
to the PHY, supporting DDR3 SDRAM and LPDDR3 SDRAM from one parameterized
design.

## Goals

1. **Reuse the pumice architecture, and its evidence with it.** The front end,
   scheduler, timing enforcement and data paths are inherited. Reuse here is
   not laziness; those blocks carry board measurements and formal proofs that a
   rewrite would discard.
2. **Change only what the standards force.** Four blocks change and two are
   new. Chapter 3 is that list, and it is short on purpose.
3. **Keep the DFI boundary clean.** No PHY responsibilities migrate into the
   controller — including the write-leveling *search*, which DDR3 makes
   tempting and decision D2 rules out.
4. **Every enforced timing a runtime CSR.** Inherited from pumice, and the
   precondition for characterization.
5. **Verifiable before hardware.** The DFI bus functional model is the target,
   so the controller can be wrong in simulation where it is cheap.

## Non-goals

**Performance parity with a vendor controller at DDR3 speeds.** scoria's design
point is architectural clarity and measurability. pumice reaches roughly 95% of
theoretical peak in both directions on its board, and the same structure should
carry, but no throughput target is set in this edition.

**The DDR4 feature set.** DFI v3.1 carries it; scoria does not implement it.

**Multi-rank beyond pumice's parameterization.** `NUM_RANKS` is inherited. As
with pumice, the practical limit is the board, not the controller.

## What makes DDR3/LPDDR3 easier than it looks

Three things reduce the work substantially, and it is worth stating them so the
project is not over-scoped:

- **LPDDR3 is not a protocol break.** JESD209-3C keeps the 10-bit
  double-data-rate CA bus that LPDDR2 uses, so the LPDDR3 side is timings and
  mode registers rather than a new command encoding.
- **pumice was written expecting this.** Its row field is already padded to
  18 bits with the comment "DDR3 forward-compat", and `memtype_e` is an enum
  rather than a boolean — though a one-bit one, which is why decision D3 gives
  scoria its own package.
- **DFI v3.1 does not disturb the datapath.** Its multi-phase signalling
  generalises pumice's explicit `_p0..p3` to `_pN`, and the 1:4 frequency ratio
  is still defined. `DFI_RATE = 4` carries over untouched.

## What is genuinely harder

- **Write leveling.** New to this family member, and it spans the controller,
  the DRAM's MR1 and the PHY. The interface is specified here; the search is not.
- **ZQ calibration as maintenance traffic.** Periodic `ZQCS` has to be
  interleaved with demand traffic, which makes it a scheduling problem.
- **A four-register mode-register set.** MR0-MR3 replaces MR0-MR2 plus EMRS3,
  and the programming order is JEDEC's. pumice learned that the hard way: its
  init order was corrected to JEDEC's after an EMRS3-first sequence, which was
  benign but wrong.
