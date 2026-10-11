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

# Purpose, Scope, and the Two Lines

## Purpose

This book is the architecture contract for the mem-ctrl-ip family. It exists
so that a person can answer, from one document:

1. What the layers are, what each one owns, and how they fit together.
2. What the interface between the layers is — the seam — and which properties
   of it are invariant.
3. Which rules (doctrines) every block and every rock follows without
   re-litigating them.
4. What "productizing" a research controller means in this family, and which
   block serves which product.

The book deliberately does **not** contain: per-block microarchitecture
(that is [common_mas](../../common_mas/common_mas_index.md)), register maps
(rock books), JEDEC or DFI clause-level detail
([04_jedec_generation_deltas.md](../../04_jedec_generation_deltas.md), the
simplified-spec books), or verification plans (rock books). A book that
answers every question answers none; the ownership rule keeps each question
at one address.

## The premise: one common core, many controllers

Three research controllers exist — pumice (DDR2/LPDDR2), scoria
(DDR3/LPDDR3), andesite (DDR4/LPDDR4) — and for a long time each carried its
own copy of the same logic: the AXI intakes, the CAMs, the timers, the
arbiter, the DFI pipeline. The Phase-2 campaign (2026-10-09 → 2026-10-10)
extracted what had two live customers into common-ip: one package
(`mc_common_pkg`), eight layers, seventeen FUBs. The premise of this book is
that the extraction is not a code-dedup exercise — it is an architecture.
The blocks in common-ip are the family; the rocks are instantiations.

The test for what moves to common-ip is the **two-customer rule** (from the
common-ip README, predating the campaign): a block moves here only when it
has two live customers at extraction time. Speculative one-customer
abstractions stay in the research controllers. This rule is why common-ip
contains what it contains and — just as important — why the rocks still own
their init sequencers, mode registers, refresh controllers, and page-policy
engines: those blocks are generation-specific today, and a common core with
one customer would be a guess.

## The two lines: research and product

The family runs two lines off the same common core:

- **Research** — pumice, scoria, andesite. Full-featured controllers that
  prove out generations, run the characterisation harnesses, and close
  timing on real boards. They are where features land first and where
  measured numbers come from.
- **Product** — granite (v2: DDR2/LPDDR2), gabbro (v3: DDR3), diorite (v4:
  DDR4/LPDDR4). Realistic, area-conscious SKUs built from the same layers.
  Product naming and the product line's reason to exist are Chapter 5.2.

granite doubles as the **bypass-validation testbed**: because the v2
generation needs no storage-layer reordering and no RAS features, a granite
build with the storage layer in its lite configuration and the RAS layer
bypassed is the cheapest full proof that the common core works without its
optional layers (Ch 5.2).

## What this book binds

- The layer stack and the name and role of every layer (Ch 2).
- The descriptor seam and its invariants (Ch 2.2).
- The DFI layer naming — `dfi_2p1_layer`, `dfi_3p1_layer`, `dfi_4p0_layer`
  (Ch 3).
- Doctrines added by the campaign (Ch 4). The original five doctrines in
  [02_family_doctrine.md](../../02_family_doctrine.md) remain in force; this
  book never restates them, it adds to them.
- The common-ip layout and the product/research line-up (Ch 5).

## Conventions

The family's conventions are inherited, not invented here: markings are
relative and match everywhere (INHERITED / MODIFIED / NEW); the evidentiary
rule (inherited, cited, or open question — nothing else); registers are
named, not offset-numbered; bandwidth figures carry the theoretical maximum
beside them. Where this book needs a new convention it says so at the point
of use.
