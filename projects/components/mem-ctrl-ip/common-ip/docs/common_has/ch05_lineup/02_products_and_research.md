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

# Products and Research: granite / gabbro / diorite

The family runs two lines off one common core (Ch 1). This chapter names the
product line and states what a product is allowed to leave out — the
"realistic version" of each memory controller, as distinct from the research
controllers that prove the generations out.

## The product names

| Product | Generation | Memory | DFI plane |
|---|---|---|---|
| **granite** | v2 | DDR2 / LPDDR2 | `mc_dfi_2p1_plane` |
| **gabbro** | v3 | DDR3 / LPDDR3 | `mc_dfi_3p1_plane` |
| **diorite** | v4 | DDR4 / LPDDR4 | `mc_dfi_4p0_plane` |

The naming is igneous, ordered, and owned here: future generations extend the
list (basalt is reserved informally for the v5/DDR5 generation per the
memtype encoding's 2'b11 code). A product is a configuration of the common
stack — planes selected, knobs set, rock children chosen — not a new RTL
tree.

## What a product may leave out — and what it may not

The v2 generation needs no bank groups, no FGR, no DBI, no CA parity. A
granite build correspondingly runs:

- **Storage plane in its lite configuration.** "Off" is not literal: the
  scheduler's pick machinery argmaxes over schedulable-entry vectors, and
  something must hold those entries. Lite means the stripped AXI-plane
  configuration serving N=1, in-order — the seam vectors with one entry
  behind them (Ch 2.2). The entry store can shrink toward one; it cannot
  reach zero.
- **RAS plane absent.** Unlike storage, this is a true bypass: no transform
  pair instantiated, no CSR surface beyond the reserved decode, scrub
  absent. Doctrine 9 governs what may later appear here.
- **The write-data buffer at its minimum.** It cannot reach zero — write
  data must be staged somewhere between the seam and the serializer — but a
  product sets it by the SKU's burst profile, not by the research
  characterisation harness's sweep needs.

What a product may **never** leave out: the entry store, the write-data
staging, the aclk↔dfi_clk CDC, and the maintenance request/grant path
(doctrine 2 — a product that cannot refresh correctly is not a smaller
product, it is a broken one).

granite is therefore the **bypass-validation testbed**: the cheapest full
proof that the common core runs correctly with its optional planes at
minimum and absent, before gabbro/diorite spend area on features the v2
generation will never see.

## The research line's role

pumice, scoria, andesite keep their jobs: generations land there first,
measured numbers come from there, and a feature's second customer comes from
there. The product line consumes the proven stack; it does not pioneer on
it. When a product needs a feature the research line has not proven (a
product-specific ODT profile, an industrial temperature derate), the feature
lands in the research line first, by doctrine 11's logic even when the
product is the only paying customer — because the research harnesses are
where a number can be produced to explain it.

## Relationship to the rocks' books

The rock HAS/MAS books record each research controller as it stands, with
deltas against the architecture of this book marked INHERITED / MODIFIED /
NEW. A product book, when the first product is built, is a short document:
this book, the chosen configuration, and the product's own board
integration. Nothing more — a product whose book is long is a product whose
configuration is not yet decided.
