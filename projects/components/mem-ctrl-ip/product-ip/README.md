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

# Product Line — granite / gabbro / diorite

Realistic, area-conscious memory-controller SKUs configured from the
[`common-ip`](../common-ip/) stack — one product per JEDEC generation the
family covers. This directory is where a controller *graduates* from the
[`research-ip/`](../research-ip/) proving ground.

## What a product is

A product is a **configuration of the common stack** — layers selected,
knobs set, rock children chosen — **not a new RTL tree**
([common_has ch5.2](../common-ip/docs/common_has/ch05_lineup/02_products_and_research.md)).
The RTL a product builds with lives in `common-ip/rtl/`; what lives here is
the product's chosen configuration, its board bring-up, and (when built) a
short product book: the common architecture book + the chosen configuration
+ the product's own board.

## The products

| Product | Directory | Generation | Memory | DFI layer | Source rock (research-ip) | Role |
|---|---|---|---|---|---|---|
| **granite** | [`granite-ddr2-lpddr2/`](granite-ddr2-lpddr2/) | v2 | DDR2 / LPDDR2 | `mc_dfi_2p1_layer` | pumice (board-validated) | **Bypass-validation testbed** — cheapest full proof the common core runs with optional layers at minimum / absent; candidate first build |
| **gabbro** | [`gabbro-ddr3-lpddr3/`](gabbro-ddr3-lpddr3/) | v3 | DDR3 / LPDDR3 | `mc_dfi_3p1_layer` | scoria (sim-verified) | Mid line; consumes scoria's elastic-refresh convergence |
| **diorite** | [`diorite-ddr4-lpddr4/`](diorite-ddr4-lpddr4/) | v4 | DDR4 / LPDDR4 | `mc_dfi_4p0_layer` | andesite (planned) | Top line; carries the v4 command surface (bank groups, gear-down, CA parity, DBI) |

The naming is igneous, ordered, and owned by the common architecture book.
Note: the family README's research table also lists "gabbro" as an informal
future DDR6 *research* codename — that collision is known docs debt; the
compound directory names disambiguate (`product-ip/gabbro-ddr3-lpddr3/` vs a
future research rock), and the README will be reconciled.

## Rules (from common_has ch5.2)

What a product **may** leave out (granite / v2 shown — each generation's
list is in the product's own brief):

- Storage layer in its **lite configuration** — the stripped, N=1 in-order
  seam. "Off" is not literal: the entry store can shrink toward one entry,
  never to zero.
- **RAS layer absent** — a true bypass: no transform pair, no scrub.
- Write-data buffer at the **SKU minimum** (staging can shrink, never to
  zero).

What a product may **never** leave out: the entry store, write-data
staging, the aclk↔dfi_clk CDC, and the maintenance request/grant path — a
product that cannot refresh correctly is not a smaller product, it is a
broken one.

Products **consume proven research; they do not pioneer on the stack**. A
feature a product needs that research has not proven lands in the research
line first, because the research harnesses are where a measured number can
be produced to explain it.

## Layout

Each product directory holds:

- `README.md` — the product brief: generation scope, DFI layer, source
  rock, allowed omissions, board target, status.
- `config/product_config.md` — the chosen configuration: layer selection,
  parameters/knobs, CSR baseline, board. Filled when the product is built;
  the single source of truth for "what makes this SKU this SKU".

No `rtl/` tree is scaffolded here by design — see "what a product is"
above.

## Status

**Scaffold only (2026-10-11).** No product is built. First build
(granite, per the bypass-testbed role) is gated on: the source rock's
board-proven configuration, the common layers timing-closed at the
product's target frequency, and the product config filled in `granite-
ddr2-lpddr2/config/`.
