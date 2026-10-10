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

# Document Conventions

## Block marking

Every block carries exactly one marking, and the block diagram colours match:

| Marking | Colour in Figure 2.1 | Meaning |
|---|---|---|
| INHERITED | green | scoria's block, used as-is; its verification evidence transfers |
| MODIFIED | amber | a bounded change with a cited cause |
| NEW | red | no scoria counterpart |

: Table 1.1: Block markings

The marking is a property of the block, not of the chapter it appears in: the
Chapter 2 table, the Chapter 3 prose, the Figure 2.1 colours, and the MAS
inventory all carry the same marking for the same block, and a drift between
those surfaces is a defect in this document.

## What this book does not restate

The family docs at `../../../../docs/` own the shared-core design and the
family doctrine — the `mem_ctrl_pkg` design, the config-not-param rule, the
maintenance request/grant discipline, the AXI4 host-side shape, and the
evidentiary rule itself. This book references them and follows them; it does
not restate them. Where this book and a family doc disagree, the family doc
wins and this book is the defect.

## Signal and parameter naming

Inherited from the scoria design requirements and not restated here: module
naming, `UPPER_CASE` parameters, `r_`/`w_` internal prefixes, and the
per-area clock and reset names. Two points bear repeating because they are
load-bearing:

- **Clock and reset names are per area.** In the component tree the controller
  uses `aclk`/`aresetn`. An `.i_rst_n(...)` connection against an `rtl/common`
  module will not elaborate, because those use `clk`/`rst_n`.
- **No assertions in the RTL.** Properties live in external `formal/` blocks.
  This is a tool-compatibility rule, not a style preference.

## Timing values

**Every enforced timing is a runtime CSR, not a parameter.** This is inherited
from pumice through scoria and was learned there: a timing compiled in cannot
be swept, and a controller whose timings cannot be swept cannot be
characterized. andesite keeps it absolutely — geometry alone is build-time
(Chapter 2.4).

Where this document states a numeric timing it is cited to a clause, and the
unit is given. `nCK` means DRAM clock cycles. Values that vary by speed bin
are named but not tabulated here — they belong to the CSR derivation.

## Citations

A claim traceable to a standard is cited as JESD79-4 (DDR4), JESD209-4
(LPDDR4), or DFI v4.0 with a section number. Those PDFs are **not in the
repository** and must not be added to it — they are not redistributable, and
the DFI 4.0 spec is additionally not on disk at all. Until andesite TASK-005
acquires and studies it, every DFI 4.0 clause citation is suffixed
`§TBC(TASK-005)`; the suffix is a promise to confirm, not a reference.

A claim inherited from scoria cites the scoria HAS or its design requirements,
both of which are in the repository. A claim about the shared core or the
family doctrine cites the family docs.
