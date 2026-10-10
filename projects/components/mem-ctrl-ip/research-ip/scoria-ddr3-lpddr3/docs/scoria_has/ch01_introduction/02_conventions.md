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
| INHERITED | green | pumice's block, used as-is; its verification evidence transfers |
| MODIFIED | amber | a bounded change with a cited cause |
| NEW | red | no pumice counterpart |

: Table 1.1: Block markings

## Signal and parameter naming

Inherited from the pumice design requirements and not restated here: module
naming, `UPPER_CASE` parameters, `r_`/`w_` internal prefixes, and the per-area
clock and reset names. Two points bear repeating because they are load-bearing:

- **Clock and reset names are per area.** In the component tree the controller
  uses `aclk`/`aresetn`. An `.i_rst_n(...)` connection against an `rtl/common`
  module will not elaborate, because those use `clk`/`rst_n`.
- **No assertions in the RTL.** Properties live in external `formal/` blocks.
  This is a tool-compatibility rule, not a style preference.

## Timing values

**Every enforced timing is a runtime CSR, not a parameter.** This is inherited
from pumice and was learned there: a timing compiled in cannot be swept, and a
controller whose timings cannot be swept cannot be characterized.

Where this document states a numeric timing it is cited to a clause, and the
unit is given. `nCK` means DRAM clock cycles. Values that vary by speed bin are
named but not tabulated here — they belong to the CSR derivation.

**Note:** JESD79-3F states some minimums without a maximum, most notably
`tWLMRD`, whose maximum it declares controller-dependent. Where the spec
declines to bound something, this document says so rather than inventing a
bound.

## Citations

A claim traceable to a standard is cited as JESD79-3F (DDR3), JESD209-3C
(LPDDR3), or DFI v3.1 with a section number. Those PDFs are **not in the
repository** and must not be added to it — they are not redistributable. They
live in the operator's cold storage; `dfi-specs/ddr3/index.md` records where and
why.

A claim inherited from pumice cites the pumice HAS or its design requirements,
both of which are in the repository.
