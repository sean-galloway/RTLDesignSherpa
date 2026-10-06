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

# What the K-maps Prove

## Methodology

The kmap workbook ([`gen_amber_contracts_kmaps.py`](../../gen_amber_contracts_kmaps.py)) applies the STREAM-derived methodology:

1. Identify every important combinational decision signal.
2. List axes as `(name, expression, cite)` triples.
3. State `depends_only_on` evidence that justifies the axis list.
4. Add checked `relations` that mark unreachable input combos as don't-cares.
5. Derive the minimal SOP mechanically with Quine-McCluskey.
6. Diff the derived cover against the RTL SOP when RTL exists.

Because amber has no RTL yet, the workbook is a **pre-RTL contract**. The derived SOP is the logic the future RTL must implement. `rtl_sop` is intentionally absent in the workbook; when RTL lands the diff step produces one of three verdicts.

## The Three Verdicts

The verdict logic is implemented in `bin/kmaps/minimize.py`:

| Verdict | Meaning | Action |
|---------|---------|--------|
| **IDENTICAL** | The RTL SOP matches the derived minimal cover. | No change needed; the RTL is already minimal. |
| **RTL-REDUNDANT** | The RTL SOP includes extra literals or terms but produces the same truth table. | Document why the redundancy exists (timing, readability, defensive coding). |
| **RTL-DIFFERS** | The RTL SOP produces a different truth table than the derived cover. | Investigate: bug, unstated invariant, or missing relation. |

## Pre-RTL Status

Until RTL exists, every kmap sheet ends with `VERDICT: NOT CHECKED — supply rtl_sop= to diff the RTL against the derived cover`. This is honest. The value of the workbook now is to make the intended logic explicit and mechanically derivable before any RTL is written.

---

**Last Updated:** 2026-10-06
