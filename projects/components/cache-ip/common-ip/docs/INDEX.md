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

# cache-ip/common-ip — documentation index

The shared MESI L1 core that [amber](../../amber-mesi-l1/) designed and
proved and [jet](../../jet-mesi-l1/) inherits: the `l1_*` FUBs, the
`l1_pkg` package, and the `l1_core` composition, plus their lowest-level
checkout ([`../dv/`](../dv/)).

## Pages

- [**The shared core contract**](l1_shared_core.md) — what the `l1_*`
  blocks are, the parameters and encodings in `l1_pkg`, the per-FUB
  contracts, the cross-cutting rules (reset/init walk, response staging,
  pending-fill and pending-effect semantics, victim/drain contract), and
  where the golden model, DV, and formal evidence live.

## The books with the full narrative

The narrative design history stays with the IPs that did the designing:

- [amber HAS](../../amber-mesi-l1/docs/amber_has/amber_has_index.md) /
  [amber MAS](../../amber-mesi-l1/docs/amber_mas/amber_mas_index.md) — the
  blocking core these FUBs were proven in (the snoop Table 3.0 decode, the
  D-decisions, the macro/top compositions).
- [jet HAS](../../jet-mesi-l1/docs/jet_has/jet_has_index.md) /
  [jet MAS](../../jet-mesi-l1/docs/jet_mas/jet_mas_index.md) — the
  lockup-free extension (MSHRs, hit-under-miss, response sequencing).
- [ACE interface definition](../../References/AMBA_ACE_Interface_Definition.md)
  — the family's snoop-port contract (the onyx D7 subset).
