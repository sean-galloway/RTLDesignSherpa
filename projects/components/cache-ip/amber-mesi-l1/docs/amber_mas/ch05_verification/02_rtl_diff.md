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

# RTL Landing Diff Procedure

## When RTL Lands

After the first RTL commit for a module, update the corresponding sheet in [`gen_amber_contracts_kmaps.py`](../../gen_amber_contracts_kmaps.py):

1. Add citations to the RTL file and line numbers in the `CITES` registry.
2. Replace `rtl_sop=None` with the actual RTL expression as a sum-of-products string.
3. Re-run the generator.
4. Review each sheet's verdict.

First landing (2026-10-06): the snoop CRRESP / next-state decode exists as
`amber_pkg` functions + `amber_snoop_kmap`. See
[01_kmap_verdicts.md](01_kmap_verdicts.md) for why its sheets record
truth-table PASS but a deferred SOP-literal diff; the procedure above applies
to every sheet still at `rtl_sop=None`.

## Diff Checklist

For every sheet that reports **RTL-DIFFERS**:

- Is the difference a deliberate redundancy? Re-label as RTL-REDUNDANT and add a note.
- Is an unstated invariant doing work? Add it as a checked `relation` and re-derive.
- Is the RTL expression wrong? File a bug and fix it.

For every sheet that reports **RTL-REDUNDANT**:

- Does the redundancy serve timing closure? Keep it and document.
- Does the redundancy serve readability? Keep it if the cost is small.
- Is it accidental? Simplify the RTL.

## Regression Rule

The generator is part of the CI check for amber. Any RTL edit that moves or changes a cited expression must cause the generator to fail loudly, not silently publish a stale map. This is enforced by the `CITES` registry in `gen_amber_contracts_kmaps.py`.

---

**Last Updated:** 2026-10-06
