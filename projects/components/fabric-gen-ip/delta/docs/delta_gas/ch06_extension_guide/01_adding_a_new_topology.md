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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Adding a New Topology

To add a new topology beyond `flat`:

1. Add a new class in `delta_generator.py` (e.g., `DeltaTreeCrossbar`).
2. Derive it from `Module` or reuse `DeltaFlatCrossbar` as a building block.
3. Add the topology name to the `--topology` choices.
4. In `main()`, instantiate the new class when the selected topology matches.
5. Add a DV test that exercises the new topology.
6. Regenerate fixtures and run the full DV suite.

## Tree topology notes

The existing `DeltaSplitter1to2` and `complete_tree_generator.py` provide the building blocks. A full tree crossbar would recursively instantiate splitters and mergers to build a multi-stage network. Because tree routing uses bit slices of `TDEST`, ensure `DEST_WIDTH` is at least as large as the tree depth.
