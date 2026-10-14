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

The mesh mode design spec (2026-10-13) is the current reference for adding a topology. The retired tree scaffolding is still in the repo, but it is not a regression baseline and should not be used as a model for new work.

Work through the design spec topics in this order, then land the generator changes:

1. **Topology semantics and routing concept** — read §2 (hierarchy), §5 (routing), and §7 (systolic and pattern support) of the [2026-10-13 mesh design spec](../../../../../../../docs/superpowers/specs/2026-10-13-delta-mesh-design.md). Define the coordinate space, escape/adaptive VC policy, and how standard modes switch.
2. **Generator CLI axis** — read §12. Choose the dimension parameters, optional torus dimensions, source-route and speculation flags, data/user widths, AMBA 5 carry-over, counters, and the FIFO implementation knob.
3. **Emitted artifacts** — read §2.1. Mesh mode emits one cell module (`delta_mesh_cell`) and a fabric top. Cell / tile / confluence / fabric are placement and documentation names, not wrapper RTL levels.
4. **Validation rules** — read §4 (flit format) and §12. Enforce dimension ranges, the torus-wrap minimum, and the `TUSER` width needed for the header fields (dest/src coords, QoS class, VC, multicast flag, misroute budget, source-route pointer, packet ID).
5. **DV suites** — read §13. Plan routing, QoS, multicast, deadlock soak, systolic, counter, DFT, and perf-model calibration suites.

After the design is settled, the generator mechanics are the same as any new mode:

- Add a class in `delta_generator.py` (e.g., `DeltaMeshCrossbar`) and derive it from `Module` or reuse existing building blocks.
- Add the topology name to the `--topology` choices.
- In `main()`, instantiate the new class when the selected topology matches.
- Add a DV test that exercises the new topology.
- Regenerate fixtures and run the full DV suite.

## Retired tree scaffolding

`DeltaSplitter1to2` and `complete_tree_generator.py` remain for reference. A tree crossbar would have recursively instantiated splitters and mergers using `TDEST` bit slices, but that path was retired on 2026-10-12.
