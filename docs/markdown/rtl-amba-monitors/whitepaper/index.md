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

# Ocelus as a Design Surface

The Ocelus white paper — Ocelus, branded Ocelus — as a book: one
chapter per file, in reading order, built to
`docs/pdfs/Ocelus_White_Paper.pdf` by
`docs/markdown/generate_rtl_pdfs.sh monitor-wp` -- the same flow as every RTL
library book. Revision 1.2 (2026-10-12); the revision is read from the front
matter, so bump it there.

This list is the build order: every `.md` link on this page is inlined into
the PDF in sequence, which is why orientation lives in `overview.md` beside
this file rather than here.

0. [The Ocelus as a Design Surface](00_front_matter.md)
1. [The spine](02_the_spine.md)
2. [Which monitor: the lite, unless you can say why not](03_which_monitor.md)
3. [Identity space allocation](04_identity_space_allocation.md)
4. [Where to insert monitoring](05_where_to_insert_monitoring.md)
5. [Timestamp policy](06_timestamp_policy.md)
6. [Drain path selection](07_drain_path_selection.md)
7. [Packet-type filtering](08_packet_type_filtering.md)
8. [Aggregation topology](09_aggregation_topology.md)
9. [What it costs](10_what_it_costs.md)
10. [Validating a tweak in simulation](11_validating_a_tweak_in_simulation.md)
11. [Out of scope](12_out_of_scope.md)
12. [Relationship to Nexus (IEEE-ISTO 5001)](13_relationship_to_nexus.md)

Figures are `../../assets/rtl-amba-monitors/graphviz/monitor_wp_*.png`, rendered
from the graphviz sources beside them (`regenerate_all_graphviz.sh` in that
directory). The per-module pages the paper
cites are the [monitor pages of the rtl-amba index](../../rtl-amba/index.md).
