# RTLDesignSherpa — standing agent instructions

## Block diagrams: house style is BINDING (highest priority for all doc/diagram work)

Every block / microarchitecture diagram in this repo — HAS/MAS books,
README figures, vault notes, fpga docs, anything — MUST follow the diagram
house style, fixed by the owner's reference (the classic DDR-MC course
diagram), and is drawn in graphviz `dot`. The canonical rules live in the
handbook:

`vault/handbook/authoring/block-diagrams.md`

The reference implementation is the family whole-unit diagram
(`common_has/assets/graphviz/01_whole_unit.png`) — mirror it.

Non-negotiables (rationale + recipes in the handbook note):

- **Three flows traceable at a glance**: command top-down the center;
  write data on its own route; read data back UP its own route (the
  spatial loop). Flows never share an arrow.
- **The scheduler is the flat wide-edge-up trapezium**
  (`shape=invtrapezium` — plain `trapezium` renders as an upside-down
  mux). Every arrow into it carries a transaction-class label (`WR / RMW`,
  `RD`, `REF / ZQ`, `timer window`); the command output leaves the narrow
  edge with a heavier pen (`penwidth=1.8`).
- **Every arrow labeled with what it carries.** Sideband/optional: dashed,
  short, labeled. Same-rank (horizontal) edge labels use `xlabel` — plain
  labels get overdrawn by node fills.
- **One boundary bar per diagram** (PHY at unit scale, layer edge at layer
  scale). No long same-rank edges. Never two parallel edges between one
  node pair for two classes (one edge, combined label). Never multiple
  mixed-direction crossings on one node pair — use the point-node scaffold
  pattern (handbook note).
- **Render, then READ THE RENDERED PNG AT FULL RESOLUTION and trace the
  three flows before committing.** Never commit an unseen diagram; if a
  flow cannot be traced with a finger, fix the ranks — not the colors.
