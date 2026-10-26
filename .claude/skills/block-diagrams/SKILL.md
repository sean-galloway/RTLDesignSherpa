---
name: block-diagrams
description: The binding house style for every block / microarchitecture diagram - graphviz dot, one column per flow, labeled arrows, one boundary bar, the element key (shape and fill name the class), and the render-then-read check. Use before drawing or changing ANY block diagram in a HAS/MAS, a docs/markdown module page, a README or a vault note.
---

# block-diagrams

READ FIRST: vault/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: vault/handbook/authoring/block-diagrams.md - rules in priority
order, the element key, layout recipes, the per-shape rulings and the failures behind them.

The rules that get violated most:
- **Copy the reference, do not retype it:**
  `vault/handbook/authoring/assets/block-diagrams/axi_plane.dot`.
- **Shape and fill name the class.** Interface rounded green, logic white,
  Registered double border blue, FSM diagonals peach, Storage cylinder
  lavender, pick trapezium gold, optional dashed. Classify from the RTL.
- **A FIFO or skid child instance is a Storage cylinder** (owner, 2026-10-25),
  whatever its output timing; the block whose outputs leave through it is
  Registered. See "Child instances" in the note.
- **The key is GENERATED.** Render with `bin/render_block_diagram.py X.dot`
  (or the directory's `regenerate_all_graphviz.sh`), never a hand-drawn
  `cluster_key`.
- **Render, then read the PNG** at full resolution: no text on a line, every
  flow traceable, every arrow labeled with what it carries.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE ([[block-diagrams]]), not to this skill.
