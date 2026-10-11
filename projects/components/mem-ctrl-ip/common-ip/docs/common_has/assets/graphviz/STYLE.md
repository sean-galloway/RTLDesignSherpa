# Diagram house style — memory-controller uarch diagrams

Every overall-uarch and per-layer diagram in the mem-ctrl-ip books follows
the same visual language, fixed by the reference the owner chose
(`design-a-ddr-memory-controller-i-top-level-diagram.webp`): the classic
DDR-MC course diagram — white canvas, light-blue functional blocks, a
tapered scheduler, a full-width PHY bar, and elbowed black arrows.

## Recipe (graphviz `dot`)

```dot
graph [rankdir=TB, bgcolor="white", fontname="Helvetica", fontsize=11,
       nodesep="0.35", ranksep="0.60", splines=ortho];
node  [fontname="Helvetica", fontsize="10", shape=box, style=filled,
       fillcolor="#D6E4F0", color="black", margin="0.12,0.06"];
edge  [fontname="Helvetica", fontsize=9, color="black", arrowsize=0.7];
```

## Vocabulary — what each shape means

| Element | Graphviz | Meaning |
|---|---|---|
| Functional block | `shape=box`, `fillcolor="#D6E4F0"` | RTL logic (a FUB or a group of FUBs) |
| External interface | `shape=box`, `fillcolor="white"` | Host channels, APB, the PHY — things outside the controller |
| The scheduler | `shape=invtrapezium`, wide | the pick — always drawn as the tapered shape, always central |
| Timing control | `shape=box`, blue, beside the scheduler | bank/global timers feeding the pick |
| PHY | wide white bar, `rank=sink` | the DFI boundary at the bottom |
| Optional/absent block | `style="filled,dashed"` | a layer a given build may omit (e.g. RAS) |

## Rules

1. Command flow runs top to bottom; the PHY bar is the last rank.
2. Arrow labels name the transaction class (WR / RD / RMW / ACT / REF /
   "DDR Command" / "Write to DDR" / "Read from DDR"), not signal names.
3. Every block label carries the reference-style name on line 1 and the
   owning RTL (`module — FUB`) on the following lines.
4. No clusters, no colors beyond the blue/white vocabulary above (the
   inherited/modified/new coloring is scoria-book specific; family diagrams
   don't use it).
5. Render with `regenerate_all_graphviz.sh` (PNG at 150 dpi, PNG8
   palette-encoded); markdown references the `.png`, never the `.mmd`/`.dot`.
6. `splines=ortho` everywhere; use invisible edges (`style=invis`) to pin
   ranks when the layout fights the reference shape.
