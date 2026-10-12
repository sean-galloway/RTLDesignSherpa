# Diagram house style — memory-controller uarch diagrams

Every overall-uarch and per-layer diagram in the mem-ctrl-ip books follows
this style, fixed by the reference the owner chose
(`design-a-ddr-memory-controller-i-top-level-diagram.webp`): the classic
DDR-MC course diagram.

**What the owner values in the reference is not the palette — it is how
clearly the data and command flows read.** Color is a don't-care; flow
clarity is the contract. The rules below are ordered by that priority.

## Prime directive: the three flows must be traceable at a glance

A reader who knows nothing about the block must be able to answer, from
the drawing alone:

1. *Where does a command come from, and how does it reach the DRAM?*
2. *Where does write data enter, and by what route does it leave?*
3. *Where does read data come back, and how does it get home?*

### The three flows and their geography

| Flow | Direction | Geography |
|---|---|---|
| **Command** | strictly top-down | the center column: channels → packetizers/intakes → pools → arbitration → scheduler → PHY. Commands never share an arrow with data. |
| **Write data** | top-down, own route | enters with the write channel, leaves through its own path to the PHY (in the reference: down the left side, via the merge/forward buffers and write data path control) |
| **Read data** | **back up**, own route | returns from the PHY on a separate route (in the reference: up the right side, through read data path control, merge logic, reorder buffer, home to the AXI read channel). The spatial loop — down the middle, up the side — is the point. |

On per-layer diagrams the same discipline applies at layer scale: request
traffic enters at the top, leaves at the bottom; returned/response traffic
re-enters at the bottom and leaves at the top or side on its own route.

## Rules that make the flows read (in priority order)

1. **One column per flow; flows never share an arrow.** If an arrow
   carries both a command and its data, the diagram is wrong — split it.
2. **Top-down is request direction; return data goes back up on its own
   route.** Never route returned data downward alongside requests.
3. **Right angles only** (`splines=ortho`); parallel flows may share trunk
   routes; crossings are minimized and always at right angles.
4. **Arrow labels name the transaction class at decision points and at
   every boundary crossing** — WR / RMW / RD / REF going in; "Write to
   DDR" / "Read from DDR" / "DDR Command" at the PHY. Never bare signal
   names. A label answers "what is this arrow carrying?" not "what is this
   wire called?".
5. **One boundary bar per diagram** — the PHY at whole-unit scale, the
   layer edge at layer scale. Everything leaving the drawn unit crosses the
   bar at a labeled point; nothing crosses silently.
6. **Blocks sit ON their flow, in flow order through the ranks.** A block
   with no arrow on its flow does not belong in the diagram. Pools and
   buffers straddle the flow they hold. Edges between blocks in the SAME
   rank are horizontal spaghetti — if a flow needs a sideways hop, re-rank
   the blocks instead. Mirror the reference's rank geography: side buffers
   (merge/forward) sit one rank below their pool at the flow's edge; the
   return path climbs back up at the diagram's edge, never through the
   center; a sideband block (e.g. configuration registers) may sit with no
   edge at all, its role stated in the label.
7. **Sideband and feedback** (grants, credits, snoop probes, ring tickets,
   config) is drawn dashed, kept short, and labeled — visible, but never
   mistakable for a main flow.
8. **Optional / shell-only blocks are dashed** and sit off the main flows,
   so "not in this build" reads instantly.
9. **The scheduler is always the tapered trapezium (wide edge up — the
   many prospects arrive on the wide edge, the one command leaves the
   narrow edge),** always central, always on the command flow. This one
   shape is the family's signature; do not use it for anything else. In
   graphviz this is `shape=invtrapezium`: graphviz's plain `trapezium` is
   narrow-edge-up and renders as an upside-down mux. Draw it flat and wide
   (the reference's shallow sliver), not tall — set `width` generously and
   keep the label short. **Every arrow that enters the trapezium carries a
   transaction-class label** (`WR / RMW`, `RD`, `REF / ZQ`, `timer window`)
   — an unlabeled arrow into the funnel reads as a mux select line, and a
   fan of selects with no visible exit is exactly the "mux with nothing
   coming out" failure. **The command output leaves the narrow edge with a
   heavier pen** (`penwidth=1.8`) and its label (`DDR Command`) so the
   funnel's exit reads at a glance. Same-rank (horizontal) edge labels
   need `xlabel`, not `label` — a plain label is drawn at the edge
   midpoint and gets overdrawn by the node fill (the "timer window" arrow
   into the trapezium was the example).

## Labels

Every block label: reference-style name on line 1, owning RTL
(`module — FUB`) below it. Every label answers "what does it do?" before
"what is it called?".

## Palette — discretionary

The default vocabulary is white external-interface boxes and `#D6E4F0`
functional blocks on a white canvas, but **color never carries meaning**.
Meaning lives in geometry (flow routes, the trapezium, the bar) and in
labels. Swapping the palette must never change what the diagram says; a
black-and-white photocopy must still pass every rule above.

## Rendering

- graphviz `dot`, `rankdir=TB`, `splines=ortho`, Helvetica, `bgcolor=white`:

```dot
graph [rankdir=TB, bgcolor="white", fontname="Helvetica", fontsize=11,
       nodesep="0.35", ranksep="0.60", splines=ortho];
node  [fontname="Helvetica", fontsize=10, shape=box, style=filled,
       fillcolor="#D6E4F0", color="black", margin="0.12,0.06"];
edge  [fontname="Helvetica", fontsize=9, color="black", arrowsize=0.7];
```

- Render with `regenerate_all_graphviz.sh` (PNG at 150 dpi, PNG8
  palette-encoded); markdown references the `.png`.
- Pin ranks with `{ rank=same; ... }` and order within a rank with
  invisible edges when the layout fights the flow geography. Downward
  return-flow edges use `dir=back` so the arrowhead still points the way
  the data goes while the rank direction stays top-down.
- Do not draw two parallel edges between the same node pair to carry two
  transaction classes — dot assigns their channels in an order you cannot
  control and `splines=ortho` ignores edge labels when routing, so the
  labels drift and mislead. Use one edge with a combined label
  (`WR / RMW`). Same for taillabel/headlabel tricks: if a label does not
  land exactly where you want it, change the edge structure, not the label.
- After rendering, **read the PNG** and trace the three flows by rule 1–5
  before committing. If you can't trace a flow with a finger, the layout
  is wrong — fix the ranks, not the colors.
