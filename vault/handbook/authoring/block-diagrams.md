---
title: Block diagrams
summary: The binding house style for every block / microarchitecture diagram - graphviz dot, flows traceable at a glance, labeled arrows, one boundary bar, render-then-read verification.
---

# Block diagrams

**Binding, highest priority, repo-wide** (owner ruling, 2026-10-11). Every
block or microarchitecture diagram follows this note: HAS/MAS books,
`docs/markdown` module pages, README figures, vault notes, FPGA system docs.
It supersedes the older "diagrams are Mermaid" rule in [[spec-doc-standards]].

**Status: v3 (element key 2026-10-19; reference example, return colour and key rulings the same day), being refined.** The rules came from the memory-controller
family and were proven there. Applying them to other block shapes (an
arbiter, a CDC block, a FIFO, a bridge, a DMA engine) is in progress with the
owner, one diagram at a time. When a diagram shows a rule needs restating for
a block shape, record the ruling here, under "Mapping to other block shapes",
with that diagram as its case.

## The reference

The owner chose the classic DDR memory-controller course diagram as the
reference. Its repo implementation is the family whole-unit diagram, and it
is the one to mirror:

- source: `projects/components/mem-ctrl-ip/common-ip/docs/common_has/assets/graphviz/01_whole_unit.dot`
- render: `.../common_has/assets/graphviz/01_whole_unit.png`

**The owner values how clearly the flows read.** Flow clarity is the
contract; the element key (below) makes each box's kind readable at a glance,
and the reference example under "Element key" shows all of it at once. The rules below are in
priority order.

## Prime directive: every flow is traceable at a glance

A reader who knows nothing about the block must be able to answer, from the
drawing alone, for each flow through it:

1. *Where does it enter?*
2. *What does it pass through, in order?*
3. *Where does it leave?*

At most block shapes the flows are the **request / command** flow, the
**forward data** flow (write data, payload), and the **return** flow (read
data, responses). For a memory controller those are command, write data and
read data:

| Flow | Direction | Geography |
|---|---|---|
| Request / command | strictly top-down | the center column, from the intakes to the boundary bar; never shares an arrow with data |
| Forward data | top-down, on its own route | enters with its channel and leaves by its own path (the reference uses the left side) |
| Return data | **back up**, on its own route | re-enters at the bar and climbs at the diagram's edge, never through the center (the reference uses the right side). The spatial loop, down the middle and up the side, is the point. |

If a diagram has fewer flows (a FIFO has one), the rules still apply to the
ones it has. A diagram at plane or sub-block scale follows the same
discipline: request traffic enters at the top and leaves at the bottom;
return traffic re-enters at the bottom and leaves at the top or side, on its
own route.

## The rules, in priority order

1. **One column per flow; flows never share an arrow.** If an arrow carries
   both a command and its data, the diagram is wrong. Split it.
2. **Top-down is the request direction; return data goes back up on its own
   route.** Never route returned data downward alongside requests.
3. **Right angles only** (`splines=ortho`). Parallel flows may share trunk
   routes. Keep crossings to a minimum, and always at right angles.
4. **Every arrow is labeled with what it carries.** At decision points and at
   every boundary crossing, the label names the transaction class (`WR`,
   `RD`, `INIT / MRS / REF`, `ZQ / MRR` going in; "Write to DDR", "Read from
   DDR", "DDR Command" at the PHY). Never use bare signal names. A label answers "what is this
   arrow carrying?", not "what is this wire called?".
5. **One boundary bar per diagram.** The bar is the PHY at whole-unit scale
   and the plane edge at plane scale. Everything leaving the drawn unit
   crosses the bar at a labeled point; nothing crosses silently.
6. **Blocks sit ON their flow, in flow order through the ranks.**
   - A block with no arrow on any flow does not belong in the diagram. The
     one exception is a sideband block (such as configuration registers),
     which may sit with no edge if its label states its role.
   - Pools and buffers straddle the flow they hold.
   - No edges between blocks in the same rank: they become horizontal
     spaghetti. If a flow needs a sideways hop, re-rank the blocks instead.
   - Side buffers sit one rank below their pool, at the flow's edge.
7. **Sideband and feedback are dashed, short and labeled.** This covers
   grants, credits, snoop probes, tickets and config. They stay visible but
   can never be mistaken for a main flow.
8. **Optional or build-dependent blocks are dashed** and sit off the main
   flows, so "not in this build" reads instantly.
9. **The many-to-one decision point is a flat trapezium, wide edge up.** The
   many contenders arrive on the wide edge and the one winner leaves the
   narrow edge. In a memory controller this is the scheduler; elsewhere it is
   the arbiter. The shape is reserved for that role, sits central, and sits
   on the request flow.
   - In graphviz use `shape=invtrapezium`. Plain `trapezium` is
     narrow-edge-up and renders as an upside-down mux.
   - Draw it flat and wide (a shallow sliver), not tall: set `width`
     generously and keep the label short.
   - **Every arrow into it carries a class label.** An unlabeled arrow into
     the funnel reads as a mux select line, and a fan of selects with no
     visible exit is the "mux with nothing coming out" failure.
   - **The output leaves the narrow edge with a heavier pen**
     (`penwidth=1.8`) and a label, so the exit reads at a glance.
10. **Legibility: no text ever sits on a line, and spacing makes every
    association unambiguous** (owner, 2026-10-19). If a reader has to guess
    which label belongs to which arrow or which block, the diagram fails —
    same as an untraceable flow.
    - **Labels never overlap an edge, another label, or a node fill.** Same-
      rank (horizontal) edge labels use `xlabel` — plain `label` gets
      overdrawn by node fills. A label that would cross any line moves: change
      the ranks, not the font size.
    - **One job per rank; spread ranks before adding columns.** If a rank
      holds more than about three blocks, or any two labels would sit within
      a label-height of each other, split it into two ranks. White space is
      free; a cramped diagram costs the reader the association.
    - **Edge labels sit beside their edge, offset from the arrowhead.** An
      unlabeled arrow must still be identifiable by position — label and
      arrow travel together, end to end.
    - **The readback is a legibility check, not just a flow check.** When you
      read the rendered PNG at full resolution, verify per rule: no text on
      any line, no two text elements touching, every label within a finger's
      trace of its arrow. Any violation re-ranks the diagram — never shrinks
      text to fit.

## Title

**Every diagram carries its title at the top, in bold** (owner, 2026-10-22).
The title is the graph label, so it is part of the drawing and travels with
it into every render and every book:

```dot
graph [label=<<B>Write path through the storage records and mc_bank_pick</B>>,
       labelloc=t, labeljust=c, fontname="Helvetica", fontsize=12];
```

- `labelloc=t` puts it above the drawing; dot's default is the bottom,
  where a title reads as a caption and is the last thing seen.
- Bold needs the HTML-like label form `label=<<B>...</B>>`. Inside it `&`,
  `<` and `>` are written `&amp;`, `&lt;`, `&gt;`, and a line break is
  `<BR/>`, not `\n`.
- The title says what the drawing shows and what it fixes: the clock for a
  single-clock block, "one of N channels", "(combinational)", "(planned)",
  the generated-value list for a sized module -- the rules below name what
  goes there. It never restates the module name alone; the block labels
  carry the names.
- `bin/render_block_diagram.py` reports the title state on every render
  (`title: bold, top`); a missing, bottom or plain title is called out in
  the same line. The 2026-10-22 census: 643 diagrams had a plain title at
  the top, 14 at the bottom, 13 none; convert a diagram when you next touch
  it, and always check the render.

## Labels

Every block label has two lines:

1. a descriptive name that says what the block does (for example "Write
   Request Packetizer");
2. the owning RTL below it (`module - FUB`).

A label answers "what does it do?" before "what is it called?".

### Parameters and configuration values

**Case:** `docs/markdown/assets/rtl-common/graphviz/dataint_crc.dot` (owner,
2026-10-12).

- **Most parameters go unmentioned.** Sizes such as `AW`, `DW`, `DEPTH` and
  `WIDTH` explain themselves, or don't matter at diagram level.
- **A parameter that changes behavior is named, with what it does.** For
  example, `REFIN` and `REFOUT` decide whether bits are reflected. Put such
  parameters in a white "Parameters (fixed at build)" legend box with no
  edges, one line per parameter in the form `NAME: 1 = what happens`. The
  block where the parameter acts also states it (for example "REFIN=1:
  bit-reverse each byte").
- **Configuration values are described, not just listed.** A runtime value
  that defines the algorithm (for example `POLY`, `POLY_INIT`, `XOROUT` on a
  CRC) is explained in its legend: what it is ("generator polynomial - the
  feedback taps") and where it acts. A bare list of names tells a reader
  nothing they couldn't get from the port table.
- **Say what kind of value it is in the legend title:** "Parameters (fixed at
  build)" versus "runtime input ports". The reader needs to know whether the
  value can change without re-synthesis.
- **Use left-justified lines (`\l`) for a legend box,** with a hanging indent
  on wrapped lines, so each name heads its own line.

## Element key: shape and fill name the element (v3, owner rulings 2026-10-19)

**Owner, 2026-10-19:** "I can't tell what is what by looking at it." A box
had to be read to learn whether it was a port, logic, a register or a
memory. Every node now takes the shape and fill of its class.

**Reference example** (owner, 2026-10-19: "a very good example ... it has
most of the elements"): the mem-ctrl AXI plane, stored with this note in
`vault/handbook/authoring/assets/block-diagrams/` -- `axi_plane.dot` and the
rendered `axi_plane.png` (its key is generated, see "The key"). Copy from it;
do not retype. It is brought to the rulings
below (its debug-directory original filled every block green and marked
flops `[==]`). Its legibility pass stacked every multi-field payload as a
multi-line `xlabel` and widened `nodesep` 0.35 -> 1.1 so each label fits
between its lanes (six had sat across a neighbouring line).

| Class | Graphviz | Fill | What it marks |
|---|---|---|---|
| Interface / boundary | `shape=box, style="rounded,filled"` (bar: `penwidth=2.2`); comb crossing adds `dashed` | `#E2EFDA` green | A port of the drawn unit, and the boundary bar |
| Combinational | `shape=box` | white | Logic with no state: masks, compares, muxes, decodes |
| Registered | `shape=box, peripheries=2` | `#D6E4F0` blue | A block whose output is a flop: pipeline and issue registers, counters, sticky flags |
| FSM | `shape=box, style="filled,diagonals", peripheries=2` | `#FCE4D6` peach | A sequencer with named states |
| Storage | `shape=cylinder` | `#E8DFF5` lavender | FIFO, RAM, CAM, register file |
| Arbiter / pick | `shape=invtrapezium` (rule 9) | `#FFF2CC` gold | A genuine many-to-one pick |
| Optional | the class's shape, `style` plus `dashed` | the class's fill | Build-dependent (rule 8) |
| Legend / note | `shape=note` | white | Parameters, notes |

: Element key

| Edge | Graphviz | Carries |
|---|---|---|
| Flow | solid, `color="#333333"` | Request / forward data |
| Return | solid, `color="#1A7A1A"` green (dashed where the hop is a sideband-style handoff, as in the example) | Return data (read data, responses back to the requester) |
| Heavy | `penwidth=1.8` | The main path, or a pick's winner |
| Sideband | `style=dashed, color="#777777"` | Grants, credits, probes, config, status |

: Edge key

- **Fill is by class, not by area** (owner, 2026-10-19). Green is ONLY for
  interfaces and the bar. Inner blocks take their class fill: logic white,
  registered blue, and so on. The example's original, which filled every
  block green, was corrected.
- **Registered is a double border plus blue** (owner, 2026-10-19), never a
  text marker such as `[==]`. Shape carries the class so a black-and-white
  copy still reads: double border, cylinder, rounded, trapezium, diagonals.
- **Return data is green** (owner, 2026-10-19). Colour now carries one
  meaning: green edges are return data. The geography rule still holds
  (return climbs its own side lane); the colour repeats it.
- **Classify from the RTL, not the name.** A block whose output is
  registered is Registered even if most of it is logic (the AW issue
  register; the intakes, whose outputs leave through `gaxi_fifo_sync`). A
  block that passes data straight through is Combinational, with any hold in
  its label (the burst chopper's first beat passes `fub_axvalid` through).
  If a timing cut matters to the reader (a request register added for 100
  MHz), draw it as its own Registered box.
- **Interfaces state their timing class** (owner, 2026-10-19). Every
  interface node and plane crossing is annotated `flopped` or `comb`: in the
  node label ("AXI AW / host (flopped)") or on the edge ("(comb)", "(flopped
  at DFI cmd FIFO)", "(sampled at store)"). A combinational crossing is where
  timing failures live -- a diagram that hides them hides the one thing the
  reader came to check.

### The key

- **The key shows only what that drawing uses** (owner, 2026-10-19): the
  line styles and the node classes present, nothing else. An absent class
  is not sampled.
- **The key is graphical samples, not prose** (owner, 2026-10-19): every
  shape drawn next to its name, every line style as a short drawn arrow. A
  text-only legend ("solid: flow | dashed: sideband") is meaningless -- the
  reader must see the style once and match it everywhere. The row is titled
  by a plain `Key` label node.
- **The key is GENERATED, never drawn by hand** (2026-10-19). The renderer,
  `bin/render_block_diagram.py`, reads the drawing's resolved attributes
  (`dot -Tjson`), samples exactly the node classes and line styles it uses,
  renders that row on its own and pastes it centered under the drawing.
  A key cannot drift from its drawing or carry an absent class, and no
  diagram carries a `cluster_key` (dot cannot center a multi-item row; every
  anchor variant tried left it off-center). More whitespace beside the key
  than key content is a design failure; the composite keeps it centered.
- **The interface sample says "(flopped)" only when the drawing itself
  annotates its interfaces "flopped"**; otherwise it reads "interface". A key
  must not claim a timing class the drawing does not state.
- **A figure in another vocabulary carries `// render: no-key`**: decision
  trees and process flows (white questions, blue actions), and conceptual or
  software figures (generator pipelines, layering, run matrices, build
  fan-outs, topology maps). They keep their own vocabulary and get no key.
  Cycle grids and address maps (HTML-table nodes) have nothing to sample and
  get none automatically.

## Tool: graphviz dot

**Graphviz `dot` is the owner's preferred tool for block diagrams** (owner,
2026-10-12). The source is a checked-in `.dot` file beside its rendered `.png`,
in the doc's `assets/graphviz/` directory. Markdown references the `.png`.
`md_to_docx.py` renders only Mermaid fences, so a graphviz figure is always a
checked-in asset, never a fence.

```dot
graph [rankdir=TB, bgcolor="white", fontname="Helvetica", fontsize=11,
       nodesep="0.35", ranksep="0.60", splines=ortho];
node  [fontname="Helvetica", fontsize=10, shape=box, style=filled,
       fillcolor="white", color="black", margin="0.12,0.06"];   // combinational default; see the element key
edge  [fontname="Helvetica", fontsize=9, color="black", arrowsize=0.7];
```

- **Flatten the alpha channel before quantizing.** `dot` writes RGBA PNGs,
  and `convert -colors 64` on the transparent border paints a grey dashed
  line down the right and bottom edges. The fix is `-background white
  -alpha remove -alpha off` ahead of `-colors 64`. It showed up on 8 of the
  first 15 rtl-cdc diagrams. Check with
  `convert X.png -crop 1xH+(W-1)+0 -format '%[fx:minima.intensity]' info:`;
  anything well under 1 means a line.
- **Render with the directory's `regenerate_all_graphviz.sh`.** Every copy
  is the same three lines: it hands the directory's `*.dot` to
  `bin/render_block_diagram.py`, which draws each one, generates and
  composites its key, writes 150 dpi PNGs palette-encoded to PNG8 (alpha
  flattened first) and excludes the `tIME` chunk, so an unchanged source
  re-renders byte-identical. A new `assets/graphviz/` directory copies the
  script from any other.
- **Assets for the RTL books live per area** (owner, 2026-10-12):
  `docs/markdown/assets/<area>/`, matching the book directory
  (`rtl-amba`, `rtl-amba-monitors`, `rtl-cdc`, `rtl-common`, `rtl-math`).
  Inside it: `graphviz/` (`.dot` + `.png` + the regenerate script), `waves/<module>/`
  (WaveDrom JSON + PNG), and `mermaid/` only for non-block figures that stay
  Mermaid. rtl-cdc has no `mermaid/`: its nine legacy sketches were unused
  and were deleted once the graphviz set replaced them.
  An area's assets cover the modules in its `rtl/<area>/` directory only: an
  amba wrapper with "cdc" in its name uses a cdc FUB, but it is an amba block
  and its figures stay in `rtl-amba`. `rtl-cdc` was the first area moved.
- **Keep `rankdir=TB`** and an aspect ratio between about 0.7:1 and 2.5:1.
  A wide strip collapses to illegibility when it is fitted to the page; see
  [[spec-doc-standards]] "Image sizing".

## Layout recipes (the failures behind them)

- **Pin ranks with `{ rank=same; ... }`.** Order blocks within a rank with
  invisible edges when the layout fights the flow geography.
- **Return-flow edges drawn downward use `dir=back`.** The arrowhead still
  points the way the data goes, and the ranks stay top-down.
- **Horizontal (same-rank) edges use `xlabel`, not `label`.** A plain label
  is drawn at the edge midpoint and the node fill paints over it. The
  "timer window" arrow into the scheduler trapezium was the case. In
  `splines=ortho` this is absolute and stronger than it sounds: dot does
  not render PLAIN edge labels at all ("Orthogonal edges do not currently
  handle edge labels") — `xlabel` still renders, `label` vanishes. Sample
  arrows in a legend are the trap: a labeled sample edge must use `xlabel`
  or be drawn without `splines=ortho` (short legend arrows don't need ortho).
- **A key row that must be exactly centered is rendered separately and
  composited** (owner, 2026-10-19). Dot cannot center a multi-item row under
  the graphics: a cluster is an anchored object, and a single anchor edge
  pins one node's column while dot reorders the rest freely -- a dozen
  anchor variants all left the row off-center (case: `mem-ctrl-ip/debug`).
  `bin/render_block_diagram.py` does it for every diagram: the key row is
  its own dot graph (same rank, short sample arrows, `nodesep=0.14`, NO
  `splines=ortho`, which swallows plain edge labels), rendered at the same
  dpi and pasted centered under the drawing with Pillow.
- **Stack multi-field payloads as a multi-line `xlabel`.** "snarf probe /
  {bank,row,col} / hit + data" becomes `xlabel="snarf probe\n{bank,row,col}\nhit
  + data"` — three short lines centered on the segment read as one payload,
  instead of one long line drifting into a neighbor.
- **A sideband whose label would crowd its segment routes through a visible
  waypoint box** (owner, 2026-10-19): a small white port box (the DFI port
  idiom above), never an invisible `shape=point` — the visible box gives the
  bend something to land on and buys the label guaranteed-empty space beside
  its segment.
- **Never draw two parallel edges between the same node pair for two
  classes.** Dot assigns their channels in an order you can't control, and
  `splines=ortho` ignores labels when it routes, so the labels drift and
  mislead. Use one edge with a combined label (`WR / RMW`). The same goes for
  taillabel/headlabel tricks: if a label doesn't land where you want it,
  change the edge structure, not the label.
- **Default: no invisible scaffolding.** Draw direct edges between visible
  nodes and control the layout with `{ rank=same; ... }` pins, `group=`
  columns, and `constraint=false` on return lanes. Owner ruling
  2026-10-18: bends at invisible `shape=point` nodes are unexplained on the
  rendered page — "you can't tell why the line went there." Every bend must
  be attributable to something visible: a labeled box, the boundary bar, or
  an obvious dodge around one. If a lane must join the boundary at a
  specific place, make the crossing a **visible white port box** (the DFI
  planes' port boxes are the idiom) so the bend lands on a labeled thing.
  Keep every multi-rank climb monotonic — each leg goes to an equal-or-higher
  rank; a leg that dips to a lower rank and climbs again draws the "weird
  jagged loop."
- **Point-node scaffolds are a last resort, not a tool.** Reach for them
  only when several crossings join the same node pair and direct edges
  demonstrably shuffle channels and flip direction unpredictably (the
  original PHY-bar case). Then route each crossing through its own invisible
  `shape=point` node in a pinned rank (`{ rank=same; ... }` plus an invisible
  spacer chain for order), so each crossing is a distinct node pair with a
  fixed direction and label placement. A leg through a point node leaves a
  hairline gap (ortho ignores `headclip`/`tailclip`), invisible at print
  scale. But if a scaffolded lane still zigzags, delete the scaffold and
  restructure — the CELL credit-loop figure renders cleaner with one direct
  `pktbld -> meshbar` lane than any point chain did.

### Recipes that made the `fifo_async` layout converge

It took about ten renders, and each recipe below fixed a specific failure.
Start a new diagram from them, not from a blank file:

- **Column grid via `group=`.** Give every node in a column the same
  `group`, so dot keeps it vertical and the edges between them straight. For
  example, the outer counter column carries its address straight down. Order
  the columns with invisible same-rank edges.
- **Never stack two blocks in the column a long lane must pass through.**
  With the flags directly under the counter, the counter's address lane had
  to detour around them and tangled. Move the second block to the inner
  column instead.
- **Use an invisible center spine to center the bar.** Add one tiny
  `shape=point, style=invis` node per rank, all in `group=C`, chained down to
  the bar with `weight=10`, and put the bar in `group=C` too. Without it, dot
  centers the bar on its in-edges and it drifts toward whichever side has
  more of them. Widening the bar alone only grows the drawing.
- **Pull on the bar symmetrically.** An edge with `constraint=false` exerts
  no pull. Draw the return lane's lower leg as a constrained edge with
  `dir=none` (`p_rdd -> mem [dir=none]`), so both sides weigh the same.
- **Size the bar to reach the outer lanes,** otherwise they hook into its
  side. Check the render and adjust `width`.
- **Under `splines=ortho`, use `xlabel` on long scaffolded edges.** A plain
  `label` was placed on a neighboring lane ("wr_data" sat on the address
  line). `headlabel` with `labelangle`/`labeldistance` separates two labels
  that would otherwise collide where two edges run parallel (the two Gray
  pointer crossings).
- **Keep point scaffolds out of a rank that holds nodes inside a cluster.**
  `dot` crashed with an ortho maze assertion when they shared one
  (`gaxi_skid_buffer_async`); moving the scaffolds to their own rank fixed it.
- **A spacer needs `label=""` and a fixed width.** `minlen` between point
  nodes in the same rank has no effect.
- **`tailport`/`headport` break edges under `splines=ortho`.** The port is
  ignored and the edge starts at the node center, drawn across its label
  (`fifo_sync`). Leave ports off; spread edges with columns or scaffolds.
- **A scaffold needs at least one constraining edge.** Point nodes placed
  only with `constraint=false` edges drift and drag lanes through the center.
- **Labels on ortho corners drift between renders.** Fix the geometry so the
  labeled leg is straight. For example, widen a block so a drop lands
  vertically. Put an `xlabel` on the long leg of a scaffolded lane and leave
  the short final leg unlabeled.
- **A spacer node does not always widen a same-rank gap.** Moving a third
  node to the other side of the lane removed the crossing
  (`dataint_ecc_hamming_decode_secded`).
- **Feedback into a block that has ports above it** needs two pinned point
  scaffolds, one in the register's rank and one in the next-state block's
  rank. Alternatively, draw `upper -> lower [dir=back]`, which is
  constrained. A single `constraint=false` scaffold loops over the top.
- **One input feeding two blocks splits at a labeled point node.** A shared
  input trunk gets one label on its long leg, and short `headlabel`
  indices (`[7]`, `[6:1]`, `[0]`) at each arrowhead.
- **A combinational output tapped off next-state logic** runs down the left
  edge to the output bar. Place the Clock / Reset box between that lane and
  the register so the two don't cross.
- **When parallel path blocks fed by one input force crossings, merge them**
  into one block that describes each path in its label (`shifter_barrel`).
- **graphviz 2.43 `splines=ortho` can crash** with "Trapezoid-table
  overflow", even on a plain vertical chain (`math_mod_3_compress`). For an
  all-vertical chain, `splines=line` renders the same picture.
- **A labeled edge between blocks in the same rank lands its label on the
  boxes.** Put the two blocks one rank apart and let the edge run
  diagonally.
- **The lower leg of a scaffolded return lane must be `dir=none`;**
  otherwise a stray arrowhead appears mid-lane.
- **The graphviz 2.43 ortho router also asserts in `maze.c chkSgraph`** on
  some small layouts. Nudging `nodesep` (0.40 to 0.45) cleared it; width
  tweaks did not.
- **A family of near-identical diagrams is best generated from one
  parameterized script** (`gen_base.py` / `gen_var.py` per family), so
  layout stays identical across master/slave and rd/wr.
- **Opposite lanes between the same pair** (commands down, status up):
  route both through scaffold points held in one same-rank row by an
  invisible order chain. Otherwise dot swaps the lanes.
- **Run PDF builds one at a time.** Parallel `md_to_docx` / LibreOffice
  builds collide: one fails, or its TOC update is skipped.
- **A label-size change can also trigger the graphviz 2.43 `maze.c
  chkSgraph` assertion.** Shortening the label fixed it when nudging
  `nodesep` did not. A labeled same-rank edge next to clusters also crashed.
- **Shorten node labels before fighting the aspect ratio.** Long third lines
  widened every column and pushed the drawing past 2.5:1.

## Verification: render, then read

**Never commit a diagram you haven't looked at.** After rendering:

1. Open the PNG at full resolution.
2. Trace every flow with a finger, by rules 1-5.
3. Check rule 9 on the trapezium: classes in, one heavy labeled exit.
4. Check the aspect ratio: `identify -format '%wx%h' file.png`.

If you can't trace a flow, the layout is wrong. Fix the ranks, not the
colors.

## Mapping to other block shapes

The owner and the agents fill this in as the repo-wide conversion proceeds.
Each entry states the ruling and names the diagram that set it.

### Dual-clock / CDC blocks

**Case:** `docs/markdown/assets/rtl-cdc/graphviz/fifo_async.dot`. The owner
approved it on 2026-10-12 as matching the reference's style and visuals. It is
the template for every CDC block.

- **The ports are the channels:** the write port is top-left and the read
  port top-right, both white.
- **Forward data drops down the left edge into the bar.** Return data leaves
  the bar's right side and climbs the right edge, which is the reference's
  spatial loop.
- **The boundary bar is the structure both clocks touch.** For the FIFO
  that's the dual-port storage. The clock domains are dashed regions
  (`subgraph cluster_*`, `style=dashed`), one per side, mirrored.
- **The signals that cross between domains take the center**, where the
  command column sits in the reference. They are drawn with the heavy pen
  (`penwidth=1.8`) and form an X between the domains. Each crossing lands
  on a synchronizer drawn in its DESTINATION domain, on the inner column
  next to the boundary.
- **Decisions show both of their inputs.** A flag block draws the local
  pointer and the synchronized remote pointer it compares.
- **Status flags are dashed feedback** to the port they gate.
- **No trapezium** when nothing arbitrates; rule 9 applies only to a real
  many-to-one pick.
- **Merging is allowed for readability.** A synchronizer and its decode
  (`glitch_free_n_dff_arn` + `gray2bin`) may share one box. A parameterized
  alternative (Johnson mode) is a third label line, not a second diagram.
  The label's second line names the module, not the instance, so boxes stay
  narrow.
- **The boundary bar is whatever crosses unsynchronized.** For the
  handshakes and `cdc_open_loop` it is the held data bus, loaded on the
  source clock and captured on the destination clock.
- **A wrapper whose only crossing is inside a child** draws that child as the
  bar, pointing at the child's own diagram (`gaxi_skid_buffer_async` over
  `gaxi_fifo_async`). A domain with no logic of its own gets no dashed
  region.
- **A one-way crossing is one heavy edge with no X**, and the empty inner
  column makes the missing acknowledge visible (`cdc_open_loop`).
- **A one-sided module (destination clock only)** draws only the destination
  domain. The source is a white port outside it, or a dashed "upstream, not
  in this module" region (`glitch_free_n_dff_arn`, `cdc_synchronizer`,
  `reset_sync`).
- **Valid/ready:** valid and data ride the solid flow edge, and ready is a
  dashed return labeled with its source (`wr_ready (= !full)`). Where a port
  talks to one control block, a single `dir=both` edge labeled
  `src_valid / src_ready` satisfies rule 1.
- **Collapse a long flop chain to two boxes:** the capture stage (may go
  metastable) and the settling stages.

### Single-clock and combinational blocks

**Cases:** `bin2gray`, `gray2bin`, `johnson2bin`, `counter_bingray`,
`counter_johnson` (`docs/markdown/assets/rtl-cdc/graphviz/`).

- **Inputs are white boxes at the top; the outputs are a white bar at the
  bottom,** which serves as the boundary bar.
- **Register feedback climbs the right edge** back into the next-state
  logic, the same pattern as the read-data return.
- **Clock and reset** are a white box with dashed sideband, kept on the side
  away from the feedback lane. A combinational block has none, and its title
  says "(combinational)".
- **Three to six blocks.** Show the real structure (next-state logic,
  register, decode), not individual gates.

### rtl-common samples (owner-approved 2026-10-12)

**Cases:** `docs/markdown/assets/rtl-common/graphviz/` -- `arbiter_round_robin`,
`fifo_sync`, `dataint_crc`, `dataint_ecc_hamming_decode_secded`, `cam_tag`,
`clock_gate_ctrl`. The owner reviewed all six: "all are great".

- **The trapezium marks any genuine many-to-one pick:** an arbiter's grant
  (`arbiter_round_robin`, with masked and unmasked requests as the class
  labels into the wide edge) or a lowest-free-slot finder (`cam_tag`). A
  mux driven by an external select is a plain box.
- **A single-clock storage block** uses the `fifo_async` geography with no
  clock regions and no crossing X. Both pointers converge on one flag block
  (`fifo_sync`), and the title names the clock.
- **Independent request flows get one column and one white port each**
  (`cam_tag`: insert, invalidate, lookup). A search reads the storage bar
  straight up its own column (`dir=back`), rather than feedback fanning out
  across the ports.
- **When the output is a clock, the clock is the main flow:** a heavy,
  straight column from the clock input through the gate cell to the output
  bar. Control logic joins the gate from the side (`clock_gate_ctrl`). A
  clock that only clocks control flops is not drawn; "(on clk_in)" goes in
  the block label.
- **N identical combinational stages collapse into one box** labeled with
  the count (`CHUNKS x dataint_crc_xor_shift_cascade`).
- **Mark the timing in labels:** registers say "(flop)", logic says
  "(combinational)", and next-state logic sits above the register it loads.
- **Parallel independent checks share one rank** and fan into the decision
  that combines them (syndrome and overall parity into the SECDED
  classifier).
- **A build-dependent block is dashed, with its condition in its label**
  (the ACK tracker, "WAIT_GNT_ACK=1 only"). A degenerate configuration
  (`CLIENTS=1`) goes in the title, not a second diagram.
- **Load strobes and enables share the Clock / Reset box** when they drive
  the same registers.
- **One heavy edge per diagram where possible:** the main flow, or the
  trapezium's exit.

### rtl-common, full area (2026-10-12)

All 50 `rtl/common` modules now have a diagram. These rulings came out of
the full pass, on top of the approved samples above.

**Picks and the trapezium**
- **Only a genuine many-to-one pick gets the trapezium:** priority encoders,
  find-first and find-last set, every arbiter's grant.
- **These are plain boxes:**
  - a one-hot encoder (its input is not a set of contenders);
  - leading/trailing-zero counts;
  - a mux or mode select driven by a port.
- **No pick, no trapezium.** A one-client arbiter and a token-bucket rate
  shaper in front of an arbiter have none, and the title says so.
- **A wrapper over a base arbiter draws the base instance as the trapezium**
  (`u_base_arbiter` in the weighted and deficit round-robin). Its
  registered grant goes straight to the output bar.
- **Both class inputs land on the wide edge.** Put the mask in the center
  column, run the unmasked bypass down a point scaffold on the left, and
  keep the right edge for the last-winner feedback. Ortho can't land an
  edge on the slanted side; make the trapezium wide enough that sideband
  from above lands on the wide edge.
- **A stored-state input to the pick** (the priority matrix) sits beside
  the request gate and drops onto the wide edge.
- **An enable that forces the pick's output to zero** is dashed sideband
  into it, labeled with its effect.

**Ports, legends and labels**
- **A runtime operation code** (`ctrl`, `select`) gets a white legend box
  listing every code and what it does, dashed into a plain "Mode Select" box.
- **A broadcast configuration input** (`poly` into eight stages) is a
  legend box with no edges, rather than N identical edges.
- **A runtime port that feeds a sequencer FSM** (`max_thresh`, `quantum`) is
  a white port with a solid edge into it.
- **A runtime mode bit** (`parity_type`) is dashed sideband; its meaning is
  stated in the port box.
- **Size-like parameters that set behavior** (`MAX`, a period `WIDTH`) go in
  the title. Behavior-switch parameters go in the Parameters legend.
- **Put edge cases in the output label:**
  - a missing valid ("no bit set: 0 - no valid flag");
  - parameter corner cases (`decoder` with `N < 2^M`);
  - a comparison against an input port, when drawing it would cross a
    feedback lane.
- **Register update rules may be a case list in the register's label**
  ("idle: load next | acked + others: load next | ...") instead of several
  control edges.
- **Combinational and registered outputs are named in the bar title:**
  "Outputs (same cycle as request)" versus "Outputs (registered)".

**Structure**
- **Multi-channel modules draw one channel.** The title says "one of
  CHANNELS identical channels", or a box label carries "N x".
- **A control FSM that sequences a datapath** sits in its own left column,
  with dashed control edges into the registers. Its status output (`done`)
  runs straight down that column.
- **A pipelined chain shows its first one or two stages in full**, then one
  counted box. A parallel valid pipeline gets its own column.
- **First, middle and last may replace a counted box** when the order
  matters (MSB-first stages in the CRC cascade).
- **A parent that wraps child modules draws them as instance boxes**
  pointing at their own diagrams (`leading_one_trailing_one`).
- **Two state loops go on opposite sides of the main column**
  (`arbiter_matrix_weighted`: credits left, matrix right).
- **Fibonacci versus Galois is shown by where the XOR sits:** an external
  feedback block beside the shift path, or in-chain tap XORs in series in
  the main column.
- **Shared flag logic** (`fifo_control`) keeps `fifo_async`'s mirrored
  domain regions without the X; its remote pointers are labeled "(remote,
  synchronized)".
- **An optional register that changes behavior is dashed,** with its
  condition in its label (the `REGISTERED=1` pointer delay).
- **Handshake flags that read storage** sit in their own column, reading the
  storage bar straight up.
- **A clock-gate primitive's clock** drives the latch dashed and runs heavy
  straight through the AND (`icg`). A divided clock's output column is
  heavy (`clock_divider`).
- **When a Clock / Reset box garbles a layout,** drop it and write "(flop on
  clk)" in the register's label.

### rtl-math (2026-10-13)

The 31 content pages hold 29 diagrams. The catalog pages (`math_fp8/16/32_modules`,
`math_bf16_extended`, `math_library`) list many small independent functions
with no shared datapath, so they get none. A catalog does not get a forced
diagram.

- **A generated per-width family gets one diagram per page.** The widths
  go in the title (`<N> = 8 / 16 / 32 / 64`) or in a white "Generated
  Variants" legend giving each width's stage counts, cell counts and final
  adder. An algorithm family (the five integer dividers) draws the shared
  recurrence once, with a "Variant (one module each)" legend for the
  differences.
- **Leaf arithmetic cells are drawn as gates** (full adder, half adder,
  black and gray prefix cells), because the gates are the real structure.
  Prefix cells carry their span ranges (`[i:k]`, `[k-1:j]`, `[i:j]`).
- **A ripple chain makes the carry or borrow the heavy main column**, LSB
  at the top. Operand bits arrive on a left trunk with headlabel indices,
  and result bits leave on a right trunk.
- **A carry-save array draws its bit cells side by side with no edge
  between them,** so the missing carry chain is visible. The output bar
  states the `<< 1` weighting the consumer applies.
- **A prefix adder is pg, then the prefix network's stages in order as
  plain boxes, then sum.** Nothing picks, so there is no trapezium. A
  "Prefix cell types" legend explains black and gray cells. The per-bit
  propagate is a bypass lane down the left into the sum.
- **A reduction tree shows its first stage in full, then one counted box.**
  The Dadda versus Wallace difference (reduce only above the target, versus
  compress early) goes in the labels. A regular cell array draws its cell
  as a legend with equations, then row 0 and rows 1 .. N-1.
- **A floating-point datapath reads operands, then Unpack + Classify, then
  the field paths side by side** (sign as a thin left column, mantissa in
  the center, exponent on the right), then normalize, round, special-case
  select, and the output bar.
  - Classification flags ride a dashed right lane into the select.
  - An exponent that depends on the mantissa's normalize bit sits one rank
    below the mantissa block.
  - A two-format module (FMA) gives each operand format its own column,
    merging at the align block.
- **A priority select among candidate results is a plain box,** with the
  order as a `>` chain in its label. It is not a trapezium: special cases
  override a result rather than compete for a grant.
- **Optional pipeline banks** (`PIPE_STAGE_n`) are thin dashed boxes between
  stages, explained once in a Parameters legend. One dashed clock edge
  covers all banks, and signals carried alongside (valid, flags) share one
  dashed side lane labeled "(through the same banks)".
- **A mode bit with two jobs splits at a point node:** the mode branch is
  dashed and the data branch solid (add/subtract `i_c`: invert B, and the
  +1 carry-in).
- **A shared unit time-multiplexed by an FSM** puts the loop on the right:
  operand select over the unit, with the product returning up the right
  edge. The FSM's select is dashed, and a one-cycle special-case shortcut
  runs dashed down the left into the output registers.
- **A trivial path** (an XOR'd result sign) folds into the label of the
  block that consumes it.
- **A sub-module drawn on another page is one counted box,** and one figure
  may appear on two pages.

### rtl-amba (2026-10-13)

171 diagrams cover every `rtl/amba` module page (`wb4_pkg` defines types
only). Templates: `axi4_*`, `axil4_*` and `apb4_*` in
`docs/markdown/assets/rtl-amba/graphviz/`. The AXI5, AXI5-Lite, APB5, WB4
and ACE pages were derived from them so the families look alike.

**Bus interfaces**
- **Ports and lanes:**
  - The requester side is a white port box on top; the completer side
    (the module boundary) is the bottom bar.
  - Each channel gets its own lane: write data (W) on the left, address
    in the center, responses (R, B) climbing the right lane via
    `dir=back`.
  - A channel hop is one edge per node pair, labeled with the channel and
    what it carries: "AR: id, addr, len ... (valid down, ready up)".
- **APB and Wishbone follow the same lane rules.** The command goes down
  the left. The response (PREADY/PRDATA, or ACK/ERR/RTY plus DAT_R)
  climbs the right. STALL is a dashed return.
- **The skid buffers and FIFOs the RTL instantiates are named boxes on
  their channel's lane** (`gaxi_skid_buffer - ar_channel`).
- **A status output computed from many counts** (`busy`) sits between the
  lanes and leaves through the bar, which names its destination ("busy (to
  the clock-gate wrapper)").
- **Optional protocol fields** (`ENABLE_*`) are one "+ AXI5 ... fields when
  enabled" line in each skid box plus one Parameters entry. Optional
  parity is one dashed block beside the beat path. A wakeup hold is a
  dashed block beside busy.
- **ACE is the axi4 diagram plus its additions.** RACK/WACK is a flop
  beside the response lane on a master, and a plain dashed wire on a
  slave. The snoop channels (AC down, CR and CD back up) get their own
  lanes.

**Variants: one rule for every family**
- **A `_cg`, `_mon` or `_mon_cg` page draws the base module as one child
  box** ("see its diagram"). Each side of it is a single `dir=both` edge
  with a combined label ("AR out / R in"). Two parallel edges between the
  same pair break rule 1.
- **`_cg`:** the clock-gate controller and the heavy clock and gated-clock
  column sit on the left. The activity terms and the forced-ready rule go
  in the controller's label, not on edges.
- **`_mon`:**
  - The `USE_MONITOR`-only monitor is a dashed box.
  - Its tap is a short dashed edge from the FUB side, which is where every
    wrapper taps (owner ruling, 2026-10-13; see [[observers-do-not-drive]]).
  - `block_ready` is dashed into a handshake-gate box on the request lane.
  - Monitor packets are the heavy edge to a white outputs box.
- **`_mon_cg`** is the `_cg` drawing wrapped around the `_mon` child. A full
  stub is two child boxes (write stub and read stub).
- **A signal the wrapper itself computes** gets its own output box, not a
  line in the child's label.

**Monitors and observers**
- **A pure observer** (bus meters, latency histogram, every monitor) draws
  its taps as a white input labeled "(observed, nothing driven back)",
  with no edge back to the bus.
- **Several packet sources competing for one output bus is a real pick,**
  so it gets a trapezium. So does a lowest-matching-entry scan over a
  transaction table, and a 2:1 packet merge. A packet-type select where
  special cases override, or an allocator that works in issue order, is a
  plain box.
- **Several inputs onto a wide trapezium edge:** put the feeding blocks in
  the same rank directly above it and widen the trapezium to span them.
  Scaffold nodes drift.
- **A pick on an upward (response) path uses `shape=trapezium`,** with the
  wide edge down, so the wide edge still faces the contenders. Example:
  the atomic filter's B and R merges.
- **A CAM read by its owner:** storage goes near the top under the write
  port, dropping into the compares and onto the pick. Storage drawn as
  the bottom bar fed the pick's narrow edge and pushed the aspect past
  4:1. A manager wrapped around a CAM child draws the child as the bar,
  read straight up.
- **A two-cycle CAM labels its stages** "Cycle T" and "Cycle T+1".
- **A composite with two routing destinations** (`monbus_group_core`) gets
  one column per destination, with both endpoints sharing the bar.
- **A master-side test block** draws the memory under test as the bottom
  bar, with a Results box top-right. This is the reverse of a slave.

**Clock domains stacked vertically** (`*_slave_cdc`): the dashed regions
collided with the crossing labels, so name each block's domain in its label
instead and point at the cdc FIFO's own diagram.

### Component books: HAS / MAS / GAS (2026-10-13)

Every `projects/components/*` HAS/MAS/GAS book was converted:
- RLB (10 books)
- mem-ctrl (common, pumice, scoria, andesite)
- cache-ip (amber, jet, onyx)
- hive, dfx
- ECC (BCH, Reed-Solomon)
- converters
- kestrel
- gatling (2026-10-21: datapath, register file, memory system, system
  context, programmer's view, plus a rotation cycle grid and an address
  map table; kestrel's MAS gained decode, ALU, block-RAM memory system,
  load/store path and halt figures the same day)
- fabric-gen-ip (bridge, delta, lattice)
- dma-ip (RAPIDS, RAPIDS beats, STREAM)

The same pass rewrote many book passages that described blocks the RTL does
not have. A figure drawn from the RTL is a check on the prose around it.

**Whole units and systems**
- **Memory-to-memory DMA (STREAM):** the data loop takes the center. Read
  data climbs from the bar through the read engine into the SRAM, then
  drops through the write engine back to the bar. Descriptor fetch is the
  left lane; observers are on the right.
- **Network DMA with two independent halves (RAPIDS):** sink write data
  runs down the left and source read data comes back up the right.
  Descriptors and control run down the center to a shared-arbiter
  trapezium.
- **A peripheral's input-only pin group** (interrupt requests, timer
  gates, event pins) is a white port at the top, with its own column.
  Outputs and bidirectional pads stay at the bar.
- **System and context figures:** white masters and slaves around one blue
  unit, `dir=both` edges labeled by protocol. Several alternative
  placements get one dashed region each, sharing a bar when they share a
  medium (ECC: "the channel that corrupts").
- **A subsystem top with N peer windows** (rlb_top) staggers them over two
  rows, so every crossbar drop and pin lane runs straight.
- **A codec:** encoder and decoder each get one column into a shared
  output bar; the shared arithmetic (GF) layer is an edge-free legend. A
  pipelined decoder keeps its received data in a FIFO lane down one edge
  while the descriptor walks the solver stages in the center.
- **Generator (GAS) books:** stages fan out to one box per sub-generator,
  then into an "Emitted files" bar. A fan-out is NOT a trapezium (the old
  "emitter funnel" was wrong). Optional stages are dashed, with their
  flag in the label.
- **Planned blocks with no RTL:** say "(planned)" in the title and carry
  the open decision IDs (J1, D5, ...) in the labels.
- **Inheritance across a family** (scoria/andesite from pumice): INHERITED
  / MODIFIED / NEW goes on the last label line, never in color.
- **FUBs under `rtl/fub` that nothing instantiates** go in one dashed white
  legend box, not on a flow.
- **A topology map** (a mesh) is undirected, with `splines=line`.

**Picks**
- **A chain of identical picks** (the MonBus 4:1, 9:1, 3:1, 2:1 tree):
  shallow trapezia that widen down the page, so each narrow edge feeds the
  next wide edge. When the tree isn't the subject, it collapses to one
  dashed sideband box.
- **When contenders span more than about 60% of the width,**
  `invtrapezium` lands the outer arrows on the slanted sides. Use
  `shape=polygon, sides=4, distortion=0.10` (negative for an upward-path
  pick) so the wide edge stays flat.
- **A requester's grant returns on the same edge** as `dir=both`
  ("WR (commit slot back)"), never as a parallel edge.
- **An interrupt controller's acknowledge-by-read** is its own small box,
  feeding ISR/IRR. The vector climbs back to the register block.
- **A bus decoder** (one-to-many route) is a plain box.

**Processor cores** (kestrel, gatling, 2026-10-21)
- **A pipeline's stages are the ranks, and the stage registers are
  wide blue double-bordered rows between them** (`gatling_datapath`).
  One rank per stage boundary, so a reader counts latency down the page.
  A barrel's per-context state (PCs, halt bits) is ONE registered bank at
  the top, read by the fetch stage and written back by the execute stage;
  the write climbs the left edge as the one architectural feedback. No
  hazard or forwarding lanes are drawn when the design has none, and the
  title says why ("every stage holds a different context").
- **The memory bar's landing points need the point scaffold** on a core
  datapath: the fetch address lane (far left), the load/store beat
  (center or right) and the instruction / load-data returns (far right)
  all reach the same wide bar, and without pinned crossings dot lands
  two of them on one spot and routes a return across the middle. Pin
  `p_f` / `p_r` points in the last rank, as `kestrel_datapath` does.
- **Decode is a truth table, not a pick:** a white box in the datapath
  and, on its own page, insn port -> key split -> casez table (with the
  default bundle feeding it dashed from the rank above) -> control
  bundle bar. The earlier kestrel datapath drew decode as a cylinder; it
  holds no state and was corrected to white.
- **An OR-combined ALU draws its rows side by side in one rank** over an
  "OR-Combine" box, with the row select dashed into the combine. Flag
  outputs nobody consumes still get a lane to the result bar, labelled
  "unconnected in <core>". Narrow the row labels before accepting a
  strip wider than 2.5:1 (`rv32i_alu` went 3.7:1 -> 2.3:1 on labels
  alone).
- **A load/store path figure exists to show what is OFF the carry
  chain:** the two-bit offset adder is its own column and the misalign
  test, store lanes and load rotation hang from it; only the word address
  waits for the ALU. Merge the size decode into the offset box, or the
  size -> misalign and offset -> strobes diagonals form an unavoidable X.
- **A halt figure is causes on top, one resolve box, the holding bit
  beside the gates it feeds, and the gated state as the bar.** The
  holding bit's feedback is the same edge as its load, `dir=both`
  ("halt_now down; halt_q back up"), never a second parallel edge.
- **A barrel rotation is a cycle grid with ONE context shaded**, so its
  single instruction in flight reads down the diagonal and the "next
  fetch is after its own writes" argument is visible. The ASCII sketch it
  replaced showed every context and nothing stood out.
- **A per-context memory system is the loader layout widened:** the
  bank field goes in the port label ("addr[15:14] = context bank") and
  the array label ("bank = context"), and the run/status bank is one
  registered box with "one entry per context" in its label, not four.

**Generator drift, found while adding figures (2026-10-21)**
- `kestrel_mas/assets/wavedrom/wvf_4_1_basic_cycle.json` had been edited
  by hand; `gen_kestrel_figures.py` still carried the older dict, so the
  first regen churned a committed waveform. The committed asset was
  restored and the dict back-ported. The rule from [[doc-pipeline]]
  ("a regeneration script must be a no-op on unchanged sources") is the
  check: run the generator and `git status` before trusting it, and fix
  the script, not the asset, when they disagree.

**Pins, clocks, crossings**
- **Two engines sharing open-drain pads** (SMBus master and target): one
  "pad wiring + wired-AND merge" box at the bar, with one `dir=both` edge
  per engine.
- **A build-time clock select** (`CDC_ENABLE`) is a plain box the heavy
  clock columns run through. The bar names which clock each output is on.
- **One right-angle crossing is allowed** when the topology forces it
  (configuration to the event side, events to the register side). Put the
  label on each lane's straight leg.
- **Stacked clock domains:** write "on <clk>" in the block label instead of
  dashed clusters, which collide with the crossing labels.

**Conversions**
- **A Mermaid containment-hierarchy flowchart becomes an ASCII tree.** An
  ASCII state chart becomes a Mermaid `stateDiagram`, not graphviz.
- **A numbered-step data-flow chart that duplicates a block figure**
  becomes numbered prose pointing at that figure.
- **A figure shared between books** (HAS and MAS, beat and byte variants)
  is copied into each book's `assets/graphviz/`, with a "derived from /
  kept in step" header line, because each build searches only its own
  book's assets. Variants come from one generator script by label
  substitution, so the layouts stay identical.
- **An ASCII timing sketch becomes a graphviz cycle grid** (owner ruling,
  2026-10-13). It is an HTML-table node with one row per signal and one column
  per clock cycle, or per event or interval when the sketch is not to scale.
  A "1" cell is shaded blue, a "0" cell is white and a don't-care cell is grey
  "x"; equal neighbouring values merge. A boxed note row at the foot
  says what to read off it. The grid is a table, not a drawn waveform, so it
  does not conflict with the FPGA-book rule below that a timeline drawn as
  graphviz edges becomes WaveDrom. Draw every cell from the RTL, not from the
  sketch: the cmd/rsp adapter's sketch showed a registered ack where the
  PeakRDL cpuif acks combinationally, so a short Verilator run settled it.
- **Captions must be `### Figure N.M:` headings** (or the book's existing
  encoded form). An italic `*Figure 1:*` line never reaches the List of
  Figures.

### FPGA-system books (2026-10-13)

- **A bench figure:**
  - Host programs and Vivado are white ports on top, then the USB chip, the
    FPGA stack down the center, and the board's parts as the bar.
  - DDR crossings at the bar split into write, command and read, as in the
    reference.
- **A characterization harness:** the harness memory models (stand-ins for
  system memory) are the bar under the DUT's AXI masters.
- **Process flows** (measurement path, program path, sequence runner):
  - Use the decision-tree vocabulary, with each step boxed as "N. Step
    (where it runs)".
  - The heavy center column carries the steps, and the per-point loop
    climbs the right edge dashed.
  - Traps and "why" notes are dashed white notes attached to their step.
- **A build-variant fan-out:** the source is a white box on top and the
  knobs go in a Parameters legend. Each arrow is labeled with the knob
  settings that make that build.
- **N alternative CDC paths** sit side by side in one rank between the two
  domain regions, fanning into a plain-box register-driven select.
- **A timeline sketched in graphviz is a waveform.** Convert it to WaveDrom.

### Decision trees

A decision tree (`cdc_choosing`, which replaced ASCII art in `cdc.md`) is
not a block diagram, so the vocabulary changes: white question boxes, blue
answer boxes, and every arrow labeled with its answer.

## Where this is stated

- This note is canonical.
- The repo-root `AGENTS.md` restates the non-negotiables for every agent and
  points here.
- `docs/DOCUMENTATION_STANDARDS.md` points here.
- `common_has/assets/graphviz/STYLE.md` keeps only the memory-controller
  specifics (the DDR flow geography and label vocabulary) and points here.

Related: [[spec-doc-standards]], [[doc-pipeline]], [[doc-placement]],
[[module-doc-template]].
