---
title: Block diagrams
summary: The binding house style for every block / microarchitecture diagram - graphviz dot, flows traceable at a glance, labeled arrows, one boundary bar, render-then-read verification.
---

# Block diagrams

**Binding, highest priority, repo-wide** (owner ruling, 2026-10-11). Every
block or microarchitecture diagram follows this note: HAS/MAS books,
`docs/markdown` module pages, README figures, vault notes, FPGA system docs.
It supersedes the older "diagrams are Mermaid" rule in [[spec-doc-standards]].

**Status: v1, being refined.** The rules came from the memory-controller
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

**The owner values how clearly the flows read, not the palette.** Flow
clarity is the contract and color doesn't matter. The rules below are in
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
   every boundary crossing, the label names the transaction class (`WR / RMW`,
   `RD`, `REF / ZQ` going in; "Write to DDR", "Read from DDR", "DDR Command"
   at the PHY). Never use bare signal names. A label answers "what is this
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

## Palette: your choice

The default is white boxes for external interfaces and `#D6E4F0` functional
blocks on a white canvas. **Color never carries meaning.** Meaning lives in
the geometry (flow routes, the trapezium, the bar) and in the labels.
Swapping the palette must never change what the diagram says, and a
black-and-white photocopy must still pass every rule above.

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
       fillcolor="#D6E4F0", color="black", margin="0.12,0.06"];
edge  [fontname="Helvetica", fontsize=9, color="black", arrowsize=0.7];
```

- **Flatten the alpha channel before quantizing.** `dot` writes RGBA PNGs,
  and `convert -colors 64` on the transparent border paints a grey dashed
  line down the right and bottom edges. The fix is `-background white
  -alpha remove -alpha off` ahead of `-colors 64`. It showed up on 8 of the
  first 15 rtl-cdc diagrams. Check with
  `convert X.png -crop 1xH+(W-1)+0 -format '%[fx:minima.intensity]' info:`;
  anything well under 1 means a line.
- **Render with the directory's `regenerate_all_graphviz.sh`.** It writes
  PNGs at 150 dpi, palette-encodes them to PNG8, and excludes the `tIME`
  chunk so an unchanged source re-renders byte-identical. A new
  `assets/graphviz/` directory copies the one from
  `common_has/assets/graphviz/`.
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
  "timer window" arrow into the scheduler trapezium was the case.
- **Never draw two parallel edges between the same node pair for two
  classes.** Dot assigns their channels in an order you can't control, and
  `splines=ortho` ignores labels when it routes, so the labels drift and
  mislead. Use one edge with a combined label (`WR / RMW`). The same goes for
  taillabel/headlabel tricks: if a label doesn't land where you want it,
  change the edge structure, not the label.
- **Use point-node scaffolds when several crossings join the same node
  pair.** For example, three flows crossing the PHY bar shuffle channels and
  flip direction unpredictably. Route each crossing through its own invisible
  `shape=point` node in a pinned rank (`{ rank=same; ... }` plus an invisible
  spacer chain for order). Each crossing is then a distinct node pair, with a
  fixed direction and label placement. A leg through a point node leaves a
  hairline gap (ortho ignores `headclip`/`tailclip`), which is invisible at
  print scale.

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
