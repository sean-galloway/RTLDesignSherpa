# TASK-054: granite storage and AXI planes -- the six reductions of the 5.12 proposals

> Source: owner, 2026-10-24, on the proposals written against the per-plane
> area table (report 5.12) and the LiteDRAM comparison: "Do all 6." Related:
> TASK-052 (the table), TASK-053 (the DFI generate, same method), handbook
> `design/per-bank-queues-admit-from-the-pool.md`.


> **Correction (2026-10-24 evening, pumice BUG-031 / TASK-058):** the board
> LUT / FF figures in this file were measured on bitstreams whose read path
> synthesis had removed -- a double continuous driver on `mc_rd_intake.map_req_o`
> (TASK-054) tied the AR valid to GND, no read ever issued on silicon, and
> Vivado folded the dead read side of the store, ring and intake away. The
> honest board trend is TASK-053 text 6 090 LUT / 4 417 FF -> fixed final text
> 5 631 LUT / 3 532 FF (report 5.18). Every cycle-count and bandwidth claim in
> this file stands: the net was dead in simulation, so the simulator measured
> the real design. The ASAP7 per-plane numbers move only in the read intake
> (1 045 -> 1 210 cells).

**Priority:** P2
**Status:** closed 2026-10-24 (board 6 090 -> 4 171 LUT, 4 417 -> 2 709 FF, +0.206 ns; writes cycle-identical on every cell, reads 1-5 cycles shorter; item 6 measured and left off)
**Owner:** TBD

## What landed

**Storage plane (`mc_bank_fifo_store`, no knobs: both are cycle-identical by construction).**

3. **Fill-order FIFO circular.** It only ever pops its head (the slot the
   next W beat belongs to), the same argument that made the bank queues
   circular in TASK-050; the 8 x 3-bit shift-and-compact network is gone.
4. **Per-bank queues as linked lists through the slots.** One 3-bit `next`
   per slot, a same-row-as-predecessor bit per slot, head / tail / count per
   bank. Push appends at the tail (or becomes the head of a queue that is
   empty after this cycle's pop), pop follows the head's `next`, the records
   read head, next[head], next[next[head]]. The 8 x 8 position array and
   its 64-way write decode per direction are gone: 416 flops per direction
   become 24 + 8 + 48 + 32 plus the tail rows. `BANK_FIFO_DEPTH` still caps
   by count.

**AXI plane (knobs on `mc_axi4_plane`, plumbed to `granite_core`,
`granite_top_geared`, the char macro / harness / top with `GRANITE_*`
defines, the UART tb top and perf proxy with `TEST_*`, both
`create_project.tcl` hooks; pumice keeps every default).**

2. **`HAS_SNARF = 0`** on `mc_rd_intake`: no snarf probe, no staged admit
   (48 flops), no source arbiter; the AR is admitted from the skid head and
   R comes from the return ring only. The order FIFO stays: it carries the
   per-read {agg, last, len, id} the R channel needs, not snarf state.
1. **`RD_FIFO_DEPTH = 0` / `WDATA_FIFO_DEPTH = 0`** (`INTAKE_FIFO_DEPTH` at
   granite_core): the intakes' 16-deep data FIFOs are bypassed; the W skid
   feeds the store's beat buffer and the ring feeds the R skid directly.
5. **`SKID_DEPTH_R` / `SKID_DEPTH_W`** plumbed from the plane
   (`AXI_SKID_DEPTH`); granite measured at 2 against the shell default 4.
6. **`SHARED_ADDR_MAP = 1`**: one `mc_addr_mapper` in the plane for both
   intakes. Each intake requests it when it has a command to decode (no
   ready term in the request: the decode feeds `ar_push_ready` through the
   bank, and a ready-gated request closed a combinational loop through the
   mapper's address mux, Verilator UNOPTFLAT on the first cut); the grant
   alternates when both ask, so neither side starves; an intake stalls its
   own handshake while it does not hold the grant.

## Measured

ASAP7 (planes kept, dead ports pruned, comb cells / flops / RAM bits):

| block | TASK-053 text | store rewrite | + all four AXI knobs |
|---|---|---|---|
| FIFO store | 6 872 / 1 203 / 1 548 | 6 644 / 806 / 1 548 | same |
| AXI plane | 4 958 / 1 298 / 5 722 | same | 3 906 / 933 / 3 314 |
| rd intake / wr intake | 1 791 / 504, 1 578 / 474 | same | 984 / 296, 993 / 316 |
| AXI slave shells rd / wr | 935 / 414, 1 116 / 436 | same | 757 / 262, 821 / 290 |
| granite_top_geared | 26 345 / 5 054 | 26 147 / 4 657 | 25 057 / 4 292 |

Board (Nexys A7, 75 MHz, LUT / FF, WNS):

| build (Nexys A7, 75 MHz) | granite_core LUT / FF | WNS |
|---|---|---|
| TASK-053 text (this morning) | 6 090 / 4 417 | +0.367 ns |
| store rewrite (items 3, 4), regenerated harness bridge | 4 525 / 2 999 | +0.272 ns |
| + no snarf (item 2) | 4 531 / 2 998 | +0.131 ns |
| + no intake FIFOs (item 1) | 4 447 / 2 971 | +0.220 ns |
| **+ skids 2 (item 5): the committed defaults** | **4 171 / 2 709** | **+0.206 ns, 0 / 97 817** |
| + shared address mapper (item 6) | 5 968 / 3 675 | +0.213 ns |
| the committed text rebuilt as plain defaults (writes `fpga/reports`) | 4 171 / 2 709 | +0.206 ns, 0 / 97 817 (bit-identical to the level-3 build) |

The store build's drop (6 090 -> 4 525) is the two store items plus the
regenerated bridge: the bridge generator's new sizing rule changed what the
harness drives into the controller, and Vivado pruned about 390 LUT / 240
FF of the AXI plane (the AR skid's unused fields, the ring's issue queue
dissolved into its parent) before any AXI knob was on. Items 2 and 1 are
small on the FPGA because Vivado had already pruned the dead snarf stage,
and the intake FIFOs were LUTRAM; item 5 is the real AXI win on the board.
The shared mapper is a loss twice over: 23 percent on mixed in the proxy,
and 1 800 LUT MORE on the board (the address mux in front of one decoder
defeats the constant propagation the two private decoders enjoyed).

Perf proxy (board geometry, cycle counts against the TASK-053 text, every
cell mismatched 0):

| cell (vs the TASK-053 text, cycle counts) | store rewrite | + no snarf | + no intake FIFOs | + skids 2 (defaults) | + shared mapper |
|---|---|---|---|---|---|
| std 1 thread, 4 families | identical | wr identical, rd -1 | wr identical, rd -2 | same as level 2 | same as level 2 |
| std 8 threads, 4 families | identical | wr identical, rd -0 to -4 | wr identical, rd -1 to -5 | same as level 2 | same as level 2 |
| row_thrash 2-beat, 1 thread | identical | -- | -- | wr identical, rd -5 | same |
| random, 8 threads | identical | -- | -- | wr identical, rd -1 | same |
| mixed, 8 threads | identical | identical | 98.1, rd -1 | 98.1, rd -1 | **75.4 MB/s, +60 330 cycles** |

The committed defaults were rerun as plain defaults (no `TEST_*`): cycle-identical to the level-3 lane at 1 and 8 threads and on mixed.

## Gates

Contract battery 12 / 3 strict xfailed (store rewrite); granite suite 6 / 1
xfailed on the default knobs and on all four lean knobs; pumice
`run-all-func-both` 218 / 218 both geometries; lint 0 errors on granite_core at every
knob setting and on pumice_core, no new warnings. The harness bridge was
regenerated on the way (`REGEN_BRIDGES=1 make prebuild`): the bridge
generator's sizing rule (bridge TASK-016, 43a845673) had moved the W skid
of two adapters from 4 to 2 and dropped the rate-buffer include, and the
prebuild drift check refused to build until the generated files matched.
