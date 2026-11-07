# pumice / granite: structures to rework for the FPGA target

Date: 2026-11-05. Scope: `projects/components/mem-ctrl-ip/common-ip/rtl` as built by
pumice (`research-ip/pumice-ddr2-lpddr2`, build-perf, FR-FCFS arbiter on the CAM store;
the passing board build is a **50 MHz** controller clock, it fails by 5.6 ns at 75 MHz
and 9.0 ns at 100 MHz) and granite (`product-ip/granite-ddr2-lpddr2`, targets/granite,
bank pick on the per-bank FIFO store; passes 100 MHz by 0.004-0.021 ns). Target: xc7a100t-1, 64-bit AXI, 8-bit ids, DFI 1:2,
DDR2-400 (one DRAM command slot per host cycle at most).

Method: five parallel read-only reviews (pumice CAMs, scheduler plane, granite store and
pick, AXI/DFI planes, Vivado report mining), one out-of-context Vivado synthesis of
`mc_storage_plane` at the board generics, plus a census of every unpacked array in the
tree and the always block that writes it. Detail per slice is in `01_..04_*.md` beside
this file; every claim there carries a file:line. Nothing in the repo was modified.

Board numbers used throughout. Granite: `utilization_hier.txt` of the 2026-10-29 build.
Pumice: a hierarchical report generated this session from the routed checkpoint
(`scratchpad/fpga_reports/pumice_util_hier.txt`; same controller source and parameters,
7+7 engine harness, so harness numbers are not comparable).

| Block | LUT | FF | Note |
|---|---|---|---|
| granite_core | 5,456 | 3,766 | 2 of 135 RAMB36 used on the whole chip |
| mc_bank_fifo_store (16 bank queues inside) | 2,204 | 1,524 | queues alone ~1,770 LUT |
| mc_scheduler_plane (granite) | 1,753 | 875 | bank_pick 726, bank_timers 568, page_policy 203, global_timers 165 |
| mc_axi4_plane (granite) | 1,097 | 1,176 | rd_return_ring 506 (was 248 on 10-17) |
| pumice_core | 11,257 | 5,936 | 2.06x granite_core |
| mc_scheduler_plane (pumice) | 4,970 | 2,467 | **mc_cmd_arbiter 3,426 / 1,139**, bank_timers 913, page_policy 367 (744 FF of telemetry) |
| mc_storage_plane (pumice) | 3,710 | 1,492 | mc_wr_data_cam 2,329 (fill/snarf/drain FIFOs 715 of it), mc_rd_cmd_cam 1,382 |
| mc_axi4_plane (pumice) | 2,078 | 1,617 | rd_return_ring 958 (ring 635 + issue_q 324) |
| OOC synth of mc_storage_plane, merge on / off | 1,880 / 1,407 live | ~1,570 / ~1,340 | head records 5,107 LUT more if BANK_PICK were paired with the CAM |
| gaxi_skid_buffer, 49 instances chip-wide | 6,366 | 6,430 | 17% of the chip, ~1 LUT per flop |
| whole chip, async-reset flops vs sync | 23.8k vs 10.9k | | zero reset-free flops; the 10.9k sync flops are PeakRDL/harness |
| whole chip, pumice | 47.9k LUT, **95% of slices occupied** | | 2 of 135 BRAM tiles; 2,126 LUTs as distributed RAM |

## 1. The seven ASIC habits, and what the FPGA wants instead

### H1. Content-addressable match as the default lookup
Every "find the entry that ..." question is answered by comparing a key against every
entry every cycle. Where it shows up, with the cost:

- pumice `mc_wr_data_cam` / `mc_rd_cmd_cam`: the window itself (inherent to the design,
  ~1,400 LUT at N=8, fine at 75 MHz with merge off; 20k LUT and fails 13.3 ns standalone
  at the macro default N=16, `ddr2_char_macro.sv:92`).
- the TASK-060 write/read combiners in pumice (`mc_wr_data_cam.sv:337-430`,
  `mc_rd_cmd_cam.sv:198-214`): three 8x34-bit scans plus id scans plus N^2 youngest
  picks. Measured +473 LUT, and the same-day board builds went from WNS +0.029 ns to
  -5.630 ns with the two CAMs owning 34% of all failing endpoints.
- the granite merge CAM (`mc_bank_fifo_store.sv:497-528, 919-937`): ~570 LUT in the store
  plus ~850 LUT of shadow tracking in `mc_rd_return_ring` (two full 64-entry 6-bit
  equality sweeps per cycle, `:147-151, :284-285`). The ring body doubled (106 to 373
  LUT) in the one commit that added it.
- snarf (read-your-own-write forward, `mc_wr_data_cam.sv:456-487`): 8x34-bit match whose
  result leaves the plane and re-enters it in the same cycle through `mc_rd_intake` into
  the rd CAM's allocation. All 461 rd_cam failing endpoints.
- `mc_bank_head_records` (`:92-168`): 56 pairwise age compares, 64 masked popcounts and 16
  eight-way priority muxes per instance. 2,554 LUT each at N=8, 8,000 at N=16. Dead on
  the board, but it is exactly what pairing BANK_PICK with the CAM backend would cost.
- `mc_cmd_arbiter` population matrices (`:1031-1060`): 16x16 bank+row equality twice
  plus 32 popcounts, recomputed every cycle for the `col_sel/row_sel` pick modes.
  ~900-1,700 LUT.

FPGA shape: order is kept by pointers (per-bank FIFOs, AW-order queues), facts are
stored as bits at insert (hit, same-row-behind, sibling-exists), and the only compare
left is one registered candidate against one registered key. Granite's bank FIFO store
is already this shape in principle (`per-bank-queues-admit-from-the-pool` note), so the
merge CAM bolted onto it reintroduced the habit the store was built to remove.

### H2. Recomputing per cycle what could be stored at insert
- `mc_cmd_arbiter` per-entry classify (`:832-909`): 16 entries each do an 8:1 x 14-bit
  open-row mux and a 14-bit compare, plus three speculative row compares. ~900-1,200 LUT.
  `mc_scheduler_plane` then does the same compare a second time for the open-row demand
  vector (`:397-421`, ~500 LUT). Granite stores `hit` in the record and reads a bit.
- bank-queue `tail_row` registers and the 16 x (8:1 x 13-bit) hit muxes in the granite
  store (`:459, :866, :1333`): carry the row in the queue entry and the head register
  holds its own row.

### H3. Many small controllers instead of one memory with regions
- 16 `gaxi_age_fifo_sync` bank queues, each 8 deep x 4 bits with its own two pointer
  counters, full/empty logic and three asynchronous read ports: 1,770 LUT, 80% of the
  store and 32% of granite_core, for 128 four-bit entries that are popped at most once
  per cycle in total. The store already keeps a registered per-bank count because the
  FIFO's own count would close a timing loop (`:454-457`), so occupancy exists twice.
  Three of the eight worst paths on the board end in these FIFO controllers.
  FPGA shape: one RAM64M per direction (4 LUTs) holding all eight banks' entries, plus a
  3-entry head shift register per bank (head, peek1, peek2 are exactly what the record
  builder reads). ~400 LUT + 290 FF total. Saves ~1,300 LUT and takes the FIFO
  controllers off the fire cone, making POP_REG moot.
- 8 `mc_bank_timer` instances each redo the same CSR arithmetic (`f_ld` saturating
  subtracts, `t <= LA+1` compares, LA_AP max+add): 568 LUT / 352 FF. Hoisting the
  CSR-derived constants saves 150-200 LUT and takes the TIMINGS CSR fan-out off the
  granite worst path (CSR tRTP field -> timer fold -> fire -> ring FIFO flag is the
  0.021 ns path). SRLC32E delay lines with the CSR value as the dynamic tap replace
  four of the five counters per bank (-250..-300 LUT); the runtime-CSR timings do not
  force the counter shape.

### H4. Flops where the fabric has RAM
The array census (every unpacked array in common-ip and the block that writes it) shows
the pattern precisely: the payload RAMs (`r_mem`, `r_strb` in the CAM and store,
`r_mem` in the ring, every `gaxi_fifo_*` memory) are reset-free and infer LUTRAM/BRAM
correctly. Everything else, including fields that are never reset, is written inside an
`ALWAYS_FF_RST` block, and `ALWAYS_FF_RST` is unconditionally async-assert
(`reset_defs.svh:55-64`). Vivado will not infer RAM from an array written in a process
with an async reset branch (the handbook's `sram-and-memories` note already records
this failure from `axi_perf_latency_hist`, 2026-10-29).

- granite slot descriptor arrays (`r_wr_*`, `r_rd_*`, `mc_bank_fifo_store.sv:354-371,
  859-864`): ~620 FF plus ~300 LUT of 8:1 read muxes. Payload (row, col, id/ticket) is
  written once at admit and could be RAM32M indexed by slot in a reset-free block.
- `mc_rd_return_ring` `r_src` table (`:131, :269-274`): 64 x 6 flops reset to `TW'(i)`,
  a value that is dead because every allocation rewrites it; 384 async-set flops that
  also keep the table out of LUTRAM. `r_resp` (128 FF) is dead logic (the aligner only
  ever produces OKAY).
- `gaxi_skid_buffer` (`rtl/amba/gaxi/gaxi_skid_buffer.sv:128-170`): every data bit is a
  4-way mux (new / shift / clear-to-zero / hold) on an async-reset flop, with the vacated
  slot explicitly zeroed. 6,366 LUT / 6,430 FF across 49 instances, ~1 LUT per flop.
  The canonical two-register skid (output reg + one skid reg, no data reset, no shift)
  is ~0.5 LUT per flop. This is the single largest chip-wide lever: ~3k LUT, one
  primitive, zero functional change at DEPTH=2 (every board instance is DEPTH=2).
- `r_strb` byte-OR read-modify-write (`mc_bank_fifo_store.sv:851-853`,
  `mc_wr_data_cam.sv:1011-1013`) exists only for the merge; without it the strobes go
  back into the 72-bit BRAM word as the entry store already does.

### H5. Same-cycle cones across plane boundaries
The plane contract (`plane-boundary-registered-snapshots`) is registered snapshots in,
one decision out. The ASIC habit is to reach for the live term:

- `mc_cmd_arbiter` STAGE-1b result gates STAGE-1a's mask in the same cycle
  (`:474-520, :565-599`): arg_sel -> bank decode -> guard -> classify -> qos tree, ~20
  LUT levels. The board's worst pumice path (`r_rd_pop -> r_wr_col_q`). It cannot reach
  100 MHz without registering the 1b shadows (bank_pick's `r_stale_*` is the worked
  example, `mc_bank_pick.sv:656-671`).
- scheduler fire cone -> CAM `commit_valid_i` -> merge match -> `ins_ready_o`,
  `wd_ready_o`, every entry CE and the `r_strb` write data (`mc_wr_data_cam.sv:396-430`):
  1,105 of the 1,120 wr_cam failing endpoints start at bank-timer flops.
- `snarf_hit_o` round trip through `mc_rd_intake` into the rd CAM allocation (H1).
- `ins_merge_o` / `ar_merge_o` combinational from the AXI AR inputs through 8x34-bit
  compares into the ring's allocation in the same handshake (`mc_rd_cmd_cam.sv:212-213`,
  `mc_bank_fifo_store.sv:919-937`).
- `gaxi_fifo_sync` full/empty from NEXT pointers (`:122-125`): the producer's entire
  valid cone lands on the flag flop. Granite's WNS path ends at
  `u_issue_q/fifo_control_inst/rd_empty_reg`. The FIFO offers no timing isolation.
- `mc_axi4_narrow_pack` (committed 11-03, not yet in a board build): AW valid gates W
  ready in the same cycle, AW/AR fields rewritten with a 9-bit variable shift and add in
  zero cycles, 3-4 LUT levels added to every host channel. No narrow traffic exists on
  the board; `NARROW_EN=0` for the board netlist.
- `w_out_ready` as the clock enable of ~400 arbiter flops, fed by `w_ap_sibling` (16 x
  17-bit compares) and `w_col_row_ok` (`mc_cmd_arbiter.sv:468, :750-770`).

Why the one-cycle loop is not worth it here: at DFI 1:2 the plane emits at most one
command per host cycle, which already saturates the command slot and the data bus at
the board geometry (the arbiter's own comment, `:1475-1480`). Pipelining that keeps one
pick per cycle costs nothing on bank-interleaved streams; it costs one cycle per
dependent hop (ACT->COL, PRE->ACT, 2 host cycles each at DDR2-400) on single-bank
streams only, and bank_pick already pays that correctly with register-only hints.

### H6. Arithmetic in the ASIC idiom
- free-running 16-bit age per CAM entry with a 16-bit subtract and compare each
  (`mc_wr_data_cam.sv:183-231`, `mc_rd_cmd_cam.sv:161-173`): ~190 LUT + 144 FF per CAM
  for a 1-bit `age_exceed` survivor on the base build. An 8-bit prescaled saturating
  counter per entry is ~6 LUT + 8 FF.
- FAST_RD_RELEASE `S_MAX` max tree over 16 CSRs (`mc_scheduler_plane.sv:1141-1175`):
  ~180 LUT + 98 FF computing a value that is constant during traffic. One software CSR
  or a 16-cycle serial scan (~12 LUT).
- tFAW 4-slot sliding window with two argmin searches (`mc_global_timers.sv:131-215`):
  an SRL of length tFAW plus a 3-bit in-window count gives the same `ok` in ~6 LUT.
- two `mc_addr_mapper` barrel shifters on a live CSR (`:96-120`): 32-bit shift right,
  mask, shift left, for `bank_lsb` which changes only at init. Precompute the bit
  selects on the CSR write, or make it a build constant on the board.
- ring index arithmetic written as 32-bit multiply-add (`mc_rd_return_ring.sv:186-187,
  250-251`) for what is a concatenation at any power-of-two beats-per-burst.
- pool age in the granite store if HAS_AGE is ever turned on: every entry in all 16
  queues decrements on every retirement, a 16-leaf max tree and 16 wait counters
  (~700-900 LUT / ~800 FF estimated). The FPGA form is a timestamp written with the
  entry and one subtract-compare per registered head.

### H7. Features built for a benefit the board cannot show
- write/read combining (both controllers): on this board one 64-bit AXI beat is one
  DRAM burst, so the only merge opportunity is a host that splits one access into two
  back-to-back narrow writes. The owner's A/B had merge-off within 2% on 171 of 180 cells.
  Combine adjacent pairs at the intake with one registered 34-bit compare against the
  last pushed AW if the half-width cell matters; otherwise `*_MERGE_EN=0` on the FPGA
  SKU. Removes H1's two largest items, the strobe RMW, the second-B queue, the ring
  shadow sweeps and the whole pumice merge-era timing failure.
- snarf: AXI4 does not require a read to observe a write before its B, and B is strobed
  at drain evict after which the entry is gone, so no required ordering case is served.
- runtime QoS (`sched_qos_en_i`) means the six `qos_top` trees are always built
  (~300-400 LUT); granite leaves them unconnected. Build-time `HAS_QOS`.
- `col_sel/row_sel` population pick modes are the only readers of the N^2 population
  matrices (H1).

## 2. Ranked rework list

Savings are structural estimates unless marked measured. The granite core projection is
5,456 -> roughly 3,000 LUT at the same NUM_ENTRIES and depth; pumice depends on whether
FR-FCFS stays.

| # | Item | Files | Saving | Risk | Note |
|---|---|---|---|---|---|
| 1 | Two-register `gaxi_skid_buffer` without data reset or shift | `rtl/amba/gaxi/gaxi_skid_buffer.sv` | ~3k LUT chip-wide (measured 6,366 today) | low | one primitive, 49 instances, DEPTH=2 everywhere on the board; a separate small FIFO form for DEPTH>2 |
| 2 | Bank queues as one RAM64M per direction + 3-entry head shift registers | `mc_bank_fifo_store.sv:1107-1157` | ~1,300 LUT (1,770 measured today) | medium | removes the duplicated occupancy state and the FIFO controllers from the fire cone; records read the same three positions |
| 2b | Move every storage array out of `ALWAYS_FF_RST` into a reset-free `always_ff` with a separate small valid vector (the synth log names 35 pumice / 30 granite arrays dissolved for this one reason, including the BRAM prefetch skids and all per-entry tags) | CAM, store, ring, skid | several hundred LUT of write-decode and read-mux, thousands of FF to LUTRAM | low | mechanical; the pattern already exists for `r_mem` in the same files |
| 3 | Merge off on the FPGA SKU; adjacent-pair coalesce at intake if wanted | `STORE_MERGE_EN`, `WR_MERGE_EN`, `RD_MERGE_EN` | granite ~570 store + ~850 ring LUT; pumice +473 LUT measured and the -5.6 ns | low | parameter first, then delete the strobe RMW, second-B queue, FO doubling, ring shadow sweeps |
| 4 | Ring shadow tracking: evaluate shadow readiness at fetch, drop `r_src` reset value, delete `r_resp` | `mc_rd_return_ring.sv:130-151, 269-320` | 150-250 LUT, 384 async-set flops | low | exact: the source is pinned until its shadows fetch, so readiness can be read at fetch instead of broadcast at return |
| 5 | Slot payload into reset-free LUTRAM; row carried in the queue entry | `mc_bank_fifo_store.sv:354-371, 859-864, 1333` | ~300 LUT, ~600 FF -> ~60 LUTRAM | medium | removes the 16 hit muxes and the tail_row registers |
| 6 | Hoist CSR-derived timer constants out of the 8 `mc_bank_timer` instances | `mc_bank_timer.sv:147-240` | 150-200 LUT | low | takes the TIMINGS CSR off granite's worst path; both cores |
| 7 | SRL delay lines (or 5->3 counters) in bank timers; SRL window for tFAW | `mc_bank_timer.sv`, `mc_global_timers.sv` | 250-400 LUT | medium | `preblk` must stay a counter (retriggers within its window); range 31 matches today's TW=5 saturation |
| 8 | FAST_RD_RELEASE `S_MAX` as a CSR or serial scan | `mc_scheduler_plane.sv:1141-1175` | ~180 LUT, 98 FF | low | both cores |
| 9 | Snarf: delete, or register `snarf_hit_o` one cycle | `mc_wr_data_cam.sv:456-487` | 150-250 LUT, all 461 rd_cam failing endpoints | low | pumice |
| 10 | CAM ages as 8-bit prescaled counters | `mc_wr_data_cam.sv`, `mc_rd_cmd_cam.sv` | ~380 LUT, ~290 FF | low | pumice |
| 11 | Register `timeout_pre_req/bank` in page policy; FIFO flags from registered pointers | `mc_page_policy.sv:543-557`, `fifo_control.sv` | timing only | low | idle timer tolerates a stale cycle; the owner already did this for `open_row_demand` |
| 12 | `NARROW_EN=0` on the board netlist; register the AW/AR rewrite if kept | `mc_axi4_plane.sv:69`, `mc_axi4_narrow_pack.sv` | 250-350 LUT avoided | low | not yet measured on a board |
| 13 | Address mapper: constant `bank_lsb` on the board or registered mask decode | `mc_addr_mapper.sv:96-120` | 100-200 LUT across two instances | low | hierarchy attribution is unreliable here |
| 14 | pumice arbiter, if FR-FCFS stays: register the 1b shadows; move hit / same-row-behind / sibling into the CAM as registered bits; `col_sel/row_sel/QoS` build-time | `mc_cmd_arbiter.sv` | ~2k of its measured 3,426 LUT; the 75/100 MHz blocker | high | (a) alone is what the clock needs. The alternative is `SCHED_CORE=BANK_PICK` on the FIFO store, which is granite |
| 15 | `mc_bank_pick` arbiter 16->8 restructure (pre-register the dir/class choice, one 8-wide rotor) | `mc_bank_pick.sv:770-830` | 150-250 LUT of 726 | high | every term cites a board cell; A/B on the proxy families, do last |
| 16 | Make N=8 the macro default for the CAM backend | `ddr2_char_macro.sv:92` | avoids 20k LUT / failing 13.3 ns at N=16 | none | the harness override is load-bearing today |

## 3. Correctness items found in passing

These are not FPGA-shape items but they came out of reading the same code and should be
filed:

1. **B responses can be dropped.** `mc_wr_intake.sv:445-459`: `wr_done_valid_i` has no
   ready, the 4-deep B FIFO's `wr_ready` is unconnected, and `gaxi_fifo_sync` writes
   only on `wr_valid && wr_ready`. With 8-16 write slots and a host holding `bready` low
   for more than four completions, Bs are silently lost. Not reachable with the char
   engines (bready always high). Verified independently. The AW-order B release queue
   proposed for granite ISSUE-001 (below) fixes both at once.
2. **granite ISSUE-001 cheapest fix**: release Bs in AW order from an 8-entry id queue
   pushed at admit, with a per-slot `pos` and a `drained` bit set at the drain's last
   beat (~4 LUTRAM + ~40 FF + ~25 LUT). Stronger than per-id order, no id compare
   anywhere, no serialization of same-id writes across banks (which the "hold the
   younger write" option would cause), slot still freed at fetch-last.
3. **DFI CDC token and data cross on separate synchronizers** (`mc_dfi_cdc.sv:105-188`,
   async branch only): the comment claims one synchronizer; there are two independent
   2-flop Gray crossings, which can resolve a cycle apart, so a token can lead its data
   and the serializer drives `dfi_wrdata` one DFI cycle late. Not reachable on the board
   (DFI_CDC_EN=0, both boards tie `dfi_clk` to the host clock). Carry `last` in the data
   FIFO payload and count staged bursts on the dfi side.
4. **No `ASYNC_REG` attribute** on `glitch_free_n_dff_arn.sv:339-350` synchronizer
   flops; it exists only in a comment. Placement may split the stages and `report_cdc`
   cannot classify the crossings safe.
5. **Same-clock branch samples across named domains without a check**
   (`mc_dfi_cdc.sv:357-364`): legal only because both clock ports are one net; a build
   with DFI_CDC_EN=0 and separate clocks is a silent CDC violation.
6. `r_rd_q` driven from two `always_ff` blocks for different bit ranges
   (`mc_bank_fifo_store.sv:848, 853`): legal, a portability smell.
7. `mc_head_rec_t` carries 32 constant-zero bits and an 8-bit slot for a 3-bit value
   (`mc_common_pkg.sv:149-151`); every `PTRW'(slot)` truncation is a place a wider
   NUM_ENTRIES silently changes behaviour.

## 4. Keep as-is

- `mc_rd_return_ring` core: BRAM payload + ticket FIFO + valid vector + fetch pointer +
  2-deep prefetch skid. It reorders by write address, not by search. Only the shadow
  tracking (item 4) and the index arithmetic need touching.
- the write-beat BRAM with 1-cycle read, 2-deep skid and credits (store and CAM).
- `mc_bank_pick`'s three-stage shape: flops in, decode, rotor on one-hot vectors with
  registered stale masks, fire with live JEDEC timer read. The right FPGA pick core.
- the registered per-bank record contract and the per-slot h1/h2 flags.
- `mc_global_timers`' single next-state with registered `ok` outputs; bank timers'
  EVT_REG/SET_LAG, live row image, TW=5 saturation.
- `gaxi_fifo_sync` / `gaxi_fifo_async` memories (reset-free, LUTRAM-inferred); the DFI
  command path, formatter, serializer and aligner (43 LUT total on the board).
- `mc_axi_burst_chopper`, `mc_wr_splitter`, the small find-firsts, the refresh
  controller, the AR stage register and the depth-0 FIFO bypasses.
- `mc_xddr2_entry_store` + `mc_bank_head_records` only as the simulation reference
  backend; never build them for the FPGA.

## 5. Strategic read

Granite's bank-FIFO-store plus bank-pick is the FPGA microarchitecture; its remaining
cost is in how the FIFOs and payload are implemented (items 2, 5) and in the merge CAM
that was bolted back on (items 3, 4). Pumice's CAM window plus FR-FCFS arbiter is an ASIC
microarchitecture: at N=8 and 75 MHz it closes with merge off, but every one of its
levers (N, merge, snarf, QoS, population modes) scales as N^2 and it has a same-cycle
feedback loop that will not make 100 MHz. The recommendation is to converge the FPGA
product on granite's shape with the reworks above, keep pumice as the research core at
N=8 with merge and snarf off, and apply the cross-cutting fixes (skid buffer, timers,
S_MAX, reset-free payload arrays) to both since they share `common-ip`.

## 6. What the Vivado reports say (detail in `05_vivado_report_mining.md`)

Build facts. The pumice `build-perf/fpga/reports` that passes (+0.029 ns) is a 50 MHz
controller clock. At 75 MHz pumice fails by 5.630 ns (4,221 endpoints) and at 100 MHz by
9.005 ns (22,755 endpoints), with 95% of slices occupied and a mean route share of 86%
on failing paths. Granite's `reports/` (+0.299) is 75 MHz; the 10-28 and 10-29 builds
pass 100 MHz by 0.004 and 0.021 ns. The 10-17 granite hierarchy report is the old
entry-store architecture (core 8,340 LUT, entry store 4,725); the FIFO-store rework cut
the core to 4,918 on 10-26, and it has grown back to 5,456 by 10-29 (bank_timers +175,
rd_ring +141 LUT / +384 FF, fifo_store +116, page_policy +53).

Pumice at 100 MHz, controller failing endpoints by block: mc_wr_data_cam 1,171 (worst
-7.44), mc_rd_return_ring 944 (-4.50), mc_cmd_arbiter 914 (-9.005), page_policy 849,
mc_rd_cmd_cam 489, bank_timers 428. Every path worse than -6.2 ns is controller, and the
60 worst are one cone: arbiter STAGE-1a read-side slot pick (`rd_{act,col,pre}_s` over
`r_rd_pop` popcounts and `r_rd_older`) -> bank of the picked read -> read candidate mask
-> **write** candidate mask `r_wr_{pre,col,act}_q`, 22-24 LUT levels, 18.8 ns of which
15.5 ns is route. The same cone is 27 levels and the only thing holding the 50 MHz build
(`r_rd_pop_reg[6][1] -> r_wr_pre_q_reg[5]`, 19.78 ns, +0.029). At 0.124 ns per LUT plus
0.6 ns per net uncongested, 23 levels is about 17 ns; placement cannot fix it.

Cross-plane flows that fail (path counts): bank_timers -> wr_cam 1,114 (the tRP
countdown `r_rp` feeding per-entry eligibility down to the BRAM write port, 16-18
levels); wr_cam `r_fdone` -> rd_ring `r_src` 811; wr_cam -> rd_cam 463 (snarf);
bank_timers -> page_policy 460 (32-bit telemetry counters); bank_timers -> arbiter 451.

Granite's knife edge is one block: `mc_bank_pick`'s effective-winner mux (`r_hold`,
fanout 138) into `r_stale_pick` / `r_pick_cls`, 11-14 levels with 7-10 ns of route, the
worst path in every granite build since 10-27. The 10-29 build adds a second cone: the
CSR tRTP field -> bank-timer compare -> bank_pick fire -> issue and bank FIFO full/empty
flags, 13 levels, +0.021.

RAM inference. The synth logs name the mechanism exactly: 35 (pumice) / 30 (granite)
arrays were "dissolved into registers", every one for the single reason `RAM is
sensitive to asynchronous reset signal`. Among them: the BRAM prefetch skid arrays beside
every write-data BRAM (`r_sk_*` in the CAM and the store), the CAM's per-entry `r_ptr`,
`r_mgid`, `r_last`, `r_id`, `r_ticket`, and the FIFO store's `r_wr_bank`, `r_wr_id`,
`r_rd_bank`, `r_rd_ticket`. Only four arrays reached BRAM, two of them 8-entry (the CAM's
8x64 and the store's 8x72, which Vivado itself says belong in LUTRAM). 135 BRAM tiles,
2 used, while 2,126 LUTs are distributed RAM (1,432 of them two harness SRAMs that would
each fit one tile) and tens of thousands of flops hold queue state.

Harness, for completeness: the failing-endpoint count in every pumice build is set by
the harness (17,183 of 22,755), chiefly one CSR write strobe fanning out to 3,897 field
flops, the latency-histogram timestamp arrays in flops (2,048 endpoints, the
`sram-and-memories` note case), and 3,399 recovery checks on the async reset net. The
controller sets the depth.
