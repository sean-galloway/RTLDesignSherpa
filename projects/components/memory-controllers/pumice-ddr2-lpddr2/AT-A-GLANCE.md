# pumice — at a glance

A DDR2/LPDDR2 memory controller. One index page: every feature area, 1-3
bullets each, so you can find the right file without reading the tree. The one
section that goes deeper is **Runtime modes**, which gives 2-3 bullets per
MODE — that axis catalogue is the characterization surface, and the whole point
of it is choosing between the modes.

Depth lives elsewhere and is linked per section — this page is a map, not a
second copy. Authority order: `/GLOBAL_REQUIREMENTS.md` > the handbook
(`vault/handbook/INDEX.md`) > the uarch specs in `rtl/*.md` > this page.

---

## The shape of it

`pumice_top` -> `pumice_core` -> **three layers**, host side to DRAM side:

    AXI4 host ──> pumice_axi4_ifc ──> pumice_mem_cmd_scheduler ──> pumice_dfi_layer ──> PHY
                  (intakes + CAMs)     (arbiter + timers + refresh)   (the ONE CDC)

* **One clock crossing in the whole controller**, inside `pumice_dfi_layer`.
  Everything host-side runs on `aclk`, everything PHY-side on `dfi_clk`.
* **FSM-free by design.** The split/aggregate path carries `agg`/`last` in
  the CAM rather than a state machine; the arbiter is a combinational picker
  with registered feedback.
* One burst length per instance, decoded from the mode register at init —
  the same RTL does DDR2 BL4 and DDR3/DDR4 BL8.

---

## Layer 1 — AXI4 front end (`rtl/macro/pumice_axi4_ifc.sv`)

Spec: `rtl/PUMICE_AXI4_IFC_UARCH.md`

* **`pumice_wr_intake` / `pumice_rd_intake`** — dumb 1:1 AXI intakes. Decode
  AW/AR into `{rank,bank,row,col}`, pass W beats through unchanged, and own
  the B and R channels back to the host.
* **`pumice_wr_data_cam` / `pumice_rd_cmd_cam`** — where a transaction lives
  between its address handshake and retirement. The write CAM holds data in
  an SRAM and gates B on `agg && last` (one response per *original* burst);
  the read CAM reorders returns into AR order and collapses `RLAST`.
* **`pumice_axi_burst_chopper` + `pumice_wr_splitter`** — split a host burst
  into fixed-BL sub-commands with no FSM. The splitter carries no B channel
  by design; aggregation is the CAM's job.
* **`addr_mapper`** — flat AXI address to `{rank,bank,row,col}` under ONE
  knob, `ADDR_MAP.bank_lsb`. Row/rank positions are invariant; only the bank
  field slides (ROW_MAJOR / INTERLEAVE / XOR-hash are settings, not schemes).

## Layer 2 — command scheduler (`rtl/macro/pumice_mem_cmd_scheduler.sv`)

Spec: `rtl/PUMICE_MEM_CMD_SCHEDULER_UARCH.md`

* **`pumice_cmd_arbiter`** — the pick core. Bank-parallel activate, open-page
  bank timers, and per-cycle selection of ACT / column / PRE / REF, emitting
  an abstract command stream to a FIFO.
* **`pumice_bank_timers` + `global_timers` + `bank_timer`** — JEDEC "safe"
  tracking per (rank,bank) and controller-wide (tFAW, tRRD, bus turnaround).
  No state machines; each is a countdown that answers "legal now?".
* **`refresh_ctrl`** — tREFI accounting with JEDEC +-8 postpone/pull-in
  credits, drain bursts, and a REFpb bank rotor mirroring the device's
  internal counter. `refi_reload_i` forces an immediate counter reload (DV).
* **`init_sequencer` + `mode_register` + `powerdown_ctrl`** — full JEDEC
  post-reset bring-up, per-rank MR shadow with live decode, and idle-detect
  power-down.
* **`pumice_cmd_history_checker`** — a scoreboard, not datapath: audits the
  issued command stream against JEDEC same-bank sequencing.

## Layer 3 — DFI layer (`rtl/macro/pumice_dfi_layer.sv`)

Spec: `rtl/PUMICE_DFI_LAYER_UARCH.md`

* **`pumice_dfi_cdc`** — the single controller<->PHY crossing. Async FIFOs
  for command, write data and read data; everything else is same-domain.
* **`pumice_dfi_cmd_path` + `dfi_cmd_formatter` + `dfi_signal_pack`** — turn
  an abstract `dram_op_e` into the multi-phase DFI v2.1 bus, including
  runtime `rd_phase`/`wr_phase` placement to match the PHY's contract.
* **`pumice_dfi_wr_serializer` + `pumice_dfi_rd_aligner`** — drive write data
  at `t_phy_wrlat`, and place each read's `rddata_en` window at its OWN
  fire + `t_rddata_en` (a stateless delay line, so tCCD-paced reads do not
  collapse — that collapse was a real silicon read failure).

---

## Runtime modes — three independent axes (PUMICE-006)

All CSR-selectable, all **encoding 0 = build default and bit-identical**, each
mutation-proven, all 80 paging x scheduling combinations swept by
`perf_paging_sched_cross`. Rationale and paper citations live in
`docs/design-requirements.md`; free-running telemetry for all three axes lands
in `PAGE_STATS_*` / `SCHED_STATS_*` / `REF_STATS_*` (0x148-0x15C).

The axes **compose by narrowing, not by interacting**: `order_mode` decides who
is a candidate at all, `row_sel`/`col_sel` decide which candidate wins, and
`access_pref` decides which class of the survivors is served. That is why the
cross sweep moves one knob at a time instead of taking a 648-point product.

### Axis 1 — scheduling (`pumice_cmd_arbiter`, `SCHED_POLICY` @ 0x068)

#### `order_mode` — which references may drive a pick

**`fr_fcfs` — `order_mode` = 0 or 2 (build default)**

* Among references whose DRAM timing and resources are already free, a
  row-hit-ready reference wins; oldest breaks the tie.
* Costs a ready-check plus one age compare — no reorder machinery. It is what
  the class masks compute natively, so it is the mask the other modes narrow.
* The paper's baseline gain: roughly +25% bandwidth over strict arrival order.

**`in_order` — `order_mode` = 1**

* Only the single oldest un-issued reference across both CAMs may drive any
  pick. No lookahead, so a row miss stalls everything queued behind it.
* Implemented as a mask AND rather than a second chain: head-of-CAM comes from
  the age-order matrix, and the losing CAM's three class masks are zeroed.
* Between the CAMs the older head wins on a relative-age compare — both CAM age
  counters free-run from reset so the values share an epoch, tie goes to read.
  Use it as the latency-floor reference point in a sweep, not as a policy.

**`age_threshold` — `order_mode` = 3 (with `SCHED_POLICY.age_thresh`)**

* FR-FCFS until any candidate's age crosses `age_thresh` (MC cycles / 16);
  from then on every class narrows to boosted entries, so an aged reference's
  PRE outranks a fresh row-hit and starvation is bounded.
* The CAMs export a per-entry 1-bit aged flag, so numeric ages never cross the
  CAM boundary — the arbiter only ever compares single bits.
* The boost keys off a boosted entry's EXISTENCE, not its momentary candidacy:
  a boosted PRE stuck behind its bank's 2-cycle guard must still engage the
  narrowing, or the competing column stream re-arms that guard forever and the
  aged entry starves on its own trigger condition.

#### `row_sel` / `col_sel` — which candidate wins inside a class

`row_sel` steers the ACTIVATE pick, `col_sel` the COLUMN pick; both take the
same three values, and precharge picks stay strictly oldest in every mode.

**`oldest` — `row_sel` / `col_sel` = 0 (build default)**

* Pure age-order matrix: an entry wins iff no other masked entry is older.
  Identical to the pre-mode `arg_oldest` pick, bit for bit.
* The population compare is bypassed rather than tied, so this is also the
  cheapest of the three selects.
* It stays the tie-break underneath the other two, so age order never fully
  leaves the pick.

**`most_pending` — `row_sel` / `col_sel` = 1**

* Picks the candidate whose {bank,row} has the MOST schedulable entries pending
  in its own CAM: drain the hottest row, maximizing accesses per activation.
* `pop[i]` is an 8x8 same-{bank,row} match triangle at CAM depth 8 — the
  paper's "expensive population counters" fall out as a few 3-bit adders.
* Population is the outer key and oldest the tie-break, so equal-population
  rows still retire in age order.

**`fewest_pending` — `row_sel` / `col_sel` = 2**

* The inverted compare on the same triangle: serve the row with the FEWEST
  pending references, so low-demand rows finish and free their bank sooner.
* Biases toward bank parallelism rather than row locality — the useful
  direction when activates, not column bandwidth, are the constraint.
* Costs exactly what `most_pending` costs (one compare direction) and keeps the
  same oldest tie-break.

#### `access_pref` — which command class is served first

**`column_first` — `access_pref` = 0 or 1 (build default)**

* Columns, then activates, then precharges: the legacy chain order,
  bit-identical.
* Lowest latency to an already-open row — a page hit never waits behind an
  activate for some other bank.
* The read/write decision (`prio_sub`) is then applied INSIDE the winning
  class, not across classes.

**`row_first` — `access_pref` = 2**

* Activates outrank columns, so more banks open sooner and more rows are
  available to hit later.
* Trades page-hit latency for bank parallelism; the natural partner for
  `most_pending` on scattered traffic.
* Only the class ORDER changes — `order_mode` still decides who is a candidate,
  which is why the two compose instead of fighting.

**`precharge_first` — `access_pref` = 3**

* Retires rows first: precharge, then columns, then activates.
* For configurations where the precharge queue is the constraint — close-page
  and the RBL paging modes, where nearly every access ends in a close.
* Precharge candidates are still picked strictly oldest, so this changes WHEN
  precharges are served, never WHICH one.

#### `prio_sub` — read versus write priority

**`load_over_store` — `prio_sub` = 0 or 2 (build default)**

* Reads outrank writes in every demand class: a 1-bit priority key protecting
  latency-critical loads.
* Writes still progress in the gaps, but a sustained read stream can hold them
  off — the write-batching watermarks exist to bound exactly that.
* Bit-identical to the pre-mode arbiter.

**`none` — `prio_sub` = 1**

* Fair alternation: a direction toggle flips on every FIRED demand op, so reads
  and writes take turns and neither direction can monopolize the pick.
* The toggle is a single flop below the output stage (it needs the fire
  signal), read by all three class decisions in the same cycle.
* Use it when measuring a mixed stream where read priority would otherwise mask
  write-path behavior.

**`age_boost` — `prio_sub` = 3**

* Reads first, UNLESS the write-class winner carries the aged flag and the
  read-class winner does not — an aged write then pierces read priority.
* Evaluated per class on the ALREADY-SELECTED winners, so it reorders two
  candidates rather than re-running the select.
* Pairs with `order_mode = age_threshold`, which is what sets the aged flags in
  the first place.

#### Standalone scheduling knobs

**Write batching — `SCHED_WR_WM.wr_high_wm` / `wr_low_wm` (0/0 = off, default)**

* Once write-CAM schedulable occupancy reaches `wr_high_wm`, writes drain
  back-to-back until occupancy falls to `wr_low_wm`, amortizing tWTR and bus
  turnaround instead of ping-ponging direction.
* Registered hysteresis, one flop: while draining it FLIPS the read-over-write
  bit in every demand class rather than adding a separate chain, and it
  OVERRIDES `prio_sub` for as long as it is active.
* `wr_high_wm = 0` disables it entirely — the bit-identical default.

**QoS — `SCHED_POLICY.qos_en` (0 = off, default)**

* `AxQOS` rides AR/AW into the intake, into CAM entry state, and back out as
  the per-entry `sch_qos` vector.
* Set, each class mask is first narrowed to its MAX-QoS candidates and the
  population/oldest select then runs inside that: QoS is the outer key, the
  existing selects break ties within a QoS level.
* Clear, the qos vector is never read, so the pick is bit-identical to a build
  with no QoS at all.

**`auto_precharge_en` — `SCHED_POLICY` bit 10**

* Allocated in the CSR map but NOT consumed by the RTL — nothing reads it
  today, so setting it changes nothing.
* Auto-precharge comes entirely from the Axis-2 paging decision
  (`ap_mode_en_o` / `ap_close_o`).
* Listed here so a characterization sweep does not spend a dimension on it.

### Axis 2 — paging (`pumice_page_policy`, `PAGE_POLICY_CFG` @ 0x070)

Every mode resolves to (a) the auto-precharge bit on the column command and
(b) a background per-bank precharge REQUEST that still respects
tRAS/tRTP/tRP/tRC. Telemetry: `PAGE_STATS_HIT` / `_MISS` / `_EMPTY`.

**`build_default` — `policy_mode` = 0**

* Defers to the legacy flat `PAGE_POLICY` CSR (OPEN or CLOSE): `ap_mode_en_o`
  stays low, so the arbiter uses its own `w_ap` and the mode engine is
  invisible.
* The bit-identical escape hatch — what every other mode is diffed against.
* Still runtime-switchable OPEN/CLOSE, and that switch alone was worth 8.8x on
  streaming traffic on silicon (12.7 -> 112 MB/s).

**`static_open` — `policy_mode` = 1**

* Never auto-precharge: a row stays open until another row in that bank forces
  the close.
* Best on high locality — about 68% of the paper's workloads, up to +18% over
  close.
* Pays a full tRP on every conflict miss, making it the worst case on random
  traffic.

**`static_close` — `policy_mode` = 2**

* Always auto-precharge (RDA/WRA): a row never outlives the column op that
  used it.
* The precharge rides inside the column command instead of consuming a separate
  PRE slot on the bus.
* Best on random / low-locality streams (up to +18% over open); throws away
  whatever locality the stream does have.

**`fixed_open` — `policy_mode` = 3 (`PAGE_TIMEOUT_CFG.tr_init`)**

* Leave the row open, then close it after an idle timeout of `tr_init` MC
  clocks (the paper used about tRC).
* One timeout counter per bank — the cheapest thing here that is not static.
* One constant serves every bank and every phase of the workload, so it can
  only ever be tuned for the average.

**`adapt_time` — `policy_mode` = 4 (Happy adaptive-timeout; recommended)**

* Per bank: a Timeout Counter TC, a Timeout Register TR and a 4-bit Mistake
  Counter MC. The row closes when TC reaches TR.
* MC counts UP on a premature close (a page-empty that reopens the row just
  closed) and DOWN on held-too-long (a conflict that could have been an empty).
  Every `check_interval`, MC above `mc_high_thr` grows TR by `tr_step`, MC
  below `mc_low_thr` shrinks it, clamped to `tr_min`..`tr_max`.
* Best measured policy for about 16-32 small registers plus a last-closed-row
  latch and comparator per bank; `policy_scope = 1` makes TR global rather than
  per-bank.

**`adapt_access` — `policy_mode` = 5 (Happy "Hybrid", `pumice_row_pred_table`)**

* A per-row 2-bit saturating counter, compared against `ctr_open_max`
  (default 2) at ACT time to decide open-or-close for that row.
* Tagless direct-mapped on {bank, XOR-folded row}: the fold replaces the
  paper's full per-row BRAM, so aliasing blends history between rows —
  acceptable in a predictor, and the reason it is a predictor and not a cache.
* Learns from accesses-per-activation at explicit PRE closes plus a
  premature-reopen decrement on auto-precharge closes. (`ctr_width` is
  CSR-allocated but unwired; the counter is 2-bit.)

**`rbl_static` — `policy_mode` = 6 (RBLA / Yoon, `pumice_rbl_table`)**

* Counts row-buffer MISSES only, never accesses — a hit carries no signal about
  whether a row deserves to stay open.
* A small set-associative table of saturating miss counters (tag = row address,
  true LRU); `PAGE_RBL_CFG` shapes ways, sets, `miss_thresh` and the epoch. A
  row over `miss_thresh` is low-locality and gets auto-precharge.
* Separates hot-but-friendly rows from hot-and-thrashing ones, which
  frequency-based schemes conflate. Only the miss predictor is kept; the
  paper's DRAM-cache migration machinery is dropped.

**`rbl_dyn` — `policy_mode` = 7**

* The same table, except `miss_thresh` hill-climbs once per epoch against the
  measured page-hit fraction instead of staying where software put it.
* Divider-free: the hit-fraction comparison is a cross-multiplication, with
  direction memory so the climb keeps walking whichever way last helped.
* `PAGE_RBL_CFG.reset_interval` sets the epoch (0 = counters never reset),
  which is also what decides how fast it can react to a phase change.

### Axis 3 — refresh (`refresh_ctrl`, `REF_CTRL` @ 0x140)

The JEDEC **+-8 postpone/pull-in credit** is the hard data-integrity budget
every mode obeys; tREFI and tRFCab live in `TIMINGS_RFC_REFI`, not here.

**`refab` — `REF_CTRL.mode` = 0 or 1 (build default; DDR2 and LPDDR2)**

* One command refreshes the whole rank at tRFCab on a tREFI interval; every
  bank must be precharged first.
* An 8-deep accumulator does the tracking: each tREFI tick increments, each
  grant decrements, and the request stays high while it is non-zero.
* The safe fallback in every configuration, and what the scheduler silently
  degrades to when a per-bank request lands on DDR2.

**`refpb_rr` — `REF_CTRL.mode` = 2 (LPDDR2 only)**

* Per-bank refresh driven by the DRAM's own internal round-robin counter — per
  JESD209-2 6.6 the command carries NO bank address. The arbiter precharges
  only the rotor bank, then issues REFPB.
* The controller keeps a rotor MIRROR advanced by the GRANTED OP_REFPB on the
  wire; keying it off the mode bit instead desynchronizes the mirror from the
  device. `REF_TIMING_PB.trefi_pb` sets the interval (0 derives tREFI/8),
  `trfc_pb` the recovery, and `perbank_supported` straps capability.
* Conservative v1 interlock: the rank-wide ACT block during the shorter tRFCpb
  also spaces consecutive REFpb commands. On traffic that cannot use the other
  banks meanwhile, the serialized commands can total about 3.5x tRFCab — keep
  `refab` selectable.

**Postpone credit — `REF_CTRL.postpone_limit` (0..8; 0 = strict, default)**

* While demand is high the refresh request is WITHHELD until the pending
  backlog exceeds the limit, so a burst is not interrupted by a refresh that
  could legally have been deferred.
* Effectively clamped at 7, so the JEDEC 8-postponed ceiling can always force
  the issue no matter what software programmed.
* 0 requests the moment anything is pending — the strict, bit-identical
  baseline.

**Pull-in credit — `REF_CTRL.pullin_limit` (0..8; 0 = never, default)**

* On CONFIRMED idle, refreshes run AHEAD of tREFI and bank up to the limit as
  credit, so a demand burst that follows sees a refresh-free window.
* Each later tREFI tick then CONSUMES a credit instead of adding a pending
  refresh.
* "Confirmed" is a 16-cycle hysteresis over CAM occupancy — micro-gaps between
  bursts must not read as idle and release the run-ahead.

**Drain burst — `refresh_burst` (1..8)**

* When the request asserts it loads a drain counter and raises
  `refresh_drain_active`, telling the scheduler to grant REF back-to-back
  without yielding to reads or writes.
* Turns N postponed refreshes into ONE contiguous bubble instead of N scattered
  ones: the same total cost, concentrated where it can be measured and
  scheduled around.
* Measured cost with credits parked: exactly 5 stall cycles per refresh, no
  scatter (`perf_refresh_bubbles`).

---

## Verification (`dv/`)

Practice: `vault/handbook/dv/` — especially [[structure-trackers]].

* **Tiers** — `dv/tests/fub` (21 files), `dv/tests/macro` (4),
  `dv/tests/top` (5), plus PHY-facing checks at the root of `dv/tests`.
  22 TB classes in `dv/tbclasses/`.
* **Everything is BFM-driven** (PUMICE-014). No test hand-pokes a standard
  interface or valid/ready handshake. `pumice_axi_bfm.py` owns every
  `s_axi_*`; `pumice_fub_bfm.py` wraps GAXI for fub-internal handshakes.
  Timing profiles come from `TBClasses.amba.amba_random_configs`.
* **Structure trackers** (`dv/tbclasses/trackers/`) — passive per-FUB
  monitors emitting one greppable markdown table each, so a paging/refresh/
  scheduling decision can be followed ACROSS structures after the fact.
  Off by default; `PUMICE_TRACKERS=1`.
* **Golden model** — `DFISlavePHY` from the RDS-DV CocoTBFramework plus a
  `MemoryModel`, so top tests check real data, not just handshakes.

## Performance measurement

* **Utilization = beats / cycles VALID was high** (not per wall-clock
  cycle) — cycles where the master offered nothing are the testbench's, not
  the DUT's. 100% means the DUT accepted every beat it was offered.
* **Clean-room ceiling** — `perf_write_ceiling` parks every maintenance
  source (refresh off, page policy OPEN, page-hit stream, writes only, AW+W
  back-to-back) so the only thing that can stall `wready` is the datapath.
  Result: 100.00%, zero backpressure cycles.
* **Refresh cost** — `perf_refresh_bubbles` reruns the identical stream with
  tREFI cranked up. It is the ceiling test's POSITIVE CONTROL as much as a
  measurement: with maintenance parked the DUT never stalls, so `bp == 0`
  passing proves nothing until you show the accounting can SEE a stall.
  Measured: every refresh costs exactly 5 cycles, no scatter.
* **Mode sweeps** — `perf_paging_sweep` (8 modes x 8-bank and 1-bank
  spreads) and `perf_paging_sched_cross` (8 paging x 10 scheduling = 80
  combinations). Outputs land as `*.out` tables beside the sim build.
  The 1-bank column is the discriminator: with 8-way rotation every paging
  mode reads 100%, so that column alone cannot fail.

---

## Registers, docs and collateral

* **`regs/`** — PeakRDL-generated CSRs (RTL + docs + `pumice_csr_regmap.py`
  in lockstep). Regenerate ONLY via `bin/peakrdl_generate.py`; DV accesses
  registers BY NAME, never by hardcoded offset.
* **`docs/`** — the HAS and MAS specs (v0.5, docx+pdf, generated by
  `generate_has_pdf.sh` / `generate_mas_pdf.sh`), `design-requirements.md`
  (the mode catalogue), and the signal-contracts workbook generator.
* **`rtl/*.md`** — per-layer uarch specs, the authority for how a layer
  works. `LPDDR2_CA_ENCODING.md` carries the JESD209-2 Table 60 CA truth
  table.

## Status

* Board-validated on the Nexys A7 (reads and writes clean); the correctness
  backlog is empty.
* Open work is tracked in `vault/Tasks/pumice/` — see its INDEX for the
  shortlist and the next free task ID.
