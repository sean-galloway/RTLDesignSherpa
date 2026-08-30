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

**`order_mode` — who is a candidate**

* **`fr_fcfs` (0/2, default)** — among references whose DRAM timing and
  resources are free, row-hit-ready wins, oldest breaks the tie.
  * A ready-check plus an age compare — no reorder machinery, and the paper's
    ~+25% bandwidth over strict order.
* **`in_order` (1)** — issue only what the single oldest un-issued reference
  needs; no lookahead. The latency-floor / bandwidth-ceiling reference point.
  * An overlay that NARROWS the FR-FCFS class masks to the head-of-CAM entry
    taken from the age-order matrix.
  * Between the read and write CAMs the older head wins on a relative-age
    compare — both age counters free-run from reset (same epoch), tie to read.
* **`age_threshold` (3, with `age_thresh`)** — a reference older than
  `age_thresh` (MC cycles / 16) is boosted, which bounds starvation.
  * While ANY aged entry exists every class narrows to aged entries, so an aged
    reference's PRE outranks a fresh row-hit. The CAMs export a per-entry 1-bit
    aged flag, so numeric ages never leave the CAM.
  * The boost triggers on the aged entry's EXISTENCE, not its momentary
    candidacy — a guard-blocked PRE must still engage the narrowing, or the
    competing column stream re-arms the guard forever.

**`row_sel` / `col_sel` — which candidate wins** (`row_sel` steers ACTIVATE,
`col_sel` steers COLUMN; precharge picks stay strictly oldest in every mode)

* **`oldest` (0, default)** — strict age order within whatever mask survived.
  * Composes under any `order_mode`; it is the tie-break the other two selects
    fall back on.
* **`most_pending` (1)** — serve the row with the MOST pending references:
  drain the hottest row, maximizing accesses per activation.
  * At CAM depth 8 the paper's "expensive population counters" degenerate to an
    8x8 same-{bank,row} match triangle per CAM — population first, oldest tie.
* **`fewest_pending` (2)** — the opposite bias: let low-demand rows finish and
  precharge sooner, freeing banks.
  * Same triangle, inverted compare. Wins when bank parallelism rather than row
    locality is the bottleneck.

**`access_pref` — which command class the address arbiter prefers**

* **`column_first` (0/1, default)** — columns, then activates, then precharges:
  the legacy chain order, bit-identical. Lowest latency to an open row.
* **`row_first` (2)** — activates outrank columns, opening more banks sooner.
  * Trades page-hit latency for bank parallelism; pairs with `most_pending`.
* **`precharge_first` (3)** — retire rows first, for when the precharge queue
  is the constraint (close-page and RBL paging).
  * The preference reorders WHICH CLASS of the `order_mode` survivors is
    served; read-over-write is then applied inside the winning class.

**`prio_sub` — read versus write priority**

* **`load_over_store` (0/2, default)** — reads outrank writes; a 1-bit key
  protecting latency-critical loads.
* **`none` (1)** — fair: direction alternates on every fired demand op, so
  neither direction can monopolize.
* **`age_boost` (3)** — reads first UNLESS the write-class winner is age-boosted
  and the read-class winner is not, so an aged write pierces read priority.

**Standalone scheduling knobs**

* **Write batching (`SCHED_WR_WM.wr_high_wm` / `wr_low_wm`)** — drain writes
  back-to-back once write-CAM schedulable occupancy crosses the high watermark,
  stopping at the low one, to amortize tWTR and bus turnaround.
  * Implemented as registered hysteresis that FLIPS the read-over-write bit in
    every demand class — not a separate chain — and it overrides `prio_sub`
    while active. `wr_high_wm = 0` disables it, bit-identical.
* **QoS (`qos_en`)** — `AxQOS` rides AR/AW into the intake, into CAM entry
  state, out as the per-entry `sch_qos` vector.
  * Each demand class narrows to its MAX-QoS candidates BEFORE the
    population/oldest select, making QoS the outer key and leaving the existing
    selects to break ties inside the winning QoS level.
* **`auto_precharge_en`** — CSR field is allocated but NOT yet consumed by RTL;
  auto-precharge today comes entirely from the Axis-2 paging decision.

### Axis 2 — paging (`pumice_page_policy`, `PAGE_POLICY_CFG` @ 0x070)

Every mode resolves to (a) the column command's auto-precharge bit and (b) a
background per-bank precharge REQUEST that still respects tRAS/tRTP/tRP/tRC.

* **`build_default` (0)** — defer to the legacy flat `PAGE_POLICY` CSR
  (OPEN or CLOSE) exactly as before the mode engine existed.
  * `ap_mode_en_o` stays low, so the arbiter uses its own `w_ap`. This is the
    bit-identical escape hatch, and it is still runtime-switchable OPEN/CLOSE —
    that switch alone was worth 8.8x on streaming traffic on silicon.
* **`static_open` (1)** — never auto-precharge; the bank timer holds the row
  open until something else evicts it.
  * Best on high locality (about 68% of workloads, up to +18% versus close);
    pays tRP on every conflict miss.
* **`static_close` (2)** — always auto-precharge (RDA/WRA), so a row never
  outlives its column op.
  * Fuses the precharge into the last column command instead of spending a
    separate PRE slot; best on random / low-locality streams (up to +18%).
* **`fixed_open` (3, `PAGE_TIMEOUT_CFG.tr_init`)** — leave the row open, close
  it after an idle timeout of `tr_init` clocks (the paper used about tRC).
  * One timeout counter per bank; the cheapest thing that is not static.
* **`adapt_time` (4, Happy adaptive-timeout, the recommended adaptive one)** —
  per bank a Timeout Counter TC, Timeout Register TR and 4-bit Mistake Counter
  MC; the row closes when TC reaches TR.
  * MC counts up on a premature close (page-empty reopening the row just
    closed) and down on held-too-long (a conflict that could have been empty);
    every `check_interval`, MC above `mc_high_thr` grows TR by `tr_step`, MC
    below `mc_low_thr` shrinks it, clamped to `tr_min`..`tr_max`.
  * Best measured policy for roughly 16-32 small registers plus a last-closed
    row latch and comparator per bank. `policy_scope` makes TR global instead
    of per-bank.
* **`adapt_access` (5, Happy "Hybrid", `pumice_row_pred_table`)** — a per-row
  2-bit saturating counter, compared against `ctr_open_max` at ACT time.
  * Tagless direct-mapped on {bank, XOR-folded row}: the fold replaces the
    paper's full per-row BRAM, so aliasing blends history — acceptable in a
    predictor, and the reason it is a predictor and not a cache.
  * Learns from accesses-per-activation at explicit PRE closes, plus a
    premature-reopen decrement on auto-precharge closes.
* **`rbl_static` (6, RBLA / Yoon, `pumice_rbl_table`)** — count row-buffer
  MISSES only, never accesses: a hit carries no signal about locality.
  * A small set-associative table of saturating miss counters (tag = row
    address, true LRU; `PAGE_RBL_CFG` sets ways/sets/threshold/epoch); a row
    over `miss_thresh` is low-locality and gets auto-precharge.
  * Separates hot-but-friendly rows from hot-and-thrashing ones, which
    frequency-based schemes conflate. Only the miss predictor is kept — the
    paper's DRAM-cache migration machinery is dropped.
* **`rbl_dyn` (7)** — same table, but `miss_thresh` hill-climbs once per epoch
  against the measured page-hit fraction.
  * Divider-free: the comparison is a cross-multiplication, with direction
    memory so the climb keeps walking the way that last helped.

### Axis 3 — refresh (`refresh_ctrl`, `REF_CTRL` @ 0x140)

The JEDEC **+-8 postpone/pull-in credit** is the hard data-integrity budget
every mode obeys; tREFI and tRFCab live in `TIMINGS_RFC_REFI`, not here.

* **`refab` (0/1, default, DDR2 + LPDDR2)** — one command refreshes the whole
  rank at tRFCab, on a tREFI interval.
  * The safe fallback in every configuration, and the mode the scheduler
    silently degrades to when a per-bank request lands on DDR2.
* **`refpb_rr` (2, LPDDR2 only)** — per-bank refresh driven by the DRAM's own
  internal round-robin counter.
  * JESD209-2 6.6: the command carries NO bank address, so the controller keeps
    a rotor MIRROR that advances exactly when an OP_REFPB is granted onto the
    wire. The arbiter precharges only the rotor bank, then issues REFPB;
    `REF_TIMING_PB.trefi_pb` sets the interval (0 derives tREFI/8) and
    `trfc_pb` the recovery. `REF_CTRL.perbank_supported` straps capability.
  * Conservative v1 interlock: the rank-wide ACT block during the shorter
    tRFCpb also spaces consecutive REFpb commands. Columns to already-open rows
    in other banks flow throughout; full ACT-during-tRFCpb overlap is a later
    optimization.
  * Caution: on traffic that cannot use the other banks during a per-bank
    window, REFpb's serialized commands can total about 3.5x tRFCab — keep
    `refab` selectable.
* **Postpone / pull-in credits (`postpone_limit` / `pullin_limit`, 0..8)** —
  rank-scoped credit split into a pending backlog and a run-ahead credit.
  * Under demand the request is withheld until the backlog exceeds
    `postpone_limit` (clamped at 7, so the JEDEC ceiling always forces); on
    CONFIRMED idle — 16-cycle hysteresis over CAM occupancy, because micro-gaps
    between bursts must not release postponed refreshes — refreshes run ahead
    up to `pullin_limit`, and each later tREFI tick then consumes a credit
    instead of adding backlog.
  * 0/0 is the strict, bit-identical baseline. Per-bank `ref_credit[b]` steering
    arrives with REFpb. Measured cost with credits parked: exactly 5 stall
    cycles per refresh, no scatter (`perf_refresh_bubbles`).

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
