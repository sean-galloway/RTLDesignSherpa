# pumice — at a glance

A DDR2/LPDDR2 memory controller. One index page: every feature area, 1-3
bullets each, so you can find the right file without reading the tree.

Depth lives elsewhere and is linked per section — this page is a map, not a
second copy. Authority order: `/GLOBAL_REQUIREMENTS.md` > the handbook
(`vault/handbook/INDEX.md`) > the uarch specs in `rtl/*.md` > this page.

---

## Read this first: pumice is a RESEARCH controller, deliberately

**pumice is over-engineered on purpose.** It is not a minimal DDR2 controller
and should not be read as one, or copied as a template for a product part
where area matters.

It exists to make memory-scheduling research *runnable on silicon*: to take a
policy out of a paper, put it behind a CSR, and measure it on a real DRAM with
the same generators, the same meters and the same host program as every other
policy. That is why there are three orthogonal runtime axes with twenty-odd
selectable modes, per-entry reorder CAMs, an AR-order return ring, a command
history scoreboard, and a characterization harness that can be pointed at a
*different vendor's controller* for a like-for-like comparison. A product part
would pick one policy and delete the rest.

The cost is measurable and is the honest counterpart to the flexibility:

| | pumice | LiteDRAM (same board, same PHY, same harness) |
|---|---|---|
| controller + PHY | **12 981 LUT / 9 667 FF** | 2 411 LUT / 2 046 FF |
| streaming read | 571.3 MB/s | 579.5 MB/s |
| streaming write | 570.3 MB/s | 569.2 MB/s |
| concurrent read+write, one window | **570.1 MB/s total** | 285.6 MB/s |

Roughly **five times the logic for equal streaming bandwidth** — and 2.0x
LiteDRAM once both directions run at once, which is the workload the reorder
window exists for. If you want a small controller, that table is the argument
against this one. If you want to ask "what does adaptive page closing actually
buy on hardware", it is the argument for it.

Everything below follows from that intent. Modes default to
**encoding 0 = build default and bit-identical**, so the research surface costs
nothing until it is switched on, and every claim on this page is measured
rather than asserted.

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
  the B and R channels back to the host. The read intake carries a two-stage
  AR pipeline: the skid head is the AR being PROBED against the write CAM (the
  snarf/RAW lookup is registered inside that CAM), the stage behind it is the
  AR being ADMITTED, and the two advance together so a sub-command admits
  every cycle. Doing this with a single arm bit instead capped admits at one
  every TWO cycles and halved board read bandwidth — see *Status*.
* **`pumice_wr_data_cam` / `pumice_rd_cmd_cam`** — where a transaction lives
  between its address handshake and retirement. The write CAM holds data in
  an SRAM and gates B on `agg && last` (one response per *original* burst);
  the read CAM reorders returns into AR order and collapses `RLAST`.
* **`pumice_axi_burst_chopper` + `pumice_wr_splitter`** — split a host burst
  into fixed-BL sub-commands with no FSM, and pad a short or ragged one out
  to a whole DRAM burst with zero-strobe filler beats (see *Legal AXI
  transaction shapes*). The splitter carries no B channel by design;
  aggregation is the CAM's job.
  NOTE the ragged-burst `$error` + SLVERR still present in
  `pumice_wr_intake` is now UNREACHABLE: the splitter guarantees a full
  chunk, so `w_aw_err` can no longer assert. It is dead code kept for
  history, not a live guard.
* **`addr_mapper`** — flat AXI address to `{rank,bank,row,col}` under ONE
  knob, `ADDR_MAP.bank_lsb`. Row/rank positions are invariant; only the bank
  field slides (ROW_MAJOR / INTERLEAVE / XOR-hash are settings, not schemes).

## Legal AXI transaction shapes

**Every legal AXI4 write and read is accepted.** There is no burst length,
strobe pattern or alignment the host has to avoid. A compliant master issues
`AxLEN=0` routinely (a CPU storing one word), and silently losing that write
was a real failure mode here, so the rule is deliberately unconditional.

| dimension | accepted |
|---|---|
| `AxLEN` | 1-256 beats (INCR). `AxLEN=0` is a normal single-beat burst |
| burst type | INCR any length; WRAP 2/4/8/16; FIXED 1-16 |
| `AxSIZE` | 1 byte up to the full bus width |
| `WSTRB` | any pattern, including sparse and all-zero (a legal no-op) |
| start address | any, including part-way into a DRAM burst |

### Names — one concept, several spellings

The tree grew multiple names per quantity. They are the SAME number; this is
the mapping so nobody invents a sixth:

| concept | canonical | also spelled |
|---|---|---|
| JEDEC burst length, in DEVICE beats | `DRAM_BL` | `BL` (core/ifc/intake), `dram_bl` (TB), `DFI_PHASE.bl` (CSR), `BEATS_PER_BURST` (char suite) |
| the same, scaled to pumice beats | `BL_PUMICE` | — |
| AXI beats in one DRAM burst | `BURST_LEN_MULTIPLE` | `CHUNK_BEATS` (chopper/splitter), `BURST_WORDS` (core), `EXP_AXI_BEATS` (wr_intake) |
| DFI phases per controller clock | `DFI_RATE` | `gear_ratio` is its LOG2, not the rate |

`gear_ratio` is the trap in that list: it is `log2(DFI_RATE)`, so rate-2 is 1
and rate-4 is 2. Writing the rate where the log belongs makes
`(RATEW'(1) << gear_i)` overflow to zero, every DFI phase goes inactive and
writes vanish with `B=OKAY`.

### How a burst maps to DRAM

One DRAM burst is `BURST_WORDS` AXI beats, derived from the build parameters:

    BL_SHIFT    = clog2(DRAM_BEAT_WIDTH / DRAM_DEVICE_WIDTH)   // 0 if beat <= device
    BL_PUMICE   = BL >> BL_SHIFT
    BURST_WORDS = (BL_PUMICE >= DFI_RATE) ? BL_PUMICE / DFI_RATE : 1

A host burst is reconciled to that in three ways, none of which the host sees:

* **Longer** — `pumice_axi_burst_chopper` splits it into `BURST_WORDS`-sized
  sub-commands, each on its own DRAM-burst boundary.
* **Shorter or ragged** — `pumice_wr_splitter` completes the DRAM burst with
  zero-strobe FILLER beats. `strb=0` becomes `DM=1` in
  `pumice_dfi_wr_serializer` (`dfi_wrdata_mask_o = ~wd_strb_i`), so the device
  clocks the beat and writes nothing. That is what DDR2's data mask is for.
  Reads need no padding: the DRAM returns the whole burst and
  `pumice_rd_intake`'s per-sub beat budget forwards only the beats the host
  asked for, dropping the rest before the R channel.
* **Unaligned** — the address handed to `addr_mapper` is aligned down to the
  AXI beat and `WSTRB` selects the bytes, exactly as AXI4 specifies. Applying
  BOTH the column offset and the strobes counted the offset twice and landed
  the write a beat further on.

### Performance caveat (this is the one that bites)

Accepted is not the same as free. **A partial DRAM burst still costs the
device a full ACT/CAS cycle**, because the DRAM always transfers `BL` beats.
A workload issuing half-bursts reports roughly half the throughput the
controller can actually sustain.

So the two sides have different rules, and the distinction matters:

* **The controller accepts any legal AxLEN.** That is a hard requirement --
  a compliant master may issue `AxLEN=0` at any time.
* **A half burst is ILLEGAL in the characterization generators.** Not
  discouraged, illegal: `_check_full_burst()` in
  `dv/tests/test_ddr2_char_macro.py` rejects any `burst_len` that is not a
  whole multiple of one DFI BL8 transaction. Behaviour observed under a
  sub-burst generator shape is void -- an illegal stimulus, not a defect to
  investigate.

Short-burst CORRECTNESS is proven by the controller-level suites below, not
by the perf shapes.

Covered by, all mutation-verified:
`test_pumice_top_partial_strb` (8 strobe patterns x 3 lengths, byte-exact
against the golden model AND through an AXI read-back),
`test_pumice_top_partial_rd` (4 lengths x 4 offsets, counting R beats on the
bus -- surplus beats carry the burst's own RID and are invisible to a data
check), `test_pumice_top_burst_len` (AxLEN 1,2,3,4,5,7,8,16) and
`test_pumice_top_geared_short_burst` (down-gear, where the 64->128 converter
manufactures a half-strobed beat).

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

## Runtime modes — three independent axes

All CSR-selectable, all **encoding 0 = build default and bit-identical**, each
mutation-proven. Catalogued in `docs/design-requirements.md`.

### Axis 1 — scheduling policy (`pumice_cmd_arbiter`)

**The default policy is FR-FCFS** — First-Ready, First-Come-First-Served, the
standard DRAM scheduling policy — with read-over-write priority. That is what
the per-cycle pick ladder implements:

    1 init  2 refresh  3 COLUMN (row-hit RD/WR to an open, tRCD-met row)
    4 ACTIVATE (oldest pending op on an idle bank)  5 PRECHARGE

"First-Ready" is stage 3 outranking 4: a row hit issues ahead of an older
access that would need an ACT. "FCFS" is the oldest-first tie-break inside
each stage.

`order_mode` selects the policy; everything else is an **overlay that narrows
which entries are candidates** — the ladder above is untouched:

| `order_mode` | policy |
|---|---|
| 0 (default) | **FR-FCFS** — reorder for row hits, oldest-first within a class |
| 1 `in_order` | **strict FCFS** — only the oldest reference may pick, so no lookahead and no row-hit reordering. In the BASE build this is per-channel (each CAM issues its own head and the arbiter's read/write preference picks the side); the global read-vs-write age compare is an extra cone and is built only under `+define+PUMICE_ENHANCED` |
| 3 `age_threshold` | **FR-FCFS with a starvation bound** — once any entry passes an age threshold, only aged entries may pick until they drain |

The overlays are independent and none of them is required:

* `access_pref` — reorders the CLASSES, not the entries. `0/1 column_first`
  is the default and is what makes the policy First-Ready; `2 row_first` puts
  activates ahead of row hits (buys bank parallelism at the cost of row-hit
  throughput); `3 precharge_first` closes wrong rows eagerly.
* `row_sel` / `col_sel` — change the pick *within* a stage from oldest to
  `most_pending` / `fewest_pending`. `row_sel` steers ACTIVATE, `col_sel`
  steers COLUMN.
* **write batching** (`SCHED_WR_WM` high/low watermarks) — once the write CAM
  crosses `high_wm`, writes outrank reads until it falls to `low_wm`, so the
  tWTR/tRTW bus turnaround is amortized over a batch instead of paid per
  write.
* `prio_sub`, `qos_en` — AXI QoS admitted as a priority class.

### Axis 2 — page policy (`pumice_page_policy`)

Decides **auto-precharge per bank** — whether a row stays open after an
access. Mode 0 keeps the flat build-time `page_policy_i` (OPEN/CLOSE); any
nonzero mode takes over:

| mode | policy |
|---|---|
| 1 `static_open` | never auto-precharge — best for streaming/row-major |
| 2 `static_close` | always auto-precharge — best for random/low-locality |
| 3 `fixed_open` | open, but rows close on an **idle timeout** |
| 4 `adapt_time` | **adaptive timeout** — a per-bank timeout register adapts up/down from a mistake counter (premature-close vs held-too-long) each interval |
| 5 `adapt_access` | **per-row 2-bit close predictor** — knob-free; predicts whether this row will be hit again |
| 6 `rbl_static` | close on a per-bank **row-buffer-locality** verdict from a miss-counter table |
| 7 `rbl_dyn` | `rbl_static` plus a per-epoch threshold hill-climb |

The block never drives a PRE itself: it raises a request and the arbiter
issues it as its lowest-priority pick, so demand traffic, refresh drain and
JEDEC timing still gate it.

### Axis 3 — refresh policy (`refresh_ctrl`)

JEDEC allows a refresh to be deferred or run early by up to 8. The default is
strict (issue on tREFI expiry); the credits trade latency against bandwidth:

* `postpone_limit` — while demand is present, hold the refresh back, up to the
  JEDEC 8-deep ceiling, so a burst is not interrupted mid-stream.
* `pullin_limit` — while idle, run refreshes **ahead** so they are not owed
  later when traffic returns.
* `refresh_burst` (drain) — issue several queued refreshes back to back.
* `refpb_mode` — REFab (all banks) vs **REFpb** (per-bank, LPDDR2), with a
  rotor mirroring the device's internal bank counter.

---

## Verification (`dv/`)

Practice: `vault/handbook/dv/` — especially [[structure-trackers]].

* **Tiers** — `dv/tests/fub` (24 files), `dv/tests/macro` (4),
  `dv/tests/top` (6), plus PHY-facing checks at the root of `dv/tests`.
  23 TB classes in `dv/tbclasses/`. 219 tests at FULL
  (`make clean-all && make run-all-full-parallel`); a bare `pytest` runs the
  FUNC subset only and under-reports.
* **Everything is BFM-driven.** No test hand-pokes a standard
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
* **Intake admit rate** — `perf_intake_admit_rate` asks "of the cycles this
  intake COULD have admitted, how often did it?", with the write intake as the
  control. Conditioning on ready is what makes it geometry-independent: a raw
  duty measures whatever the bottleneck happens to be, and at this testbench's
  geometry that hides a half-rate intake completely.
* **On the board** — `build-perf/host/pumice_master.py --char` drives the
  characterization harness over UART and writes a CSV. `--char-profile
  concurrent` and `multigen` run both directions in ONE window, which is the
  only way read/write turnaround is paid at all; every other profile runs a
  write phase then a read phase. Results and the LiteDRAM A/B live in
  `docs/char_results/`.

---

## Registers, docs and collateral

* **`regs/`** — PeakRDL-generated CSRs (RTL + docs + `pumice_csr_regmap.py`
  in lockstep). Regenerate ONLY via `bin/peakrdl_generate.py`; DV accesses
  registers BY NAME, never by hardcoded offset.
* **`docs/`** — the HAS and MAS specs (v0.5, docx+pdf, generated by
  `generate_has_pdf.sh` / `generate_mas_pdf.sh`), `design-requirements.md`
  (the mode catalogue), `char_results/` (board CSVs and the LiteDRAM A/B
  findings), and `pumice_signal_contracts.xlsx` — ONE workbook holding the
  spec decision tables and the computed K-maps, with axis equations,
  invariants, don't-cares and derived implicants. `check_kmap_rtl_sync.py`
  fails if a map's mirror drifts from the RTL and the generator refuses to
  write on drift.
* **`design/`** — spec-first collateral: WaveJSON timing diagrams for the
  ideal cadence, five bad-but-correct shapes and the pathological ones, each
  captioned with the board number it produced. `check_waves.py` validates them
  (WaveDrom renders a malformed diagram silently) and `render_waves.py`
  produces the PNGs that MAS Chapter 7 embeds.
* **`rtl/*.md`** — per-layer uarch specs, the authority for how a layer
  works. `LPDDR2_CA_ENCODING.md` carries the JESD209-2 Table 60 CA truth
  table.

## Status

**Working, on silicon, at target.** Board-validated on the Nexys A7 at
75 MHz / DDR2-300 / BL4 on the x16 MT47H64M16. Peak is 600 MB/s (8 B per
controller cycle).

| | MB/s | share of peak |
|---|---|---|
| streaming write (row_major bl8) | **570.3** | 95.0% |
| streaming read (row_major bl8) | **571.3** | 95.2% |
| concurrent read+write, one window | **570.1 total** | 95.0% |

14 of 14 characterization points integrity-clean. Timing closes at
WNS **+0.285 ns**, 0 failing of 94 060 endpoints. Simulation is green: 219
controller tests at FULL plus the DDR2 characterization harness (31 passed).

**How it got here (2026-09-10).** Reads sat at 291.7 MB/s — 48.6% of peak,
against a 570 write — for weeks, and two separate throttles were responsible:

* `pumice_rd_intake` admitted one sub-command every TWO cycles. A single arm
  bit marking "the registered snarf probe belongs to this AR" was cleared by
  its own admit and could only re-set the following cycle. One sub-command is
  one DRAM burst, and at this geometry one burst is one bus beat, so the gate
  *was* the bandwidth. Fixed by staging the AR; read 291.7 -> 470.9.
* The read return ring ran 32 tickets because the characterization macro never
  passed `RD_RET_DEPTH` down, so every board build used the default regardless.
  At ~49 cycles of read latency, 32 tickets cap reads near 78% of the DRAM
  rate. Board default is now 64; read 470.9 -> **571.3**, write parity.

Neither was visible in simulation, because the core suite runs a geometry where
one DRAM burst is FOUR bus beats and a half-rate intake still supplies two
beats per cycle. That gap is filed (see below) and is the single most valuable
thing to fix next.

**What is known to be true, and measured:**

* Every legal AXI burst length works, including `AxLEN=0`, and any `WSTRB`
  pattern including all-zero. Proven byte-exact against a golden memory model,
  each check mutation-verified.
* Reads and writes both reach ~95% of peak, and hold it with one, two or three
  concurrent generators.
* Under concurrent read+write pumice sustains 2.00x LiteDRAM through the
  identical harness. That is the first workload where the reorder window pays
  for its area: it batches same-direction columns and amortises the tWTR/tRTW
  turnaround that a per-bank round-robin machine pays on every switch.
* Refresh costs exactly 5 cycles per event, deterministically.

**What is NOT done — read this before trusting a number:**

* **Simulation cannot run the board's DRAM geometry.** The core suite is BL8 /
  64-bit beat / device == beat, so one burst is four bus beats. Any
  per-sub-command rate limit is divided by four before a bandwidth assertion
  can see it, which is exactly how a 2x read throttle shipped with the suite
  green. The geometry is now env-overridable but the board point does not run
  clean (a read checker trips; the write ceiling stalls where the real board
  reaches 95%), so it is not yet in the regression.
* **Two writers is unsafe in the characterization harness.** pumice returns B
  out of AW order across masters while the generated write bridge routes
  responses by FIFO position, so a second writer would be silently misrouted.
  Single-writer results are unaffected. Three candidate fixes are filed; none
  is chosen.
* **KNOWN BUG: read latency is ~49 cycles against LiteDRAM's 24.7 on the same
  board and PHY.** Roughly 24 cycles of extra pipeline for the same DRAM
  access. The two 2026-09-10 fixes bought bandwidth and not latency, and this
  is now the largest identified defect in the controller. It is also what
  caps small-burst reads — see below.
* **Small-burst reads are latency-bound, and it is Little's law, not a
  scheduling bug.** Reads at AxLEN 1/2/4 reach 16%/31%/60% of peak while
  writes hold 95%. Measured against the model
  `min(8 x AxLEN / (read_latency + AxLEN), 0.95)` -- the read generator allows
  8 bursts in flight:

  | AxLEN | predicted | measured |
  |---|---|---|
  | 1 | 96.1 | 96.2 |
  | 2 | 184.6 | 188.1 |
  | 4 | 369.2 | 359.9 |
  | 8 | 570.0 | 570.5 |
  | 16 | 570.0 | 570.7 |

  Five points inside 2%. The proximate cause is a HARNESS parameter
  (`GEN_MAX_OUTSTANDING=8` in the read engine), but it only binds because
  pumice's read latency is ~49 cycles: at LiteDRAM's 24.7 the same 8-burst
  budget would cover AxLEN 4 and the shortfall would vanish. Writes do not show
  it because pumice returns B at CAM commit rather than after a DRAM round
  trip, so a write burst retires in a fraction of the time and 8 in flight is
  ample. **Fix the latency and this closes with it.**
* **No observer is instantiated on the pumice AXI interface** — the bridge slot
  exists and is tied off.
* **The advanced modes are characterized but not tuned.** All three axes run on
  the board and the sweep exists; nobody has gone through the results and
  picked defaults per workload class.

Detailed work items live in `vault/Tasks/pumice/` and `vault/Tasks/nexysa7/`.

---

## The traffic generators — 1 to 8 streams per direction

The characterization harness does not drive pumice with one address stream. It
drives an ARRAY of independently programmed AXI4 masters, split by direction,
and that array is the reason a board number can distinguish "the controller
will not go bank-parallel" from "the stimulus never asked it to".

`projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/` —
`char_engine_block.sv` (the DUT-agnostic spine) and `chargen_regs.rdl` (config).

### How many streams

`NUM_GEN` is the count PER DIRECTION, so a build has `NUM_GEN` writers and
`NUM_GEN` readers. **The design range is 1 to 8.** The register map reserves
all eight slots either way — `WR_GEN[0..7]` at 0x000 on a 0x40 stride,
`RD_GEN[0..7]` at 0x200 — so growing the array is a parameter and a bridge
regen, never an address-map migration.

What is actually built is smaller than the ceiling, and for a boring reason:

| `NUM_GEN` | fits the XC7A100T? |
|---|---|
| 8 + 8 | **no** — 66 470 LUTs against 63 400 available |
| 4 + 4 | yes, at 77% LUTs / 47% DSPs |
| **2 + 2** | **what the board builds** — proves multi-master behaviour with routing and timing headroom |

The invariant is `NUM_GEN <= NUM_BANKS`, not equality. Each generator is
expected to SPAN `NUM_BANKS/NUM_GEN` banks, so two generators still keep all
eight banks busy; the host gives each one a wrap window covering that span.
Nothing in hardware can enforce that, because the bank field's position is
pumice's runtime `ADDR_MAP.bank_lsb`, so the host asserts the mapping and reads
the compiled count back from `GEN_CONFIG` rather than assuming it.

**Launch is global on purpose.** Every generator is staged first — write its
config in any order, over as many bus transactions as it takes — and then all
of them start on one cycle from a single write to `GO`. A per-generator start
bit means the first generator has been running for however many microseconds
the host needed to program the last one; on the RAPIDS characterization that
skew alone produced 0%-utilization windows and a meaningless number.

### How an address is generated

Each generator walks a strided, optionally wrapped sequence
(`projects/components/misc/rtl/dma_address_gen.sv`):

    addr[i] = start_addr + ((i * stride_0) & wrap_mask_0)

`stride_0` is SIGNED, so a negative stride walks backwards; `wrap_mask_0` turns
the walk into a circular window of `mask+1` bytes; a mask of zero disables
wrapping and the walk marches linearly. The second dimension (`stride_1`,
`wrap_mask_1`) exists in the generator but is inert in this harness — one
(stride, wrap) pair fully defines the pattern.

That single pair is what makes the access FAMILIES, all defined in
`build-perf/host/pumice_char.py::strides_for`:

| family | stride_0 | wrap_mask_0 | what it exercises |
|---|---|---|---|
| `incremental` | one burst | none | contiguous march across the device |
| `row_major` | one burst | `page_bytes-1` | wrapped inside ONE page — every burst a page HIT |
| `col_major` | `row_stride_same_bank` | `device_bytes-1` | next row, SAME bank — a page MISS every burst |
| `col_major_interleaved` | `bank_stride` | `device_bytes-1` | next BANK every burst — activates pipeline across banks |

Per generator the host also programs burst length, transaction count, an
inter-burst gap, AXI size and burst type, and `id_mode` (a fixed AXI ID, or an
LFSR that issues multi-ID traffic so the controller's reordering is actually
exercised).

**Data is an address hash, not a counter.** In `data_mode` each beat carries
`f(byte_address, seeds)`, which is what makes the check order-independent: two
generators whose windows overlap write identical values to a shared address,
and a read verifies against the address alone regardless of the order writes
landed or returns arrived. A sequence counter would have made multi-ID and
multi-stream traffic unverifiable.

### What the stream count does and does not model

**Eight is the intended maximum, and the documented reason is one stream per
DRAM bank** — `NUM_GEN` is sized against `NUM_BANKS` on the 8-bank
MT47H64M16, and the harness asserts the two agree rather than trusting them to.
It came from a specific failure: the flat ~12.7 MB/s board result was the
arbiter falling back to a single oldest bank, and a harness driving ONE address
stream cannot tell that apart from a controller that refuses to go
bank-parallel. Eight independently addressed generators make bank concurrency a
property of the STIMULUS rather than of a hand-built address pattern.

So the "eight streams" target is a **bank-concurrency** argument, not a
server-workload model, and nothing in the tree claims otherwise. The distinction
matters because the two want different things:

* Bank concurrency wants N streams on DISJOINT, neighbouring banks, which is
  what the current profiles do.
* A server-like workload wants concurrent agents with DIFFERENT working-set
  sizes, burst lengths, read/write mixes and QoS classes, contending for the
  same banks — including the pathological case where two agents ping-pong rows
  in one bank set.

The generators can express all of that today: every one is independently
programmed, the directions are on separate bridges so the mix is a knob, and
pumice takes AXI QoS as a priority class. What does not exist is a PROFILE that
sets it up. The closest is `--char-profile multigen` (one writer, two readers,
disjoint regions), and the one heterogeneous case measured so far was an
accident — spacing two readers a device/4 region apart put them in the same
banks on different rows and collapsed row_major from 570 to 224 MB/s.

**On whether an OS would hand different applications different banks:**
generally no, and that is worth being clear about before anyone reads the
8-streams-on-8-banks arrangement as a model of real system software. Stock
Linux and Windows allocators are bank-unaware; they place physical pages by
availability and NUMA node, not by DRAM geometry. Worse for the idea, the usual
memory-controller address map *deliberately* interleaves consecutive cache
lines across banks to extract parallelism from a single stream, so even a
contiguous allocation is scattered across all banks by the time it reaches the
device — the OS could not keep two applications bank-disjoint without the
controller cooperating. Bank-aware and bank-partitioned allocation is a real
research line (page-colouring extended from caches to DRAM banks, for
predictability and isolation on mixed-criticality systems) rather than
something a general-purpose OS does today. So the per-bank stream arrangement
here is a STIMULUS construct for making bank concurrency observable, not a
claim about what software does. Pointing the generators at the same banks on
different rows is arguably the more realistic contention case, and it is the
one measured at 224 MB/s.

Two caveats before anyone scales the array up:

* **Two writers is unsafe today.** pumice returns B out of AW order across
  masters while the generated write bridge routes responses by FIFO position,
  so a second writer is silently misrouted. Readers are unaffected. Filed.
* **Region placement IS the measurement.** Generators placed adjacently land in
  neighbouring banks and measure arbitration; placed far apart they land in
  different ROWS of the same banks and measure page thrash instead. The
  difference was 570 against 224 MB/s on identical traffic.

---

## Measured on silicon — bandwidth and % of peak under load

Every number below is from the Nexys A7, not simulation: 75 MHz controller
clock, DDR2-300, BL4 on the x16 MT47H64M16. **Peak is 600 MB/s** (8 B per
controller cycle). Raw CSVs in `docs/char_results/`; reproduce with
`build-perf/host/pumice_master.py --char`.

### Single stream, one direction at a time (`open_page`)

| access pattern | AxLEN | write MB/s | % peak | read MB/s | % peak | rd latency |
|---|---|---|---|---|---|---|
| row_major (page hit) | 8 | **570.2** | **95.0%** | **571.2** | **95.2%** | 48.9 |
| row_major | 16 | 570.3 | 95.0% | 571.3 | 95.2% | 48.9 |
| row_major | 4 | 570.3 | 95.0% | 360.4 | 60.1% | 48.0 |
| incremental | 8 | 551.3 | 91.9% | 556.9 | 92.8% | 49.4 |
| incremental | 16 | 551.3 | 91.9% | 557.0 | 92.8% | 49.4 |
| incremental | 4 | 551.3 | 91.9% | 357.4 | 59.6% | 48.4 |
| col_major_interleaved (bank walk) | 16 | 311.3 | 51.9% | 331.7 | 55.3% | 49.8 |
| col_major_interleaved | 8 | 208.9 | 34.8% | 229.3 | 38.2% | 85.7 |
| col_major_interleaved | 4 | 196.6 | 32.8% | 213.8 | 35.6% | 70.6 |
| col_major (page thrash) | 16 | 262.1 | 43.7% | 262.1 | 43.7% | 96.0 |
| col_major | 8 | 163.8 | 27.3% | 172.0 | 28.7% | 96.0 |
| col_major | 4 | 98.3 | 16.4% | 102.4 | 17.1% | 96.0 |
| col_major, multi-ID (LFSR) | 8 | 163.8 | 27.3% | 172.0 | 28.7% | 96.0 |
| col_major, 8-cycle inter-burst gap | 8 | 163.8 | 27.3% | 172.0 | 28.7% | 96.0 |

All 14 points integrity-clean. Reading this table:

* **Page locality is the dominant term, not the controller.** The same silicon
  and the same settings give 95% on a page-hit stream and 17% on a page-miss
  one. A 5.6x spread from the ADDRESS PATTERN alone is the single most useful
  fact on this page: tune the address map before tuning the controller.
* **Bank interleaving recovers roughly half of the thrash penalty** (col_major
  17% -> col_major_interleaved 36% at AxLEN 4) because activates pipeline
  across banks instead of serialising in one.
* **Small-burst reads are LATENCY-bound, and that is a known bug.** AxLEN 4
  reads reach 60% against a 95% write on identical addresses. This is Little's
  law on the read generator's 8-outstanding-burst budget against pumice's
  ~49-cycle read latency, confirmed by a five-point sweep (AxLEN 1/2/4/8/16
  predicted within 2%, table in *Status*). The generator budget is the
  proximate cause; the latency is the defect, and halving it to LiteDRAM's
  24.7 cycles would make the shortfall disappear from AxLEN 4 up. Writes are
  immune because B returns at CAM commit, not after a DRAM round trip.
* **Multi-ID traffic and inter-burst gaps cost nothing** here; both land
  bit-identical to the fixed-ID back-to-back case, which says the reordering
  machinery is not the limiter at this operating point.

### Both directions at once, in ONE measurement window

Every row above runs a write phase and then a read phase, so read/write
turnaround is never paid. These run both together, which is the workload the
reorder window exists for:

| load | write MB/s | read MB/s | **total** | % peak |
|---|---|---|---|---|
| 1 writer + 1 reader, row_major bl8 | 285.0 | 285.0 | **570.1** | **95.0%** |
| 1 writer + 1 reader, incremental bl8 | 276.3 | 276.3 | 552.6 | 92.1% |
| 1 writer + 2 readers, row_major bl8 | 190.1 | 380.2 | **570.2** | **95.0%** |

**pumice holds ~95% of peak with one, two or three concurrent generators**, and
the split follows the generator mix rather than collapsing. For contrast, the
same harness driving LiteDRAM on the same board and PHY reaches 285.6 MB/s
total on the 1+1 case — pumice is **2.00x** there, which is the one place the
extra area pays for itself.

The `col_major` rows are deliberately absent from the concurrent table: those
families walk the whole device, so concurrent generators cannot be placed on
disjoint regions and the integrity check does not hold. They are reported as
not-measurable rather than quoted.

### What this establishes

The controller has seen silicon under a real DRAM at a real operating point,
across page-hit, page-miss, bank-interleaved, multi-ID, gapped, single-stream
and multi-stream loads, with data integrity checked byte-by-byte on every
point. The headline is not the 95% — it is that the 17% and the 95% come from
the same bitstream, and the table says which lever moved between them.
