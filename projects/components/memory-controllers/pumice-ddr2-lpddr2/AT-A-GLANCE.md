# pumice — at a glance

A DDR2/LPDDR2 memory controller. One index page: every feature area, 1-3
bullets each, so you can find the right file without reading the tree.

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

## Runtime modes — three independent axes (PUMICE-006)

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
| 1 `in_order` | **strict FCFS** — only the single oldest reference across both CAMs may pick. No lookahead, no row-hit reordering |
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

* **Tiers** — `dv/tests/fub` (21 files), `dv/tests/macro` (4),
  `dv/tests/top` (5), plus PHY-facing checks at the root of `dv/tests`.
  22 TB classes in `dv/tbclasses/`. 210 tests at FULL
  (`make clean-all && make run-all-full-parallel`); a bare `pytest` runs the
  FUNC subset only and under-reports.
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
