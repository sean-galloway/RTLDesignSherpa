# Pumice performance bracketing: every stimulus axis

How pumice's bandwidth and latency have been bracketed, on the board and in
sim. The list covers every deterministic (algorithmic) access pattern, every
seeded pseudo-random element, and the constrained-random tests that sit beside
them. Each item names the code that implements it, so a number can be traced
back to the stimulus that produced it.

Sources:

- the char engine `build-perf/host/pumice_char.py`;
- the family builders `half_burst_family.py` and `perf_mixed_family.py`, and
  `dv/tests/perf_half_rot_family.py`;
- the perf proxy `ddr2_char_framework/dv/tests/test_ddr2_char_perf.py`;
- the board sequences in `bin/seq_*.py`;
- the pumice DV tests under
  `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tests/top/`.

## 1. The two kinds of bracket

| Kind | What varies | Oracle | Where |
|---|---|---|---|
| Algorithmic | A deterministic address walk, picked so the DRAM behaviour is known by construction (all hits, all misses, bank hops) | Bandwidth, latency, page telemetry, stall counters | `pumice_char` on the board, and the perf proxy in sim |
| Seeded pseudo-random | LFSR address index, LFSR AXI IDs, address-hash data, all from fixed seeds | The same perf counters, plus exact data checks | The same engines; the `random` family and `id_mode=LFSR` |
| Constrained random | AXI handshake timing, burst order, length, ID, QoS, delay, and the controller config vector | Data integrity against a golden memory model, plus telemetry invariants. Never bandwidth | Pumice top-level DV: `random_soak`, `config_sweep`, `config_soak` |

Almost all of the performance bracketing is algorithmic. Randomness enters
the perf numbers only through seeded LFSRs, so every cell can be replayed
exactly. The truly constrained-random tests bracket correctness across the
config space, not throughput. Randomized traffic does not prove that an
arbiter or scheduler performs well; see the `rds-dv-randomization` skill.

## 2. Measurement machinery (shared by every cell)

- **Meters.** `axi_bus_meter` counts productive, backpressure, starvation and
  idle cycles on R and W. `axi_perf_latency_hist` keeps a log2 latency
  histogram:
  - reads: AR to first R, and AR to RLAST;
  - writes: AW to B.

  Exact `rd_lat_mean/min/max` registers have existed since 2026-10-31.
- **Window discipline.** Clear the counters, unfreeze, run, then **freeze**
  before reading back over the UART. Reading unfrozen inflates idle by
  thousands of cycles.
- **Bandwidth formula.** `bytes_moved / cycles * clk_mhz`, using the on-chip
  first and last stamp of each engine. `clk_mhz` is measured off the board
  (`resolve_clk_mhz`), never taken from a constant. A wrong constant once
  reported 123 percent of the port's peak and still said PASS.
- **Controller telemetry.**
  - `PAGE_STATS`: hit, miss (conflict ACT), empty (cold ACT), plus ACT and
    PRE counts;
  - `STALL_*`: the limiter, such as `starved` or `turnaround`;
  - `STORE_STATS_MERGE` and `STORE_STATS_RD_MERGE` for the combiners.
- **JEDEC floor (perf proxy only).**
  - read gap floor = tRTP + tRP + tRCD;
  - write gap floor = tWR + tRP + tRCD.

  Each col_major number is printed next to its floor. The silicon gates are
  `row_major` 570, `col_ilv` 354 and `col_major` 369 MB/s.
- **Integrity on every cell.** In address-hash data mode, the data is
  f(addr, seeds), so a reader checks every byte without assuming any order.

## 3. Controller axis: `ControllerConfig` presets (`CONFIGS`)

Each preset changes one lever from a reference corner, so a difference between
two cells can be attributed to that lever. Every preset reprograms all of its
fields on each apply, so results do not depend on the order the presets run in.

| Axis | Presets |
|---|---|
| Power-on reference | `defaults` (paging fields at the RDL reset values, read from the regmap) |
| Reference corner | `close_page` (row-major map, close page, FR-FCFS) |
| Address map | `bank_interleave`, `open_interleave` |
| Static page policy | `open_page`, `close_page` |
| Scheduling order | `inorder`, `inorder_open`, `age_thr` (age threshold = 8) |
| Arbiter sub-policies (TASK-002 axis 1, on open page) | `prio_load_over_store`, `prio_age_boost`, `row_most_pending`, `row_fewest_pending`, `col_most_pending`, `col_fewest_pending`, `qos_on`, `pref_column_first`, `pref_row_first` |
| Page-timeout ladder (mode 3) | `fixed_open_tr{1,2,3,4,8,16,32,64}` |
| Hybrid page mode (mode 4, since 2026-10-30) | `hybrid_tr{1,2,4}` |
| Auto-precharge datapath isolation | `static_close_mode2` (drives `ap_close_o`, which `close_page` never does) |
| Refresh, close page | `fast_refresh` (tREFI 0x100), `slow_refresh` (0x7FFF), `refresh_credit` (postpone 8 / pull-in 8) |
| Refresh, open page | `open_page_fastref`, `fast_refresh_open`, `slow_refresh_open`, `refresh_credit_open` |

`DEFAULT_MATRIX` is `defaults, close_page, bank_interleave, open_page,
inorder, age_thr`.

## 4. Algorithmic access-pattern families

### 4.1 One-dimensional stride families (`strides_for`)

Each family is a single `(stride_0, wrap_mask_0)` pair on one
`dma_address_gen` dimension, so addr[i] = base + (i * stride & wrap). The
default geometry is the board's: column [10:0], bank [13:11], row [14+].

| Family | Stride / wrap | DRAM behaviour by construction | What it brackets |
|---|---|---|---|
| `incremental` | one burst, no wrap | Linear march: hits until each row crossing | Sequential best case |
| `row_major` | one burst, wrap = page - 1 | **Every burst a page hit** | Back-to-back column throughput in one row |
| `col_major` | one row in the same bank, wrap = device - 1 | **Every burst a page miss** (PRE + ACT) | Worst case; exposes tRC, tRP and tRAS |
| `col_major_interleaved` (`col_ilv`) | one bank, wrap = device - 1 | Bank hops; activates pipeline | Bank-level parallelism recovered |

Two ratios are flagged in the summary:

- `incremental / col_major` gives the page-management penalty;
- `col_ilv / col_major` gives the bank parallelism recovered.

The device-boundary wrap on `col_major` and `col_ilv` is required. Without it,
the address hash uses the pre-wrap address and every pass reports a false
mismatch.

### 4.2 Window families (`perf_mixed_family.py`; on the board since 2026-10-29)

These are the shapes where scheduling-window depth pays off. A one-dimensional
stride cannot express them.

| Family | Construction | What it brackets |
|---|---|---|
| `mixed` | Generators paired on a bank, one row apart. Each walks its own row in row-major order. Reads and writes run concurrently (one GO), and the write and read regions are rows apart in the same banks. | Row-hit grouping across requestors, plus read/write turnaround and cross-direction bank conflicts. Needs at least 2 generators. |
| `row_thrash` | One thread, one bank, two rows, a burst to each in turn (`idx1_shift=1`). Thread g owns bank g. | The textbook row-buffer conflict. A row-hit scheduler serves the A hits then the B hits; an oldest-first per-bank picker pays an ACT per burst. |
| `random` | An LFSR address index (`addr_lfsr=1`) over two rows across all banks. Thread g owns rows 2g and 2g+1. | A hit/miss mix in random order (seeded, see section 6) |

### 4.3 Half-burst families (`half_burst_family.py`, TASK-060)

Each host transaction is half a DRAM burst: at the board geometry, one 4-byte
narrow beat with strobes. The family sets the order the halves arrive in.

| Family | Order | Pacing |
|---|---|---|
| `half_pair` | l0 h0 l1 h1 ... (index bit k = 0) | No gap |
| `half_oct` | l0..l7 then h0..h7 (k = 3) | No gap |
| `half_pair_sweep` | Same order as `half_pair` | Gap = gap + (n mod 8), looping 0..7 inside one run |
| `half_oct_sweep` | Same order as `half_oct` | Gap loops 0..7 |

Two readouts show the write combiner at work:

- merges / host writes, from `STORE_STATS_MERGE`;
- column ops / host writes: 0.5 when every pair merged, 1.0 when none did.

IDs rotate per transaction (COUNTER mode, 32 IDs per thread). With FIXED IDs,
AXI B-ordering would forbid every merge after the first.

### 4.4 `half_rot<d>` (`perf_half_rot_family.py`, proxy only)

The two halves of each burst arrive **d transactions apart**, where d is a
power of two, on eight threads in one line. Sweeping d shows where
aggregation stops. The read pass sends the same programs through the read
combiner (`STORE_STATS_RD_MERGE`), whose window is shorter: the second half
must arrive before the first half has *issued*.

### 4.5 Hot/cold mix (`hotcold_scenarios`, TASK-011 / TASK-013)

- **The mix.** N-1 generators are hot: `row_major`, so many column ops per
  activation. One is cold: `col_major` at `cold_blen=2`, which is exactly one
  16-byte column op per activation. All of them share one bank.
- **Why it exists.** It is the only stimulus where locality varies by row, so
  it is the only workload on which a per-row page predictor can beat both open
  page and close page.
- **How to read it.** Use thrash% and ACT per transaction, not MB/s.
- **Knobs.**
  - `n_hot` sets the hot:cold ratio: 3:1, or 2:2 where open and close page
    nearly tie;
  - `bank_spread=2` spreads two bank groups so precharges compete for
    command-bus slots;
  - `same_bank_rows=8` keeps the cold walk below the predictor table's
    6-bit fold.
- **The `confine_mask` rule.** The mask must be coarser than the stride, or
  the generator emits one address forever. Every "adapt_access is inert"
  result from before 2026-09-26 was taken on that broken stimulus.

## 5. Generator-side axes (`Scenario` fields and `measure_concurrent`)

| Axis | Values used | What it brackets |
|---|---|---|
| `burst_len` (AxLEN + 1) | 4, 8, 16 (medium and full levels); 1 for the half families; 2 for hot/cold cold engines | Burst amortisation of ACT/PRE |
| `txn_count` x `txn_scale` | Base 8 (basic) or 64; times 1 in sim, about 1000 on the board; clamped to 16-bit `TXN_MAX` | Window length for stable meters |
| `gap` | 0; 8 (`col_major_bl8_gap`); a 0..7 sweep (`half_gap`); the injector's `gap_sweep` | Idle recovery, merge-window closure, refresh interaction |
| `max_outstanding` | 0 = as built (32), or swept through `CHAR_SC_OVER` | The latency cliff: read BW is bounded by outstanding x AxLEN / (latency + AxLEN) |
| `threads` | 1..8 (`half_threads`), 4 (`windows`); clamped to the 4 injectors per direction the bitstream has, with a note on the record | Combiner merging as threads interleave at the port |
| `concurrent=(n_wr, n_rd)` | (1,1), (1,2), (0,4) | Turnaround (tWTR/tRTW), multi-master arbitration; (0,4) isolates the pick from turnaround |
| `placement` | `regions` (adjacent power-of-two regions, the default), `banks` (writers on even banks, readers on odd), `same_bank` (hot/cold) | Placement decides what is measured. Regions spaced far apart measure page thrash, not arbitration. |
| `id_mode` | FIXED, COUNTER, LFSR | Single-ID vs out-of-order-capable traffic (whether it is reordered is the config's `order_mode`) |
| Timing overrides (proxy) | `TEST_TIMING_OVERRIDES="tRTP=1,tRP=2"` | Like-for-like timing what-ifs with the RTL untouched |
| Scheduler core (proxy) | `TEST_SCHED_CORE` (BANK_PICK vs FRFCFS), `TEST_ACCESS_PREF` | Pick-core A/B on identical stimulus |

The direction-mixed bank-gap knee and the concurrent-gap corruption hunt
(PUMICE-036/037) were run as `measure_concurrent` with `placement="banks"`
across gaps 0..15.

## 6. Seeded pseudo-random elements (all replayable)

| Element | Mechanism | Seed |
|---|---|---|
| `random` family address | 16-bit LFSR replaces the transaction counter (`addr_lfsr`) | `gen_seed(g) = PERF_SEED + 0x1000*g (+0x100000 per direction region)`, with `PERF_SEED = 0xABCD1234` |
| AXI IDs | `id_mode=LFSR` (`*_multiid` scenarios: col_major at medium, every family at full) | Engine LFSR seed |
| Data | Address hash f(addr, seed0..2); hash seeds derived from the generator seed | `seed_fields()` |
| Per-scenario seed (stride families) | FNV-1a of the scenario name (`_stable_seed`); Python `hash()` is avoided because it changes per process | The scenario name |

`perf_mixed_family` holds the single seed, and the pumice, granite and
LiteDRAM proxies all import it. A grid cell is therefore the same address
stream and data stream on every controller, and every record carries the
seeds it ran with.

## 7. Constrained random (correctness across the config space)

None of these produce perf numbers. They bracket the space the perf cells
assume works.

| Test | What is randomised | Oracle |
|---|---|---|
| AXI timing profiles (`set_axi_timing_profile`: `backtoback`, slow producer, constrained) | BFM valid/ready timing, seeded from `SEED` | Golden memory model |
| `random_soak` (test_pumice_top) | Burst order, length (up to 16), ID (8), QoS, inter-burst delay (up to 8); 16/64/256 bursts by level | Golden model per transaction address; **fails if fewer than 4 distinct lengths were drawn** |
| `engine_mirror` | `ENG_PROFILE` timing profile; `ENG_ID_MODE` fixed / counter / LFSR | Golden model |
| `patho` | Pathological address kinds (`PATHO_KIND`, e.g. `bank_hazard`) under a timing profile | Golden model |
| `test_pumice_config_sweep` (TASK-015 plane 1) | A pairwise covering array: 39 vectors over 15 runtime mode selectors, every 2-way combination present, crossed with read gap {0,4,8,15} and direction {sequential, concurrent}: **312 cells** at full | Data integrity plus telemetry invariants |
| `config_soak` (TASK-015 plane 3) | Seeded random config vectors, which reach 3-way interactions and beyond over time | The same; a failure message carries seed, round and vector ID so it becomes a pinned cell |
| `seq_telemetry` (board, TASK-015 layer 2b) | Telemetry invariants on silicon | Counter identities |

The covering array exists because of pumice BUG-003: `policy_mode=3` crossed
with `rd_gap>=8` was a 2-way interaction, and single-field coverage had
called it green.

## 8. Run profiles (`RUN_PROFILES`): the named brackets

`run_profile(drv, name)` runs the same program in sim and on silicon; only
`txn_scale` differs. Environment variables can narrow one cell for a repro:

- `CHAR_CONFIGS`
- `CHAR_FAMILIES`
- `CHAR_THREADS`
- `CHAR_SC_OVER="field=int,..."`

| Profile | Configs | Stimulus | Brackets |
|---|---|---|---|
| `smoke` | close_page, bank_interleave, open_page, inorder | incremental, col_major (basic) | Config-apply path, best vs worst case |
| `matrix` | `DEFAULT_MATRIX` | 4 families x BL {4,8,16} + multiid + gap | One lever per axis |
| `full` | all presets | full level | Everything |
| `every` | defaults, open, close, bank_interleave | 4 families at full | Cross-controller pattern matrix (granite, LiteDRAM) |
| `windows` | defaults, open, close | mixed, row_thrash, random, 4 threads | Window-depth payoff |
| `paging_grade` | open, close | all families | A falsifiable telemetry check: row_major and col_major must land at opposite ends of the hit-rate column |
| `paging` | open_page, fixed_open_tr2 | incremental, col_major | Timeout vs none |
| `default_candidate` | open_page, fixed_open_tr{1,2,4} | medium grid | "Does tr2 ever lose?" before shipping a default |
| `paging_default_allfam` | open_page + tr{1,2,3,4,8} | 4 families, **no gen_mix** | Per-family optimum of the TR ladder |
| `bug003_tr_floor`, `ap_vs_bgpre`, `ap_port_probe` | TR ladder / AP vs background PRE / mode 2 | hot/cold 2:2 on 2 banks, (0,4) | Smallest safe TR; AP mechanism vs policy; `ap_close_o` on hardware |
| `hotcold` | open_page | hot/cold 3:1, (0,4) | Per-row locality variation |
| `order` | open_page, inorder, inorder_open, age_thr | incremental, col_major | Order modes |
| `sched_sub` | open_page + 9 sub-policies | (0,4) readers only, outstanding 32 | Arbiter tie-breaks with the pick saturated and turnaround removed |
| `refresh`, `pairs_refresh_open` | refresh presets on close / open page | families | Refresh elasticity |
| `concurrent`, `pairs_paging_mix`, `multigen` | defaults / open | (1,1), (1,2) | Turnaround; multi-master (one writer only: BUG-012) |
| `half_burst`, `half_burst8` | defaults, close, open | 4 half families, 1 or 8 threads | Write-combiner merge |
| `half_threads` | defaults, close, open | pair, oct x threads 1..8 | Where merging stops as threads interleave |
| `half_gap` | defaults, close, open | pair, 1024 txns, gap 0..7 one cell each | Where the merge window closes |
| `open_min`, `close_page_min`, `multiid_min` | single config | col_major | Minimal repros for waveform debugging |

Two traps:

- A profile that pins its own `families` ignores the CLI `--families`.
- `gen_mix="hotcold"` overrides the family's generator shape. Listing four
  families with it measures one workload four times; the first
  `paging_default_allfam` did this and reported identical numbers to 0.1 MB/s.

## 9. Board sequences that bracket outside `char`

| Sequence | Bracket |
|---|---|
| `seq_page_policy` | OPEN vs CLOSE A/B per family through `measure`; read-BW ratio |
| `seq_wr_batch` | Write-batching watermark (`SCHED_WR_WM`) A/B at the gaps where turnaround bites, then **repeats** at the chosen and aggressive settings: one pass cannot tell 0 percent from a low-rate intermittent (BUG-014 / BUG-018) |
| `seq_telemetry` | Counter invariants on silicon |
| `seq_ocelus` | Monitor-on completions and error counts, and record and drop counts under traffic (granite, 2026-11-02) |
| `pumice_master.py --soak --minutes N` | Timed soak to CSV |

## 10. Fidelity limits to keep in mind

- **DFI-loopback sim does not model DRAM page timing.** In it, the families
  move identical data in identical time. It validates the mechanism; the board
  supplies the MB/s.
- **The perf proxy does model the timing.** It runs `DFISlavePHY` plus
  `DramStateModel` with JEDEC timings derived at the board clock, so its
  numbers are comparable to the board's.
- **Page counters are valid in either sim** (`paging_grade`), because they
  count scheduler decisions, not DFI timing.
- **Sim-sized runs are too short for the mode-4 adapt loop.** At
  `txn_scale=1` the loop never fires, so the adaptive-TR verdict comes from
  the board only.
- **Mode 5 diverges between sim and board.** Sim refresh pressure is about
  117x the board's per activation, so a predictor result in sim can be a
  refresh artefact.
- **The bitstreams carry 4 injectors per direction**, so `threads` above 4 is
  clamped. The record notes the clamp.
