# Memory-controller recovery: single-bank parity with LiteDRAM on one plane contract

Date: 2026-10-21
Status: assessment + plan for owner approval. Nothing here is implemented.
Scope: `projects/components/mem-ctrl-ip/` (common-ip, pumice as reference, granite
as the first drop-in consumer). Supersedes the parked
`2026-10-20-pumice-100mhz.md` plan (see section 6 for what survives from it).

---

## 1. Where things actually stand (measured, not remembered)

### 1.1 Performance

Board A/B through the identical `char_engine_block` harness, 75 MHz / 1:2 /
DDR2-300 (`FINDINGS_litedram_ab_2026-10-03.md`), and the board-free sim proxy
(`test_granite_char_perf.py`, 75 MHz, tREFI=585, txn=1024, JSONs in
`ddr2_char_framework/dv/tests/logs/`):

| pattern | pumice FRFCFS (board 10-03) | FRFCFS (sim proxy) | per-bank core (sim, 10-18) | LiteDRAM (board) | JEDEC floor at pumice's programmed timings |
|---|---|---|---|---|---|
| row_major wr / rd | 570 / 572 | 568 / 571 | 578 / 562 | 569 / 579 | 600 peak |
| col_major (same-bank row walk) wr / rd | 192 / 195 | 213 / 229 | 262 / 293 | 304 / 386 | 320 / 369 |

Streaming parity was reached on 2026-09-10 and holds. **The open gap is
single-bank row walking, and it is a pipeline-latency gap, not a bandwidth
gap.** Read from the command-gap histograms (`perf_dump_colfix2.json.gaps.json`):

- One AXI txn in col_major is 8 columns to one row, then the next row in the
  same bank. The 8 columns always fire at gap 1. Everything is in the inter-row
  gap: last column, PRE, ACT, first column.
- Floor at the programmed cycles (tRTP 2, tRP 2, tRCD 2; tWR 4): **rd gap 6,
  wr gap 8** → 13 / 15 cycles per 64-byte row → 369 / 320 MB/s.
- Per-bank core measured gap **9 / 11** (+3 over floor: one cycle lost per
  dependent hop, three hops).
- FRFCFS core: 21.5 cycles per row → gap **~14.5** (+8: each hop re-enters the
  5-stage pick pipe).
- LiteDRAM: 12.4 cycles per row → gap ≈ 5.4. Read from the generated
  `bankmachine0` FSM (`flows-litedram-uart/gen/board/gateware/litedram_core.v`):
  the column with auto-precharge is followed by one tRP-1 wait state and, after
  the ACT, one tRCD-1 wait state, so tRP = tRCD = 2 cycles, the same as pumice.
  The netlist carries NO tRAS, tRC or tRTP counters at this operating point
  (`trccon_ready` is a constant 1; `trascon` has no counter register), so the
  row-switch gap is 5 FSM cycles: column, precharge-state, tRP wait, ACT, tRCD
  wait, column. Pumice's floor is 6 because it enforces tRTP = 2 before the
  precharge, and that 2 is itself the phase-margin-padded derivation of a
  7.5 ns part spec (one bare MC cycle). Writes: LiteDRAM loads tWTP = 3 and
  lands at gap ≈ 8.8; pumice's tWR port derives 4, floor 8.

**Consequence for the target.** "Parity with LiteDRAM on single-bank" has two
parts: (a) the controller must issue dependent commands at the JEDEC floor,
and (b) the comparison must name which rules each side enforces. LiteDRAM
skips tRTP; pumice pays a padded 2. One cycle per row is 8% on col_major, so
the owner's ±2% criterion is only meetable like-for-like: the proxy's
`TEST_TIMING_OVERRIDES="tRTP=1"` makes pumice's rule set match LiteDRAM's
actual behaviour without touching RTL, and every number is reported beside
the floor at the timings actually programmed.

### 1.2 Timing (the real reports, post-route, Nexys A7 -1)

| build | core / storage | WNS @75 MHz | notes |
|---|---|---|---|
| pumice `build-perf` 2026-10-15 | FRFCFS + CAMs | **+0.122 ns** | `build-perf/fpga/reports/timing_summary.txt` |
| granite `targets/stable` 2026-10-15 | FRFCFS + entry store | **+0.008 ns** | the shipping granite bit |
| granite seat-pending per-bank (c1dab8e00) | 0-stage `mc_bank_sched` + entry-store head scans | -1.35 plain / -0.73 directed | MC-003 §12 |
| granite registered-pick per-bank | registered `r_pick` + head2 bypass | -3.94 | MC-003 §14 |
| granite aged-matrix (13691eefb / fc9848135) | `mc_age_fifo` x16 + `mc_matrix_arbiter` | **-33.4 / -35.6** | the "-38 ns" build; reverted e95d676a8 |
| pumice OOC synth-only, 100 MHz | FRFCFS + CAMs | aclk -13.2, dfi_clk -2.8 | `pumice-100mhz-baseline-2026-10-20.md` |

Two things follow. The 100 MHz plan's premise that "Stage B is still required
even for 75 MHz" is contradicted by the post-route reports: both FRFCFS builds
close at 75 MHz today. And the only core that reaches the perf floor
(per-bank) has never closed timing in any of its three shapes.

### 1.3 Why the FIFO storage plane blew up to -35 ns and the CAM plane did not

The worst path in the committed granite report is
`u_entry_store/g_age_fifo[1].u_rd_fifo/r_row_reg[6][10] -> u_bank_sched/r_winner_reg[col][8]`
(-33.4 ns, 53 levels, 80% route); in the working-tree report it is
`r_winner_reg[bank][0] -> r_winner_reg[row][5]` (-35.6 ns): the winner register
feeds its own next value through the whole decision. Tracing the reverted
`mc_bank_sched.sv` (fc9848135), one cycle contained, in series:

1. `r_winner.bank/is_rd` → `w_use_head2[pair]` (which pair must present its
   second entry because its head is firing now).
2. Per-pair head/head2 **age** select (16 x 6 bits) → a **16-way age minimum**
   (comparator tree) → equality mask to the minimum.
3. `mc_matrix_arbiter` (16x16 AND-OR) → one-hot pair → `w_sel_*`.
4. Payload mux: 16:1 over ~38 bits, where each input is itself the FIFO's
   **pointer-indexed read** `r_row[r_rptr]` inside `mc_age_fifo` (comb array
   view, 8:1 per field, crossing the plane boundary as ~1300 wires).
5. `winner_stale` compare (slot + row vs live view) and the live JEDEC fire gate
   in the same cycle, both feeding the winner-load condition.

Three structural sins, all absent from the CAM path: comb array views cross
the plane boundary; a global age-minimum (a compare tree) sits in the loop
where the CAM uses an insert-time N x N `older` matrix (oldest = one AND-reduce
per entry, two levels); and decide == fire == next-decide in one cycle. The
FRFCFS core has flat per-entry **registered** vectors, matrix age, and four
register stages, so each stage is a third of the cone. It pays for that with
the +8-cycle hop penalty. The two cores sit at opposite corners of the same
trade: pick latency vs cone depth. Neither corner is where LiteDRAM is.

The owner's 2026-10-19 contract rethink (MC-003 evidence §17) already names the
cure: plane-to-plane signals are registered snapshots plus handshakes, never
comb probes, and a flag that depends on state from two planes is computed in
the plane that owns the decision.

### 1.4 The parked 100 MHz plan

Tasks 1-2 done (baselines, four contract cells), Task 3 Stage A committed
(bf53f9556), Stage B is a 1578-line unverified rewrite in
`.superpowers/sdd/2026-10-20-pumice-100mhz/task-3-stageB-scratch-mc_cmd_arbiter.sv`
that fails `cocotb_test_hold_on_gate_block` because the contract TB ties
`bank_*_ready_i` to `'1` (`mc_store_arbiter_macro_tb_top.sv:276-278`), so the
gate-block can never be created. Even finished, Stage B restructures the
FRFCFS cone but keeps the pipeline depth, so it does not move col_major.

---

## 2. Target architecture

LiteDRAM's shape, built out of this repo's planes, with the storage backend
swappable behind one registered contract.

```
 storage plane (ANY backend)            scheduler plane                    DFI plane
 ┌──────────────────────────┐   regs    ┌─────────────────────────────┐   cmd/wd/rd
 │ per (dir,bank):          │ ───────▶  │ 16x per-bank decode         │   packed
 │   head record  (reg)     │ {head,2nd}│   hit = head.row==open_row[b]│ ─────────▶ (2p1 | 4p0,
 │   2nd  record  (reg)     │           │   op  = ACT|COL|PRE from     │             unchanged)
 │ wr data (BRAM) drain ───────────────────────▶ bank_*_ready_la (LA=D)│
 │ pops on fire handshake   │ ◀───────  │ req[16] (reg)               │
 └──────────────────────────┘ commit/   │ RR/age arbiter → r_winner   │
                               issue    │ fire gate: LIVE timers for  │
   CAM backend: per-bank oldest         │   r_winner.bank only, hold- │
   via its older matrix, registered     │   on-not-fired              │
   FIFO backend: 16 small FIFOs,        │ payload = record[r_winner]  │
   registered head/2nd (prefetch)       │ maint/REF override (as-is)  │
                                        └─────────────────────────────┘
```

### 2.1 The contract (`mc_common_pkg`, one struct, every backend)

Per (direction, bank), **registered**, updated only on push / pop / aging tick:

```
typedef struct packed {
  logic              vld;
  logic [ROW_W-1:0]  row;
  logic [COL_W-1:0]  col;
  logic [PTRW-1:0]   slot;     // commit/issue handle
  logic [IW-1:0]     id;
  logic              last;     // wr: last sub-burst (B consolidation)
  logic              behind_empty; // no younger entry in this bank's queue
  logic              age_exceed;   // backend-private aging policy, flag only
} mc_head_rec_t;
```

Bus: `wr_head_i[NUM_BANKS]`, `wr_head2_i[NUM_BANKS]`, `rd_head_i[...]`,
`rd_head2_i[...]`. Handshakes unchanged: `wr_commit_valid/slot`,
`rd_issue_valid/slot`, `rt_alloc_*`, `rd_iss_*` tickets. Config in:
`sched_age_thresh_i`, aging tick `sched_decr_i`.

Removed from the boundary: `wr_sch_*` / `rd_sch_*` N-wide vectors and
`*_older` matrices (they stay inside the CAM backend), `bank_open_row` /
`bank_row_active` into storage, the `*_bh_act` hit flags, the `bh2` comb
views. The snarf probe stays an optional sideband.

Rule (promote to the handbook): **a plane's internal state never leaves the
plane as a combinational input to another plane.** Head records are flops
driven by the backend's own output stage, not array reads.

### 2.2 The pick core (`mc_bank_pick`, new FUB; replaces `mc_bank_sched`)

- **Per-bank decode (16 copies, ~5 levels each).** Inputs: one head record,
  one bank's registered open-row and `bank_*_ready_la` (LA = pipeline depth
  D, see below), the direction-turnaround and tCCD-forward windows. Output:
  `req[pair]` and `op[pair]` (ACT / COL / PRE), both registered.
  `AP` (RDA/WRA) when the head is a column and `2nd` is a different row or
  `behind_empty` — the exact per-bank CLOSE_ON_DRAIN; the FRFCFS
  youngest-same-row heuristic (BUG-027) is gone.
- **Arbiter.** Round-robin rotor over the 16 request bits with age_exceed and
  write-batching watermark as priority overlays; optional matrix arbiter.
  Output registered: `r_winner = {vld, is_rd, bank, op}` (pair-only, ~7 bits).
  The payload is NOT in this loop.
- **Fire stage.** `cmd_valid = r_winner.vld && live_gate(r_winner.bank, op)
  && cmd_ready_i`, where `live_gate` is a 16:1 select of the live
  `bank_*_ready_i` bits ANDed with the global windows and the refresh/tRFC
  demand blocks. Payload = `record[r_winner.pair]` (16:1 x 38 bits, parallel
  with the gate). Hold-on-not-fired: a failed gate holds `r_winner`; nothing
  is dropped, nothing re-picks. Fire pops the storage head; the record
  refreshes next cycle.
- **Single-bank 1 column/cycle.** While `r_winner` is a column for pair p and
  `head2[p]` is a same-row column, the decode for p requests from `head2`
  (the owner's 2-deep contract exists for exactly this; it is what
  `w_use_head2` did, now on registered records). Gate: the existing
  `cocotb_test_zero_bubble_stream` cell.
- **Floor-exact dependent hops.** The loop fire → bank timer → decode → req
  (reg) → winner (reg) → fire is D = 2 register stages beyond the timer.
  Decode on `safe_*_la` with LA = D so the request lands exactly when the
  live gate opens. `mc_bank_timer` already has LA and `mc_bank_timers` already
  plumbs `BANK_LA`; the pumice CLAUDE.md "LA saturates at 3" note was about the
  FRFCFS pipe. A too-early winner simply holds one cycle (hold, not drop).
- **Maintenance/refresh/init override.** Lift verbatim from `mc_bank_sched`:
  `w_ref_dmd_block`, `w_rfc_dmd_block`, `r_actfire0` grant gate,
  `rd_ret_busy` return-window gate, all-idle grant semantics. These were
  bought with four days of MC-003 debugging; do not redesign them.
- **Budget.** Every stage ≤ ~8 LUT levels, all inputs flops: closes at 75 MHz
  with margin on this part, and is the first shape with a credible 100 MHz
  story. Nothing wide crosses a plane boundary unregistered.

### 2.3 Where the pick lives (reconciling MC-003 §17.1 and §17.3)

§17.1 mandates per-bank {head, 2nd} records; §17.3 proposes the storage plane
present one winner record. Build `mc_bank_pick` as a standalone FUB that
consumes the 16 records plus a registered bank image. Default: instantiate it
in the scheduler plane (storage stays pure storage, simplest swap contract,
the arbiter sees near-live timers). Fallback if the 16-record cone misses the
target frequency: instantiate the same FUB inside the storage plane and carry
the winner record across instead. Same module, same records, one decision
deferred to a measured OOC run. **Recommendation: scheduler-side.**

### 2.4 Backends

- **CAM backend (pumice).** `mc_storage_plane` gains a registered record stage:
  per bank, oldest schedulable entry via the existing `r_older` matrix
  (AND-reduce per entry, then 8:1 payload mux) → `head`, second-oldest →
  `head2`. N = 8: ~6 levels inside the plane, registered at the edge. The CAMs
  keep snarf, aggregation, the BRAM data path and the FRFCFS vectors (for the
  research core). Within-bank order becomes FIFO-by-arrival (LiteDRAM-class);
  cross-bank reordering is preserved.
- **FIFO backend (granite).** New `mc_bank_fifo_store`: 16 x small FIFO
  (depth 2-4) with registered head/2nd prefetch, plus the BRAM write-data path
  and drain engine lifted from `mc_xddr2_entry_store`. WR pushes at fill-done,
  RD at AR; pops at commit/issue. The head of a true FIFO cannot go stale under
  the scheduler, which deletes the stale-skid class of bugs entirely.
- **Research core.** `mc_cmd_arbiter` stays selectable (`SCHED_CORE=FRFCFS`)
  on the CAM backend, unchanged. No further timing work on it.

### 2.5 DFI side

Already consistent: `mc_dfi_2p1_plane` and `mc_dfi_4p0_plane` take the same
packed `cmd/wd/rd` valid-ready buses (the 4p0 `CMD_DW` adds BG, `WD_DW` adds
DBI; the scheduler plane already exports `a_cmd_bg`). A compile-only swap
test of `pumice_core` with the 4p0 plane is a one-session check, not a
redesign. Nothing in this plan touches the DFI boundary.

---

## 3. Phased plan with gates

Every RTL phase ends with: `make clean-all && make run-all-func` in
`research-ip/pumice-ddr2-lpddr2/dv/tests` (bar: 216 passed / 1 skipped / 78
lint, both geometries), the common-ip store-arbiter contract at N = 8 with
> N chunks in flight, and the perf proxy. Shared-tree discipline as before
(`git commit --only <paths>`).

### Phase 0: stop the bleeding, fix the yardstick (1 session)

**Status 2026-10-21: done except the func-regression gate (running at
writing).** Report: `reports/regr/mem-ctrl-recovery-phase0-2026-10-21.md`.
Two things the plan did not anticipate: (a) the first proxy run found and
fixed a real deadlock, pumice BUG-028 (refresh drain PRE guarded by the
demand-PRE pre-pick shadow, exposed by CLOSE_ON_DRAIN=0); (b) the proxy's
own DRAM-checker calibration moved the model's read return (CL from
`dram.timings`) and produced a one-word slip that looked like a read-path
bug for two hours — keep the slave's CL/CWL when swapping the checker.
pumice-CAM baseline (txn 1024): incremental 559/558, row_major 573/570,
col_ilv 330/330, col_major 213/213 MB/s wr/rd, mism 0; col_major inter-row
gap 15 (floor 6 rd / 8 wr), 22.5 cycles per row.

1. Park Stage B formally: ledger line in
   `.superpowers/sdd/2026-10-20-pumice-100mhz/progress.md`, keep the scratch
   file as evidence, no further work on `mc_cmd_arbiter` timing. Stage A
   (bf53f9556) stays; it is harmless and committed.
2. Fix the contract TB: drive `bank_*_ready_i` from TB-controlled signals
   instead of `'1` (`mc_store_arbiter_macro_tb_top.sv:276-278`) so
   `cocotb_test_hold_on_gate_block` can block the gate. The four cells become
   the acceptance tests for the new core; re-point them at the plane-level
   core select rather than `u_arb` internals.
3. **A pumice perf proxy.** `test_granite_char_perf.py` measures granite
   (FRFCFS + entry store); there is no board-timing sim proxy for pumice with
   its CAMs. Clone it onto `ddr2_char_uart_tb_top` (same DFISlavePHY +
   DramStateModel, `set_jedec_timings` at 75 MHz) as `test_ddr2_char_perf.py`.
   Record pumice-CAM baseline numbers for the four families.
4. Add a `TEST_TIMING_OVERRIDES="tRTP=1,..."` knob (patch the programmed
   timings after the board derivation) so parity can be measured like-for-like
   with LiteDRAM's actual rule set, and log the JEDEC floor per family beside
   every number. Also `TEST_NUM_GEN` for the multi-thread case.
5. Housekeeping: `targets/granite/fpga/reports*` in the working tree describe
   the reverted aged design; the untracked `reports_fp1/`, `reports_retry*`
   dcp directories are multi-hundred-MB experiment residue. Note them in the
   closure, do not let them ride into a commit.

Gate: pumice-CAM col_major baseline recorded; the four contract cells run
against the real gate; `make run-all-func` unchanged.

### Phase 1: the contract and the CAM backend's records (1-2 sessions)

**Status 2026-10-21: done.** `mc_head_rec_t` in `mc_common_pkg` (no bank,
id, last or hit flag -- see the type's comment), `mc_bank_head_records`
(new fub, registered per-bank {head, 2nd} from any backend's per-entry
vectors + age matrix), four record outputs on `mc_storage_plane` from the
two CAMs, fub test with a Python slot/age model at one-cycle latency plus a
hold-stability check (gate/func/full, two seeds), handbook note
`design/plane-boundary-registered-snapshots.md`. Additive: pumice
run-all-func unchanged. Decision carried into Phase 2: the record lags the
backend by one cycle by contract; `mc_bank_pick` decodes from the record
and never from the vectors.

1. `mc_head_rec_t` in `mc_common_pkg.sv`; record ports on `mc_storage_plane`;
   per-bank oldest/second-oldest from the CAM `r_older` matrices, registered
   at the plane edge. Existing `*_sch_*` outputs stay for the research core.
2. Contract unit test (common-ip macro): push/pop/aging sequences assert the
   record invariants: a record changes only on push into an empty queue, on
   pop, or on the aging tick; `head2` is the second-oldest; `behind_empty` is
   exact; pop → refreshed record next cycle.
3. Handbook note: `vault/handbook/design/plane-boundary-registered-snapshots.md`
   (the §17 law and the -35 ns failure that taught it), indexed; link from
   `what-is-a-plane`.

Gate: pumice `run-all-func` byte-identical (records are additive).

### Phase 2: `mc_bank_pick` on pumice (2-3 sessions, the hard one)

**Status 2026-10-22: done** (one session). `mc_bank_pick` landed as the
default pumice core (`SCHED_CORE`, FRFCFS kept for research) -- **reversed
the same evening by the owner: granite (product) carries BANK_PICK, pumice
(research) carries FR-FCFS; both selectable, every harness / tb / proxy
default follows** (Phase 3 report §5.1 has both cores on the same harness); `mc_bank_sched`,
`BANK_FIFO`, `BANK_IN_ORDER` and the `*_bh_*` head-view ports retired. Beyond
§2.2 the core needed three things to land dependent hops on the floor through
a two-stage pipe: a one-cycle pop shadow (the record lags a pop), a next-op
hint (ACT->COL, PRE->ACT, last-of-row COL->PRE; direct winner load when the
hop is shorter than the pipe) and a stale-winner mask in the arbiter (the
request register lags a fire). Found on the way: pumice BUG-029 (the plane fed
the REFpb rotor mirror from the command FIFO head), the write CAM's
commit_ready must be checked exactly one cycle before the fire (it is a
function of commit_valid), and the REF all-idle gate belongs on the live
activate-ready bits. Gates: contract bench 5/5 on BANK_PICK (FRFCFS 2 + 3
strict xfails), pumice run-all-func 216/1 at both geometries, granite 6/1xpass
on FRFCFS with the records wired. Perf proxy at the board timings: col_major
195/195 -> 358.7 rd / 310.9 wr MB/s (inter-row gap at the floor, 6/8; the
rest is refresh), col_ilv 307/354 -> 459/457, streaming held at 571-578; at
the LiteDRAM-equivalent profile (tRTP=1) col_major rd 387.6 vs LiteDRAM's
386, wr 311.3 vs 304 -- parity within the owner's 1-2%. Report:
`reports/regr/mem-ctrl-recovery-phase2-2026-10-22.md`. Not done from the
list below: item 4 (tREFI 100/200/400 cells on the pumice proxy; the pumice
suite's refresh cells cover the corners at both geometries) and a BANK_PICK
close-drain probe (`test_pumice_close_drain` still builds FRFCFS).

1. New FUB per §2.2; `mc_scheduler_plane` gains `SCHED_CORE` = BANK_PICK |
   FRFCFS (retire the `BANK_FIFO` and `BANK_IN_ORDER` parameters; the
   constant-folded mask plumbing in `mc_cmd_arbiter` goes with them).
2. Bring-up on the store-arbiter contract bench first (fast, directed), then
   the four cells, then `test_pumice_close_drain` semantics (group drain →
   exactly one AP, zero explicit PREs in steady col_major).
3. `BANK_LA` = 2 in `pumice_core` for this core; verify the hop lands at the
   floor with the gap histogram (`PERF_CMD_TRACE=1`): col_major RD gap 6, WR
   gap 8 at the default profile.
4. Mixed-direction and refresh corners: `test_granite_char_gap.py` style
   cells at tREFI 100/200/400/585 ported to the pumice proxy; cmd-history
   checker armed (`CMD_HISTORY_EN`).

Gate: `run-all-func` 216/1/78 both geometries with `SCHED_CORE=BANK_PICK`
(config-sweep cells that exercise FRFCFS order modes run on the research
core); perf proxy row_major ≥ 570 held, **col_major rd ≥ 360 / wr ≥ 310 at
the default profile** (floor 369 / 320 minus refresh episodes), and ≥
LiteDRAM's 386 / 304 at the LiteDRAM profile; incremental and col_ilv not
below the FRFCFS baseline.

Parity criteria (owner, 2026-10-21): bandwidth within 1-2% of LiteDRAM and
AR-to-first-R latency within ~3 clocks, single-threaded, per family.
Latency comes from the harness histograms; compare only within one run and
one histogram semantics (the 2026-09-13 engine rework changed it). A full
DRAM-command-stream comparison against LiteDRAM is not possible in this sim
(no LiteDRAM model); the equivalent evidence is pumice's per-family gap
histogram (`PERF_CMD_TRACE=1`) measured against the JEDEC floor, plus the
armed cmd-history checker. Multi-threaded expectation: with 8 generators
(the harness `multigen` profile, 4 wr + 4 rd) pumice is expected to beat
LiteDRAM clearly, as the 2.0x concurrent result already does at 1w+1r; the
proxy gains a `TEST_NUM_GEN` knob and reports both.

### Phase 3: timing (1 session, plus a checkpoint inside every RTL phase)

**Status 2026-10-22: done** (one session; report
`reports/regr/mem-ctrl-recovery-phase3-2026-10-22.md`). The Phase 2 text
missed 75 MHz in the board build (`w_sys_i` WNS -3.175, 122 / 77 059
endpoints, 17 in the controller) on one arc that bypassed the pipeline: the
fire cone (record mux, hit compare, live timers) on the winner register's
load enable and, through the stale-winner mask, on the arbiter. Restructured
so that no fire-cone arc reaches the winner register: the record carries
its hit (classified at the storage edge against the scheduler's REGISTERED
row image, one cycle stale, ANDed with live row-active at fire); one-hot pop
shadow; the pick register loads every cycle and a winner waiting on a timer
holds through a register-to-register mux bounded by its lookahead bit, and
its own pair is masked out of the pick while its request is stale (a
no-hold core issued reads out of order under tCCD, +20 cycles on the return
ring, and re-picked the stale request in the fire cycle: a bank-rotating
single-entry write stream at 50%); hops shorter than the pipe are
speculated from registers (ACT->COL, PRE->ACT, last
COL->PRE, COL->COL same row when alone, hit-gated); the write sink is one
register-only predicate (`wr_commit_ready_now`, the CAM's own accept
condition, no drain-pop term -- the pop reaches both consumer readies and
was the worst 100 MHz cone). `pumice_core` out of context, post-route:
aclk 10 ns WNS -0.520 (23 / 16 320: two in the arbiter, 21 in the storage
plane's snarf-match -> read-insert arc), dfi_clk 5 ns -2.067 (464 / 2 776,
the aligner -> CDC cone, independent of the pick core). Board builds on the
final text: 75 MHz `w_sys_i` +0.077, 0 / 77 093 (the gate, closed); 100 MHz
-2.574, 3 463 / 77 128 (Phase 2 text -6.672 / 11 899; the FRFCFS control
-2.555 / 6 296: the harness cannot close 100 MHz with any core). Perf:
col_major 310.0 / 355.6 and row_major 577.7 / 576.9 at parity with Phase 2,
the LiteDRAM profile 311.1 / 383.3, col_ilv 460.0 / 459.1 once the
stale-winner mask was back (without it every row switch under interleaved
traffic paid a bubble: 418 / 436, four generators 420 / 437; found with the
proxy's new `PERF_PICK_TRACE`). OPEN: eight-generator streaming 461 / 458
against Phase 2's 567 / 535 -- demand row switches once per eight columns
(521 ACTs per 4 096 columns vs Phase 2's 108); not the hold, the sink, the
re-pick or the idle-timeout policy (report §6). The miss deliverable (binned xlsx,
rd / wr diagrams with the failing cones in red) is in the gitignored
`projects/components/mem-ctrl-ip/debug/`.

Target is **100 MHz** (owner, 2026-10-21); 75 MHz is the floor that must
never be lost. **Owner, 2026-10-22, after the Phase 3 report: 100 MHz is a
FUTURE goal, not this phase's gate; the requirement now is that each
injector runs eight threads at once, so the eight-generator streaming loss
(report §6) is the first item after this phase.** Done the same day: the
loss was the second cycle of the stale request (the request register
describes a fired entry for two cycles; the mask covered one; the free
slot went to the idle-timeout close of another generator's row); a fourth
registered mask source from the fire fixes it, four generators per
direction measure 567 / 568 streaming against Phase 2's 567 / 535 (report
§5 follow-up). Eight injectors is pumice TASK-043 (harness GO register). Why the history looked flaky: no build ever closed 100 MHz on
the real domain. The recorded "100 MHz pass, WNS +9.26" was the one-endpoint
`sys_clk_pin` input domain (MC-003 §2026-10-17 night correction); the
73k-endpoint `w_sys_i` domain was red in that same build, and the -33/-40 ns
builds were the aged core. Rule from here: **every timing claim names the
clock, the WNS, the failing-endpoint count and the total-endpoint count**,
taken from the `Clock ... WNS(ns)` table, never the headline line.

1. Checkpoint, every RTL phase: OOC synth (the `/tmp/pumice_timing_head`
   recipe, regenerated, aclk 10 ns / dfi_clk 5 ns) on `pumice_core`,
   bucketized by cone; the new core's cones must each sit under ~6 ns of
   logic at synthesis, and no bucket may span the storage/scheduler boundary.
2. End of Phase 2: `build-perf` post-route at 75 MHz (WNS ≥ 0 on `w_sys_i`,
   it is +0.122 today) and at 100 MHz (`PUMICE_SYS_100`-style define, same
   flow). 100 MHz WNS ≥ 0 is the goal; a miss is reported with the bucket
   table, not iterated silently.
3. If the 16-record arbiter is the worst cone at 100 MHz, exercise the §2.3
   fallback (move `mc_bank_pick` into the storage plane) and re-measure; one
   iteration, then report. The dfi_clk cones (aligner → rd CDC FIFO full,
   -2.8 ns at 200 MHz) are independent of the pick core and get the parked
   plan's Task 5 skid if they still fail.

### Phase 4: the FIFO backend and the swap proof (2 sessions)

**Status 2026-10-22 (owner ruling):** granite's `SCHED_CORE` default is
BANK_PICK now, on its existing entry-store backend with the Phase 1 records
-- the swap proof's "scheduler plane RTL identical between the two builds"
holds by construction (same `mc_scheduler_plane`, one parameter). Gates and
the 1/2/4/8-thread perf on that default are in the Phase 3 report §5.1; the
FIFO backend (`mc_bank_fifo_store`) and the storage battery below remain
this phase's work.

**Status 2026-10-23:** `mc_bank_fifo_store` landed and is granite's default
(`STORE_BACKEND=1`). Its first cut capped each (direction, bank) queue at 4,
which blocked the AXI address channel half way through every chopped burst
(23 percent off at eight threads, the mixed family deadlocked); the shipped
form keeps the bank queues pool-deep and stores the same-row-behind flag as
one bit per queue position at push, so no match matrix remains (item 4 of
the Phase 3 report's area list falls out of item 1). Battery: contract test
at N=8 with 2xN chunks on both backends (`test_mc_store_arbiter_contract`,
`entry`/`fifo` cells), `test_granite_top_geared` n8/m12, the granite suite
on both backends and with `FIXED_TIMINGS=1`, the perf proxies, whole-harness
lint. Numbers and the board build: Phase 3 report section 5.11.

1. `mc_bank_fifo_store` per §2.4 presenting the same records; granite_core
   composes it with the untouched scheduler plane.
2. Storage-backend battery (AGENTS.md rule generalised): contract test at max
   depth with > N chunks per direction, `test_granite_top_geared`
   NUM_ENTRIES=8 / MANY=12, `test_granite_char_uart`, perf proxy,
   whole-harness lint.
3. The swap gate itself: the scheduler plane RTL is byte-identical between the
   pumice and granite builds; both backends pass the battery; granite closes
   at 75 MHz with the scheduler untouched.

### Phase 5: board (owner's call, 1 session each)

pumice `build-perf` A/B against LiteDRAM at both timing profiles; granite with
the FIFO backend (14/14 integrity, the three perf gates). No programming
without a timing-clean report in hand.

### Phase 6: close-out (1 session)

Update `common_mas` ch03/ch04 and the pumice MAS scheduler chapter; close
MC-003 against this plan (file the new work as MC-004 in the
memory-controllers lane); drop `mc_bank_sched.sv` and its tests once
`mc_bank_pick` passes Phase 4; delete the `MC_ARB_BANK_OH` compile guard
(Stage A's unused hook) or finish it, one or the other.

Rough total: 9-11 agent sessions. Phase 2 is where the time goes; Phases 0,
1 and 3 are bounded.

---

## 4. What this plan deliberately does not do

- No 100 MHz work on `mc_cmd_arbiter`. It closes at 75 MHz on the board, it
  is the research core, and its pipeline is the perf problem, not the fix.
- No further floorplan / directive campaigns on the per-bank core. Three
  rounds showed the residual is structural (73-80% route on comb boundary
  crossings); placement is not the lever.
- No change to the DFI planes or the AXI plane.
- No LiteDRAM-style per-bank hit-first reordering inside a bank. In-order per
  bank is the owner's stated product semantics; the research core keeps
  within-bank FRFCFS for studies.

---

## 5. Risks and how each is caught

| risk | catch |
|---|---|
| LA = D lands a winner one cycle early and holds, costing other banks a cycle in mixed traffic | gap histogram per family; col_ilv must not drop below the FRFCFS baseline |
| CAM per-bank oldest cone grows with N (N = 16 builds) | it is inside the plane and registered at the edge; OOC bucket per N before adopting N = 16 |
| Refresh / tRFC / return-window holes re-open in the new core | the MC-003 override blocks are lifted verbatim; `test_granite_char_gap` tREFI 100-585 cells ported to the pumice proxy; cmd-history checker armed |
| 1 column/cycle on one bank needs head2 bypass that re-creates a comb boundary path | head2 is a registered record; the bypass is a select between two flops |
| Research-core-only features (order modes, QoS prio_sub, access_pref) assumed by pumice tests | config-sweep cells gate `SCHED_CORE=FRFCFS`; the BANK_PICK suite runs the shared cells |
| Equal-timing comparison hides a real LiteDRAM advantage (AP decided with lookahead) | the proxy reports both profiles and the floor; AP-on-2nd-row is in the new decode |

---

## 6. Owner decisions (2026-10-21)

1. **Park Stage B** of the 100 MHz plan, keep Stage A and the four cells.
   DECIDED: yes. AMENDED 2026-10-21 (Phase 0 finding): Stage A (bf53f9556)
   fails 25/216 pumice func cells with refresh-adjacent read drops and had
   never been run against the suite; it is reverted and the arbiter is
   a8331c9d6 + the BUG-028 fix. The four cells stay.
2. **Contract shape / pick placement** (§2.3). DECIDED: per-bank records
   cross the boundary, `mc_bank_pick` instantiates in the scheduler plane by
   default; storage-side placement is the measured timing fallback only.
   Reason recorded: the two placements have equal cone depth, and only the
   scheduler-side shape fires another bank when the winner's gate closes,
   which is the multi-thread case pumice is meant to win.
3. **Parity definition.** DECIDED: bandwidth within 1-2%, latency within ~3
   clocks, single-threaded, at equal programmed JEDEC cycles with the floor
   stated beside every number; 8-thread run expected to favor pumice
   clearly. Folded into the Phase 2 gate.
4. **Frequency.** DECIDED: 100 MHz is the target, 75 MHz the floor; timing
   claims carry clock, WNS and endpoint counts. Folded into Phase 3.
5. **pumice first, granite trailing.** DECIDED: granite's FIFO backend is
   the swap proof once pumice meets the goals (Phase 4 stays, deprioritized).

## 7. Reference index

- Perf JSONs: `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/logs/perf_dump_*.json`
- Board A/B: `research-ip/pumice-ddr2-lpddr2/docs/char_results/FINDINGS_litedram_ab_2026-10-03.md`
- Timing reports: `build-perf/fpga/reports/timing_summary.txt`,
  `targets/stable/reports/`, `targets/granite/fpga/reports/` (aged design)
- Aged core (for the cone trace): `git show fc9848135:.../mc_bank_sched.sv`,
  `git show 13691eefb:.../mc_age_fifo.sv`, `.../mc_matrix_arbiter.sv`
- Contract rethink: `vault/tracking/projects/components/mem-ctrl-ip/MC-003_read_hang_root_cause.md` §17
- Parked plan: `docs/superpowers/plans/2026-10-20-pumice-100mhz.md`,
  ledger `.superpowers/sdd/2026-10-20-pumice-100mhz/progress.md`
