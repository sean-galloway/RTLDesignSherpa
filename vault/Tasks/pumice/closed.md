<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Closed (done)

---

## PUMICE-014 — retire ALL hand-poking of valid/ready interfaces in pumice DV
**Status:** CLOSED 2026-08-29 — COMPLETE. No hand-driven handshake
remains anywhere in pumice DV. The two remaining are deliberate
exclusions with reasons, not leftovers — see below. HARD RULE from Sean:
"None of the environments should EVER hand poke on any standard interface
or valid ready interface", and "If there are bfms you don't need to set any
signals" — the BFM drives the PAYLOAD too, not just the handshake.
See [[feedback-always-use-axi4-bfms]].

**DONE (0 handshake pokes remaining; residual counts are non-handshakes):**
top: `test_pumice_core_dfi` (50→0), `test_pumice_core` (33→0),
`test_pumice_top_csr` (22→0), `test_pumice_top` / `_geared` (2 ea→0).
fub/macro: `pumice_axi4_ifc_tb` (35→0), `pumice_wr_intake_tb` (34→0),
`pumice_rd_intake_tb` (32→0), `pumice_wr_data_cam_tb` (17→6),
`pumice_rd_cmd_cam_tb` (13→3), `pumice_dfi_cdc_tb` (12→0),
`test_pumice_dfi_cmd_path` (8→2), `pumice_cmd_arbiter_tb` (7→0),
`test_pumice_dfi_wr_serializer` (6→0), `pumice_mem_cmd_scheduler_tb` (3→0).

**Collateral to reuse, do not re-roll:**
* `dv/tbclasses/pumice_axi_bfm.py` — `PumiceAxiBfm`, the one place any
  pumice `s_axi_*` is driven. `write=`/`read=` for single-direction ports.
* `dv/tbclasses/pumice_fub_bfm.py` — `fub_consumer()` / `fub_producer()`
  over the GAXI BFMs for fub-internal valid/ready ports, with an explicit
  `signal_map` (pumice's `aw_push_bank_o` style names do not match GAXI
  auto-discovery, and explicit fails loudly on a rename).

**The two deferred files were FINISHED 2026-08-29**, not waived. Both had
the same root problem -- the MEASUREMENT, not the driver -- and the same fix:
rebase onto the OBSERVED handshake cycle instead of a fixed offset from when
the testbench presented. That is BFM-compatible and more honest (it measures
the DUT's latency, not latency-from-the-testbench).
  * `test_pumice_dfi_rd_aligner.py` — `_CycleObs` records op fires and
    rddata_en cycles; t_rddata_en checked as (en - fire), and the tCCD case
    asserts OUTPUT gaps track INPUT gaps rather than hardcoding 2. Pacing
    comes from the `fixed` valid_delay profile.
  * `dfi_cmd_formatter_tb.py` — `_watch_fire` counts accepts; the check
    samples once the accept is observed, with NO extra cycle (the outputs are
    registered from the accepted command, so an extra wait sampled after
    valid dropped -- that was why the first attempt failed).
  Both mutation-checked: firing a read a cycle early (the ILA-confirmed
  silicon bug) fails the aligner tests; corrupting the bank encoding fails
  9 of 10 formatter tests.

**Not handshakes — verified against the RTL port lists, leave hand-driven:**
CREDITS with no matching valid — `rd_op_ready_i` ("rd aligner has a free
slot"), `bank_act_ready_i` / `bank_rdwr_ready_i` / `bank_pre_ready_i`
(per-bank permission vectors). STROBES with no ready — `wr_done_valid_i`,
`dfi_rddata_valid_i` (DFI read data is unconditional per spec),
`init_cmd_valid_i`, `sched_lu_valid_i`, `snarf_probe_valid_i`,
`wr_fire_i`. Read-only MONITORS also stay (`_mon_b`, `_mon_r`): the AXI
master owns bready/rready but the sequence result carries no per-beat
rid/rlast/rresp/bresp. Observing is not poking.

**Two traps that cost real time — read before the next port:**
1. **Queue-and-go vs blocking send.** `send()` blocks until its packet is
   accepted, so awaiting per beat leaves a GAP between beats. A hand-rolled
   "present the head every cycle" source is always-valid; to match it use
   `_driver_send` (queues and returns). The wr-serializer tCCD test
   measures gaps between `wrdata_en` pulses and read 3 where 2 was
   required until this was fixed.
2. **`ready_policy` is not the `backtoback` profile.** GAXISlave's default
   `valid_first` waits for valid on a CLOCKED loop, so ready lands a cycle
   LATE even at ready_delay 0. Use `ready_policy='always'` to model a TB
   that used to tie ready to constant 1, and `'stall'` +
   `set_ready_policy()` for deterministic consumer backpressure.
   (RDS-DV c220c19 / aacb90d / 5fcf039.)

**Whenever GAXI changes, run all of val/amba** (Sean). Baseline for A/B:
739-741 passed / 2-4 failed at `-n 24` with SEED pinned, and the failing
set is NOT stable run to run — see [[AMBA-MONRATE-INTERMITTENT]]. Do not
read a single differing failure as a regression.

**Also outside pumice (same rule, flagged not owned):**
`projects/components/misc/dv/tbclasses/axi4_slave_wr_crc_check_tb.py`.

**Rule going forward:** no NEW test may hand-poke a valid/ready interface.

## PUMICE-015 — greppable structure trackers (CAMs / page policy / refresh / scheduler)
**Status:** DONE 2026-08-27 — the infrastructure already existed
(`dv/tbclasses/trackers/`, predating the request); this closed the gap
between it and the rearchitected RTL, added the missing structures, and
proved it live. Method note: [[structure-trackers]].

**What was wrong** (nothing had run the trackers since the rearchitecture,
so the rot was invisible):
- `page_predictor_tracker` targeted a DELETED fub (retired with
  HAPPY_HYBRID) — removed.
- `xbank_timers` / `rd_cl_aligner` / `wr_beat_sequencer` targeted RENAMED
  fubs (`pumice_bank_timers`, `pumice_dfi_rd_aligner`,
  `pumice_dfi_wr_serializer`) and read signals that no longer exist —
  retargeted (`btmr` short name; emit-stall + wd handshake taps).
- `scheduler_tracker` targeted the pre-rearchitecture FSM scheduler —
  retargeted to `pumice_cmd_arbiter` and given the Axis-1 POLICY view
  (ORDER/PREF/ROWSEL/COLSEL/PRIO/QOS/WRDRAIN emit-on-change), so a pick
  can be explained and not just observed.
- EVERY tracker hard-coded `mc_clk` while the rearchitected fubs use
  `aclk` — the first one to run killed the test with an AttributeError.
  Fixed centrally: `tracker_clock()` resolves by name, and `guard_run()`
  wraps every run() so a signal miss disables THAT tracker instead of
  failing the sim (instrumentation must never turn a green run red).
- `wire_trackers`'s hierarchy map still pointed at pre-rearchitecture
  instance paths — updated to `u_sched.u_arbiter` / `u_ifc.u_rd_cam` / etc.

**What was added:**
- `page_policy_tracker` (`pgpol`) — the Axis-2 decisions: mode changes,
  per-bank ap-mask edges, timeout-PRE requests, page hit/miss/empty, plus
  the rbl (modes 6/7) and row-pred (mode 5) verdicts read through the
  child instances.
- `cam_tracker` (`camrd` / `camwr`) — entry lifecycle
  INSERT/ISSUE|COMMIT/DRAIN|DONE, CAM-full INS_STALL, and OCC_<n>
  occupancy (the population the write watermarks and most/fewest_pending
  selects key off).
- `refresh_tracker` extended for the v3 work: pull-in CREDIT_<n>, burst
  DRAIN_ON/OFF, REFab-vs-REFpb KIND, and `rotor_advances()` — the exact
  check that catches a desynchronized REFpb rotor mirror.

**Usage:** `PUMICE_TRACKERS=1 pytest <test>` wires them in the core TB;
each writes `<sim_build>/<short>.out`. Off by default.

**Proof (clean run of test_pumice_core_rbl):** all ten trackers wrote live
logs; `pgpol` reproduced the test's arms exactly
(MODE_0 -> MODE_6 -> RBL_LOWLOC(b3) -> MODE_7 -> MODE_0), both CAMs
conserved (45 INSERT = 45 ISSUE/COMMIT = 45 retire), and sched EVT_ACT
(59) matched btmr ROW_ACTIVE_SET (59).

**Remaining (optional, not blocking):** no tracker yet for
`pumice_axi_burst_chopper` / `pumice_wr_splitter` (front-end burst
framing) or the DFI CDC; add them if a front-end bug ever needs the same
cross-structure view.

## PUMICE-001 — Runtime-config axes corrupt data (board + sim)
**Status:** closed 2026-08-25 — board re-validated on the fresh bitstream; matrix 65/70 with the 5 residuals split to PUMICE-020 (observability only). Issue #42.

**Fixes landed 2026-07-23 (commit fab57682):**
- `pumice_cmd_arbiter`: auto-precharge column guard. Under CLOSE the xDA
  precharges the bank as part of the access, but the generic guard deliberately
  does not gate columns against columns and `r_bank_row_active` is a cycle
  stale, so the next entry on the same bank+row still saw "row active" and
  issued a second column into a bank already committed to precharge. On the
  DRAM that column has no open row and the access lands wherever the device
  last had one (batch-2 row-1 writes landed on row 0, clobbering batch 1 —
  64 beats / 48 unique). Guards the bank for 2 cycles after a fired AP column,
  exactly as `r_guard0/1` do for ACT/PRE. No-op under OPEN/HYBRID.
- `pumice_top`: `REFRESH_TUNING.page_policy_or` carries the SOFTWARE encoding
  (0=build default, 1=OPEN, 2=CLOSE, 3=HYBRID) while `page_policy_e` is
  OPEN=0/CLOSE=1/HYBRID=2. The raw cast made software-OPEN run CLOSE and
  software-CLOSE run HYBRID — the entire open_page/reorder config-axis
  corruption keyed off this.

Verified: `pumice_cmd_arbiter` FUB passes on a clean build; macro+top 54 passed
(the 1 failure is PUMICE-002, pre-existing).

**Still open:** board re-run of the config-axis families on a rebuilt bitstream.

**Board baseline (2026-07-22, first rearch config-axis run):** baseline/inorder
9/14 (col_major fails only at scale 1000); bank_interleave / open_page /
reorder 0/14. multiid showed 7 EXTRA read returns (hist 64007 != 64000) —
suspect rd-CAM duplicate issue under reorder. Correctness at the baseline
config is SOLID (soak gate green); these are the runtime
page-policy/scheme/reorder paths.

Full map + signatures:
`projects/fpga-systems/NexysA7/pumice/ddr2-characterization/char_results/FINDINGS_pumice_board_2026-07-22.md`
(+ `char_2026-07-22_wrapup.csv`). Tools: CMD_HISTORY_EN checker,
dfi_rd_return_checker, ILA flow.

**Sim repro available:** `test_ddr2_char_char_families` fails the
bank_interleave family over the DFI loopback — the config-axis defect is
digital and wave-debuggable in sim; start there, no board required.
See PUMICE-003, same class.

**Board re-validation (2026-08-25, bitstream 3159cd6b, unit 210292BFA3EE,
releveled bitslip0/tap7/eye0..14):**
- init + write_read integrity clean; smoke@1000 initially 4/6 — bank_interleave
  32000/32000 beats mismatched, which root-caused to the HOST, not RTL: the
  burst_cols formula counted pumice-beat units where ADDR_MAP.bank_lsb is
  DEVICE-WORD granular, so x16 got bank_lsb=1 (needs 2) and every burst striped
  across banks. Invisible at device==beat, which is why the sim families test
  passed — new `test_ddr2_char_char_families_x16` reproduces it (RED 60 beats)
  and pins the class; one-line fix (BOARD_BURST_COLS = BL) → sim GREEN, board
  smoke 6/6, bank_interleave BW 33→65 MB/s (7.5–7.8x baseline).
- matrix@1000 then 45/70: every col_major-family point failing on ALL configs —
  proven a CHECKER ARTIFACT by exact arithmetic: the 64000-txn x 16 KiB walk is
  1 GiB over a 128 MiB device; mismatched beats = 55808*BL mod 2^16 =
  26624/53248/40960 at bl4/8/16, matching observation exactly. (This was also
  July's "col_major fails only at scale 1000".) Fix: wrap the GENERATED address
  at the device boundary (Geometry.device_bytes; wrap_mask for
  col_major/col_interleave) so the address-hash stays cell-consistent —
  DRAM-visible behaviour unchanged. Sim regression both families tests green.
- matrix@1000 re-run: **65/70 — every family x config DATA-CLEAN.** The 5 flags
  are the multiid 1:1 hist anomaly only (data clean) → split to PUMICE-020.
- tREFI soak gate: **0/15 dirty** (default / tiny 0x40 / huge 0xFFFF) — the
  PUMICE-004 refresh fix re-validated on the current bitstream.
- Config-axis perf, all as designed: open_page/reorder 13–13.8x baseline on
  inc/row_major; bank_interleave 7.8x on col_major; bank-recovery visible on
  col_major_interleaved. July's 0/14 axes are fully recovered.

Final accounting for issue #42 + the July cluster: every failure across
PUMICE-001/002/003/004/007 was verification- or host-side. Zero RTL defects.
CSVs: build-perf/results/char_2026-08-25_{smoke,matrix}_s1000*.csv.


## PUMICE-007 — Retire the deskew RTL + PHY_TIMING.deskew_lo/hi CSR
**Status:** closed 2026-08-24 — already done by 38c8ae63 (Jul 22), the day before this page was stamped open

The deskew path was superseded (see PUMICE-008 in `dropped.md`): the board read
fix was the PUMICE-005 bring-up tuple at deskew 0/0. The RTL and its CSR fields
remain and cost area/timing. Delete rather than train — but only after the
board is re-validated on a rebuilt bitstream so the removal is not entangled
with an active bring-up.

**Resolution (2026-08-24):** the fourth stale entry from the Jul 23 vault
migration (with 002/003/004). `38c8ae63` had already retired the whole
experiment — aligner delay-lines, DESKEW_W threading, PHY_TIMING.deskew_lo/hi
(RDL regenerated), train_deskew/validate_reads, Makefile/ILA hooks — and the
same commit closed board bring-up with reads working on the rebuilt bitstream,
which was this task's stated precondition. Verified against the tree: zero
deskew references in rtl/, the regmap, or the board area; the only survivor is
the historical removal note in pumice_csr.rdl.


## PUMICE-004 — Refresh collides with an open row (arbiter registered-feedback hazard)
**Status:** closed 2026-08-24 — fix landed 38c8ae63 (Jul 22, silicon-soaked); detector armed + mutation-proven

**Bug (#2, command-sequencing).** The arbiter (`pumice_cmd_arbiter`) can grant a
`REFab` immediately after an `ACT` to the same bank WITHOUT a `PRE` in between —
refreshing a row that is still open — and the following `RD` then returns
garbage (zero) for that one read.

Root: the per-bank "safe signals" (`pumice_bank_timers` readiness) are COARSE
and REGISTERED (2-cycle event->ready latency, see the `r_guard` note in the
arbiter), so the combinational picker issues the `ACT`, and the refresh path's
precharge-before-REF check does not yet see the just-opened row -> REF fires
with the row open.

**Reproduced pre-silicon** in `engine_mirror[64]` (`test_pumice_top`),
gear-2/BL8, sustained b2b: burst 25 shows `ACT@31920000 -> REF@31940000 (no PRE)
-> RD@31980000` -> read returns `0x0` (golden `0x190000`); refresh cadence
~10.25 us lands on one read. On the BOARD (gear-4, ILA
`reports/ila_refresh_collide.csv`) the refresh is correctly sequenced
(`RD->PRE->REF->ACT->RD`) — so this is not the board blocker, but it IS a real
arbiter defect. Confirmed on silicon as the residual row-sized corruption in
PUMICE-005.

**Instrument (already wired):** `rtl/fub/pumice_cmd_history_checker.sv`
(generate-gated by `CMD_HISTORY_EN` inside `rtl/macro/pumice_mem_cmd_scheduler.sv`)
— a per-(rank,bank) command-history shift register (slot = cycles-since-issue)
that binds to the arbiter's `cmd_valid/op/rank/bank` and audits JEDEC same-bank
sequencing the coarse gate misses. Ships the refresh-collision assertion (no
`REFab` with any bank row open) plus optional tRCD/tRP/tRAS positional checks.
Coarse = *permission to issue* (forward, lossy); fine = *record of what issued*
(backward, exact) — you need the fine one to audit the coarse one.

**Plan:**
1. `bind` the checker in the arbiter FUB (`test_pumice_cmd_arbiter`) and/or the
   scheduler MACRO (`test_pumice_core_macro`) TBs; add `--assert` to the
   verilator compile args.
2. Reproduce as a directed pre-silicon test — small `tREFI` + sustained
   same-bank reads -> the checker fires RED. **The test MUST also do DATA
   checking** (golden read compare), not just the sequencing assertion.
3. Fix the arbiter refresh sequencing: the precharge-before-REF logic must
   account for a just-issued `ACT` (don't grant `REF`/`REFab` while any bank's
   most-recent row-affecting op is an `ACT`), or block the `ACT` when a refresh
   is being sequenced. Mirror the fix in `refresh_ctrl`/`pumice_cmd_arbiter`.
4. Re-verify: checker GREEN, `engine_mirror[64]` burst-25 read == golden, macro
   109 + gear2 + FUB stay green.
5. Rebuild the bitstream (also picks up the APB CDC fix) and re-soak at tiny
   tREFI as the regression gate.

Scope note: this checker catches command-SEQUENCING bugs only.

**Resolution (2026-08-24):** the same staleness as PUMICE-003 — the fix landed
the day BEFORE this page was stamped open during the vault migration.
`38c8ae63` (2026-07-22) added exactly what the plan's step 3 asks for:
`w_ref_safe` (REF only with all rows closed in the registered view AND nothing
row-affecting in flight or inside the 2-cycle guard AND tRFC met) plus a
mission-mode tRFC down-counter with `t_rfc` threaded top→core→scheduler→
arbiter. Silicon-validated then by the tiny-tREFI A/B soak: 4/4 dirty before,
0-dirty after, on the rebuilt bitstream.

**What was still missing — the plan's steps 1-2 — landed today:**
- `CMD_HISTORY_EN` plumbed through `pumice_core` / `pumice_top` / both tb tops
  (it stopped at the scheduler, so no top-level test could arm the checker).
- `test_pumice_core_refresh_collide` now compiles with `-GCMD_HISTORY_EN=1`.
  Before, its "expected RED" docstring was DOUBLY vacuous: the checker generate
  was off, and the loopback DFI slave serves golden data regardless, so the
  data compare could never see a collision either.
- Anti-vacuity teeth: the test asserts the DFI slave decoded >0 REF commands
  (72 in the directed run) — a scenario that never refreshes can't go green.
- Mutation-checked per the formal discipline: gutting `w_ref_safe` to 1'b1
  fires the checker with the exact bug signature ("REFab issued with rank0
  bank3 ROW OPEN (ACT 2 cyc ago, no PRE)"); restoring it audits 72 REFabs
  clean and the full core_dfi file passes 5/5.

Diagnosis footnote: "zero DBG lines" from the checker was a pytest artifact —
cocotb sim output rides Python logging, shown only on failure unless
`--log-cli-level=INFO` is passed. The checker had been watching all along.

**Residual (rides PUMICE-001's board trip):** re-soak tiny-tREFI on the
2026-08-16 bitstream as the standing regression gate — the July soak was on the
July rebuild. This is confirmation, not an open defect.


## PUMICE-003 — test_ddr2_char_char_families integrity fail (bank_interleave/incremental_bl8)
**Status:** closed 2026-08-24 — already fixed by fcafc435; the re-check just never ran

`bank_interleave/incremental_bl8` fails integrity in the char-families sim
("read engine did not complete", 42 beats mismatched).

**Bisected 2026-07-22:** fails identically at HEAD (95c9490a) — predates the
deskew removal, the refresh/tRFC arbiter change, and the no-rmw shadow writes.
Same masked-regression window as PUMICE-002 (the top/char sims were
compile-broken by the dv/tb filelist drift for a period).

Suspect the config-switch path (ADDR_MAP `bank_lsb=0` preset) interacting with
the read engine. Re-check whether the PUMICE-001 fixes move this before
debugging further.

**Resolution (2026-08-24):** the task's own advice ("re-check whether the
PUMICE-001 fixes move this before debugging further") was correct. The July
bisection pinned the failure at HEAD `95c9490a` (Jul 21) — one day BEFORE
`fcafc435` (Jul 22) fixed exactly this: the bank_interleave preset programmed
`bank_lsb=0`, striping one DRAM burst across banks (writes stripe, the read
command fetches one bank's columns → the deterministic 42-beat corruption).
The re-check never happened because the DV framework then broke (RDS-DV
#69/#70) and the char sims were red for unrelated reasons until 0.6.5.

Verified on cocotb-framework 0.6.5, clean build: the exact repro
(`test_ddr2_char_char_families`, smoke profile = baseline/bank_interleave/
reorder × incremental/col_major) passes in 504s. `set_addr_map_scheme` now
derives the legal boundary `bank_lsb = log2(burst_cols)` with `burst_cols`
computed from the TEST_DRAM_* geometry env the sim wrapper exports (sim
64b-device: burst_cols=4 → lsb=2; board x16: burst_cols=2 → lsb=1).

Same #42 family as PUMICE-001's board findings — this was the sim face of the
scheme-axis corruption. The board re-run of the config-axis families
(PUMICE-001) remains the silicon-side confirmation.


## PUMICE-002 — test_pumice_top_csr wr_rd roundtrip returns zero read beats
**Status:** closed 2026-08-24 — TEST defect, not RTL: stale hand-packed DFI_PHASE

`cocotb_test_pumice_top_csr` fails its AXI write-then-read phase: read 0 gets
ZERO R beats in 800 cycles (`got=[]`), i.e. the read path never returns — while
`test_pumice_top` (45 read-heavy tests), core, core_dfi, geared and the whole
fub/macro suite pass.

**Bisected 2026-07-21:** fails identically at HEAD (95c9490a) with only the
filelist fix applied — predates the deskew removal and the refresh/tRFC arbiter
change.

**Re-confirmed 2026-07-23:** fails identically with `pumice_top.sv` reverted to
HEAD and a clean rebuild, so it is not caused by the PUMICE-001 page_policy fix
either. Note the rebuild mattered — the first run reused a stale `sim_build`
and completed in 0.41 s, which would have made a reverted-RTL run meaningless.

Suspect the CSR-programmed config path (hwif-driven init) diverging from the
TB-driven config the other tops use. The top tests were compile-broken (missing
`gaxi_fifo_async` deps in the dv/tb filelists) for some window, so the
regression that introduced this was masked.

**Root cause (2026-08-24):** the test programs CSRs by HARDCODED offset +
hand-packed bit positions (predates [[registers-by-name]]). `DFI_PHASE` grew
`gear_ratio[8:7]` and `bl[12:9]` when gear/BL became runtime CSRs — during the
exact filelist-drift window this test could not compile — and the test's
`pk((0,0),(0,4))` kept writing the whole register as 0. gear=0/bl=0 programs a
zero-beat burst: init completes, AXI writes still get B responses, but the read
path has nothing to return → rvalid never fires → `got=[]`. Every register
OFFSET still matched the current regmap; only the field packing had rotted.

**Fix:** write `gear_ratio=log2(DFI_RATE)`, `bl=BL` in the DFI_PHASE pack
(one line). Red→green flip confirmed on clean builds. The suspicion in the
original filing ("CSR-programmed config path diverging from TB-driven") was
half right — the divergence was in the TEST's packing, not the RTL's hwif.
Textbook case for [[registers-by-name]]: the by-name TB absorbed the RDL
change, the hardcoded one silently rotted. Follow-up candidate: migrate this
test's CSR writes to the generated regmap so it cannot rot again (its distinct
value — raw-cpuif programming + hand-rolled AXI as a BFM-independent second
opinion — is worth keeping).


## PUMICE-005 — Board reads WORK: validated tuple + honest measurement
**Status:** closed 2026-07-21 — reads clean on silicon; residual corruption split out to PUMICE-004

The rate-2/BL4 board (BUILD_ID 0x44445232) reads CLEAN. The blocker was never
the analog read path; it was three stacked measurement/config defects:

1. **Sweep axis.** s7ddrphy asserts `rddata_valid` a FIXED `read_latency`
   (= cl_sys+6 = 8) sys cycles after `rddata_en` (pure delay line; ISERDES
   capture is continuous), so for reads `t_rddata_en` only places valid. The
   DATA arrives at its own physical latency — `DFI_TUNING.rddata_delay` slides
   the data onto the valid window. Every failed sweep held rddata_delay=0 where
   alignment is unreachable. **Validated tuple: t_phy_wrlat=1, t_rddata_en=6,
   rddata_delay=7, bitslip=0, IDELAY tap 8 (eye taps 0..16, width 17).** Baked
   into the A7Leveling ctor defaults.
2. **False-pass metric.** `wait_engine` default bails when rd_error latches (a
   mismatch latches it) -> `beats_mismatched` read EARLY; and a HUNG read counts
   nothing -> reads back 0 = fake clean. Fixed in bringup_joint_probe /
   `A7Leveling._test` / train_per_lane (ignore_error=True + require done; hang
   reported distinctly).
3. **RMW poison.** On pre-CDC-fix bitstreams the pumice APB window returns a
   PRIOR transaction's data, so every `rmw=True` write spliced stale garbage
   into preserved fields (set_deskew after set_controller_cfg silently reverted
   wrlat/rden -> leveling swept at reset timing). pumice_device now NEVER rmws:
   shadowed full-word writes seeded from RDL resets, `invalidate_shadow()` on
   soft_reset. (RTL CDC fix already landed in `apb4_slave_cdc`; bitstreams in
   `bitstream/` predate it — rebuild to retire the hazard on-silicon.)

Residual intermittent row-sized (256-beat/2KB) read corruption, strongly
refresh-correlated (soak A/B: tREFI default 0/8 dirty, tREFI=0x40 4/4 dirty at
~32-44/1024 beats, tREFI=0xFFFF 0/8) is a separate defect — split out to
PUMICE-004, now confirmed on silicon.

## PUMICE-009 — Generic AXI data-width gearing
**Status:** closed — resolved via external converter

Make host `AXI_DATA_WIDTH` a free parameter (32/64/128/256/512) decoupled from
the core width `DW = DRAM_BEAT_WIDTH x DFI_RATE`. Family-wide
(DDR2/3/4/LPDDR2), for future DDR* IP where each device/PHY pins its own
(beat, rate) but the host SoC wants a fixed convenient AXI width.

Implemented via the EXTERNAL formally-verified `axi4_dwidth_converter_wr/_rd`
in a wrapper `rtl/top/pumice_top_geared.sv` (host width <-> DW; GEAR-1 =
generate bypass, bit-identical). Core datapath untouched. Verified end-to-end
(`test_pumice_top_geared.py`): write bursts at host in {64, 128, 256}
round-trip back through host-width reads (down-gear / bypass / up-gear).

Chose external over the internal gearbox because the datapath was freshly
stabilized and the converters are already formal; also the rearchitecture
already solved the original a7ddrphy forcing function (AXI = beat x rate = 128,
a fine width — no gearing needed for the board).

Design + rationale + deferred internal-gearbox option:
`docs/AXI_DRAM_GEARING_SCOPE.md`

## PUMICE-010 — Single-register AXI-address -> {bank,row,col} mapping
**Status:** closed — resolved

`addr_mapper.sv` is now driven by ONE knob — `ADDR_MAP.bank_lsb` (the CSR
register that replaced the old scheme selector) — plus an optional bank
XOR-hash (`ADDR_MAP.hash_en`/`hash_seed`). The mapping is derived by stacking
fields around the bank position: `col_lo(bank_lsb) | bank | col_hi | row | rank`,
row LSB invariant at `CW+BW`. The classic schemes are just settings, no scheme
mux: `bank_lsb == COL_WIDTH` = ROW_MAJOR; `bank_lsb == log2(cols/burst)` = max
BANK_INTERLEAVE (burst locality preserved by col_lo); `hash_en` = XOR_HASH on
top.

Landed: RDL ADDR_MAP register (regenerated CSR + regmap via
`bin/peakrdl_generate.py`); addr_mapper rewritten (single stacked extraction +
hash, 3 generate blocks + mux gone); bank_lsb/hash_en/hash_seed threaded through
pumice_axi4_ifc / wr+rd intakes / pumice_core / pumice_top (driven from
`hwif_out.ADDR_MAP`); program_defaults + test_pumice_top_csr + core tests
updated. FUB conformance (`test_addr_mapper`) rewritten to sweep bank_lsb across
[0, COL_WIDTH] + hash on/off vs a Python reference — 5/5. Full suite: 407 pass,
0 fail (macro 141 + fub/top 266).

`addr_map_scheme_e` retained only for the retired OLD macro sentinels
(pumice_core_macro / axi_frontend_macro / pumice_config_block), which were
carried to the new intake interface — candidates for future retirement.

## PUMICE-011 — Full LPDDR2 mode-register init
**Status:** closed — resolved

Implemented the JEDEC JESD209-2F LPDDR2 init sequence in `init_sequencer.sv`
(memtype-gated): MRW Reset(MR63) -> ZQ Init(MR10=0xFF) -> MR1(BL8/nWR3=0x23) ->
MR2(RL3/WL1=0x01) -> MR3(DS 40ohm=0x02). The wide MR index (MA up to MR63)
reaches the CA formatter via the ROW request field packed as {MA[5:0], OP[7:0]}
(`dfi_cmd_formatter` unpacks row[13:8]=MA, row[7:0]=OP) — no 3-bit bank-port
limit. Only MR1/2/3 update the CL/CWL/BL shadow; MR63/MR10 are issued but not
shadowed. `mode_register.sv` LPDDR2 CL/CWL decode made JEDEC-faithful (MR2[3:0]
RL&WL enum).

Verified: DFISlavePHY now records decoded MRW ({index:data}); `smoke_lpddr2`
asserts init programmed {63:0x00, 10:0xFF, 1:0x23, 2:0x01, 3:0x02}. Formatter
conformance + init_sequencer FUB updated.

**NOTE (silicon):** the sim gates PHY-init-complete on config-ready (TB) so the
sequencer latches the correct memtype ("config before init"). Real LPDDR2
silicon needs memtype stable before init — a strap, or gating the sequencer's
start on `CTRL.init_start`. DDR2 (the board target) is unaffected: its reset
default IS DDR2.

## PUMICE-012 — LPDDR2 write-auto-precharge dropped writes
**Status:** closed — resolved (RDS-DV DFISlavePHY fix)

`workload_mix_lpddr2` had dropped writes under LPDDR2's HAPPY_HYBRID row-miss
policy, which issues WRA (write-auto-precharge). Root cause was NOT the CA
encoding or write cadence: the DFI slave `_handle_command` had branches for
WR/RD but none for WRA/RDA. DDR2's decoder never returns WRA/RDA (it returns
WR/RD and carries auto-precharge in addr bit 10), but the bit-exact LPDDR2 CA
decoder folds AP into the opcode -> returns WRA/RDA -> fell through -> no
pending write -> `wrdata_en` became "stray data beats" and the write was
silently dropped.

Fix: fold WRA->WR and RDA->RD in `_handle_command` (auto-precharge already
carried in addr bit 10 for both paths). All LPDDR2 traffic tests now pass;
xfail removed.

## PUMICE-019 — top-tier shared sim_build races under clean parallel runs
**Status:** closed 2026-08-26 — fixed via per-worker build dirs (was: open 2026-08-23, mechanism confirmed twice, serial run the workaround)

`dv/tests/top/test_pumice_top.py::_run` shares one compiled sim per parameter
set (`local_sim_build/shared_nr1` / `shared_nr2`) so the suite compiles ~twice
instead of once per test — but there is NO LOCK around the compile. After
`make clean-all`, `run-gate-parallel` (-n 48) sends dozens of concurrent
Verilator/ccache compiles into the same directory and they destroy each
other's artifacts (`Vtop__pch.h.fast: No such file`, invalid-PCH, missing .o).
Measured 2026-08-23: two consecutive clean parallel runs reported 48 and 31
spurious FAILs (126-144 reruns) on a suite that passes 53/55 serially — the
reruns converge only once one compile survives, so the tally is garbage and
the flake burns ~5 min anyway.

`smoke`/warm-tree parallel runs are fine (nothing to compile). fub/macro use
per-test build dirs and don't race.

**Fix options:** a file lock around the cocotb_test `run()` compile (fcntl on
`<sim_build>/.compile_lock`), or a cheap pre-compile step in the Makefile's
parallel targets (run one test per shared build serially first, then fan out).
Whichever lands, the parallel targets must give an honest tally after
`clean-all` — that is the canonical regression recipe.

Found while validating the RDS-DV#69 fix; the 2 real reds behind the noise are
PUMICE-002 and the LPDDR2 decode regression RDS-DV#70.

**Second finding (2026-08-24): failing seeds are unrecoverable.** One serial
clean tier run showed geared[64/128/256] failing together; the per-test SEED is
`random.randint(0,100000)` at wrapper level, printed nowhere in the summary, and
the logs/ + results xml were wiped by the next `make clean-all` — so the repro
was lost. File-scope reruns and a 10-seed `PUMICE_SEED` sweep (30 runs) all
pass. Whatever fix lands for the lock should ALSO make the wrapper echo each
test's SEED into the pytest summary line (or persist logs/ across clean-all
until explicitly cleared) so a one-off failure is reproducible after the fact.

**CLOSED 2026-08-26.** Root cause: cocotb_test's Verilator path re-runs
`verilator -cc` + make UNCONDITIONALLY on every run() (no staleness check),
so ANY cross-process sharing of a sim_build is unsafe — a compile-only
flock cannot help because the unlocked sim-run pass regenerates the tree
too. Fix: per-XDIST-WORKER build dirs (`shared_nrN_gwK`) — workers run
their tests sequentially, so the compile-sharing win survives inside a
worker with zero cross-process sharing; ccache absorbs duplicate C++.
Validated: clean `run-gate-parallel` = 61/61 passed in 88s (was 42
spurious FAILs / 126 reruns). Seed echo also landed: every wrapper prints
`[seed] <tag> ...SEED=<n>` so pytest surfaces it for failing tests and a
one-off red is reproducible after logs are cleaned.

## PUMICE-024 — ORDER_MODE overlays miss 75 MHz: CLOSED by shortening the pre-pick stage
**Status:** closed 2026-09-09 — the ENHANCED tier now closes post-route

The overlays missed 75 MHz by 21-53 ps depending on the placer. Root cause was
not the overlays themselves but where the arbiter did its slot-to-data muxing:
the output stage indexed the CAMs' flat {bank,row,col} vectors with the
REGISTERED pre-pick slot, so six NUM_ENTRIES:1 muxes sat AFTER the pre-pick
flop and fed r_bank/r_row/r_col. That was the reported critical path in every
build (`r_*_pop -> ... -> r_bank`).

Fix: mux at the pre-pick flop instead, registering the already-narrow
{bank,row,col} per class. The wide muxes move into the STAGE-1b cycle where
arg_sel has already resolved and there is slack, and the output stage keeps
only the small class-priority mux. `rd_col_ap` already used exactly this
pattern, so it is the established idiom rather than a new one. Sampling one
cycle earlier is also more coherent: a CAM entry's key is fixed at insert and
the forward guards prevent re-selecting a just-selected slot, so the operands
now come from the same epoch as the decision.

Post-route at 75 MHz, same flow, before -> after:

| Build | Before | After |
|---|---|---|
| base | +0.010 ns, 0 failing | +0.009 ns, 0 failing |
| ENHANCED | -0.021 ns, 4 failing | **+0.005 ns, 0 failing of 72896** |

The base tier was already closing so it does not move (both figures are inside
the placement band); the enhanced tier closes for the first time. Cost is about
144 flops and 0.19% LUT. The same change also shortens the prepick-guard cone,
which feeds the mask build.

Validation: pumice fub 96 / macro 3 / top 119, zero failures; char sim 31
passed + 2 xfailed, zero unexpected.

## PUMICE-017 — CAM->arbiter pick cone does not close timing: CLOSED (stale)
**Status:** closed 2026-09-09 — the measured condition no longer exists

Filed 2026-08-31 against a post-route WNS of **-48.861 ns** with 8939 failing
endpoints, on the grounds that logic delay alone (17.825 ns) exceeded the 15 ns
period so no placement effort could recover it: "it is depth, and it needs
registers."

It got them. The three-stage pick split (STAGE-1a snapshot -> STAGE-1b arg_sel
-> pre-pick -> output), the CAM per-entry vector refactor, and finally the
pre-pick operand muxing of PUMICE-024 did exactly what the task asked for. The
current measurement on the same board and harness, at the HIGHER 75 MHz
target:

    WNS                 +0.009 ns   against 13.333 ns (75 MHz)
    Failing endpoints      0 / 72896
    ENHANCED tier       +0.005 ns, 0 failing

The task's secondary claim -- "PUMICE-006 was never synthesized" -- is also
stale: all three mode axes are in the board build, and the paging predictors
were restored to it on 2026-09-09.

Closed against evidence rather than assumption; the remaining pick-cone work
is performance (the auto-precharge head advance under strict ordering), not
closure, and it is recorded on PUMICE-021 in this file.

## PUMICE-022 — board validation: WRITE TARGET MET (570 MB/s), READ CEILING FOUND
**Status:** closed 2026-09-10 — measured on silicon; read shortfall re-filed as PUMICE-025

Nexys A7 (210292BFA3EE), 75 MHz / DDR2-300, base-tier bitstream at
3c66f442d. Peak is 600 MB/s (75 MHz x 8 B).

**Integrity first:** a7 read leveling found a clean eye (bitslip 0, tap 4,
width 10); 32 MB memtest 8/8 chunks clean, 0 dirty; every characterization
point passed its integrity check (12/12, then 13/13, then 32/32). So the
whole 2026-09-08/09 body of work -- read return ring, write-lead block, JEDEC
timings, restored paging modes, base-build order modes, pre-pick muxing --
is data-clean on hardware.

**Bandwidth, best config (`open_page` and equivalents, row_major BL8):**

| Direction | Measured | Target | Peak | Result |
|---|---|---|---|---|
| Write | **570.0 MB/s** | 510 | 600 | **MET** (95.0% of peak) |
| Read | **291.7 MB/s** | 450 | 600 | missed (48.6% of peak) |

> **CORRECTED 2026-09-10.** The first pass reported `refresh_credit` at
> 574.0/292.2 as the best config. That was an ARTIFACT of run order, not a
> result. `pumice_char.ControllerConfig.apply()` only programmed a mode axis
> when the preset set it, so a preset that left `page_mode` unset inherited
> the previous config's. `refresh_credit` is a CLOSE-page preset and ran
> straight after `rbl_dyn`, inheriting `page_mode=7`, whose predictor kept the
> page open. Standalone it measures 33.8/35.8, which is the correct
> close-page number. apply() now programs every axis on every config
> (0 = build default) so nothing is inherited; the re-run is 36/36
> integrity-clean and order-independent.

For scale: this path measured 12.7 MB/s flat on 2026-07-08 and ~2% of peak.
Writes are now essentially at the data-path limit.

**The read ceiling is structural, not a tuning problem.** Read bandwidth is
291.7-292.2 MB/s and read latency 49.2 cycles in EVERY configuration that
streams at all, and it does not move with:
- burst length -- bl4 290.8, bl8 291.7, bl16 291.7 (identical). This rules out
  an outstanding-transaction or Little's-law limit: more bytes per transaction
  would raise it.
- access pattern -- incremental, row_major identical.
- paging mode -- open_page, adapt_time, adapt_access, rbl_dyn all 291.7.
- scheduling -- age_threshold identical to FR-FCFS.

48.7% of peak, invariant to everything above the return path, is the signature
of a return path that moves one AXI beat every other cycle while the write path
moves one per cycle. Re-filed as PUMICE-025 with this evidence.

**Mode characterization (row_major BL8, MB/s write/read):**

Re-measured order-independently, 36/36 integrity:

| Config | Write | Read | Note |
|---|---|---|---|
| `open_page` | 570.0 | 291.7 | the ceiling; four configs tie here |
| `age_thr` | 570.0 | 291.7 | starvation bound is FREE |
| `adapt_time` | 570.0 | 291.7 | |
| `adapt_access` | 570.0 | 291.7 | predictor holds the page open |
| `rbl_dyn` | 570.0 | 291.7 | **hill-climb works on silicon** |
| `rbl_static` | 33.8 | 36.9 | miss_thresh=2 too aggressive for streaming |
| `inorder` | 33.8 | 35.8 | 16x cost, as sim predicted |
| `refresh_credit` | 33.8 | 35.8 | CLOSE-page; credits do not rescue close-page |
| `baseline` | 33.8 | 35.8 | CLOSE-page reference |

The split is binary: anything that keeps the page open reaches 570/291.7,
anything that closes per access sits at ~34/36. Nothing lands in between,
which is what a command-bus-bound design looks like -- see the BL4 note in
PUMICE-025.

Two results worth keeping:
- **rbl_dyn vindicates the dynamic threshold.** `rbl_static` at the same base
  miss threshold collapses to 33.8 MB/s because it closes pages on a streaming
  pattern; `rbl_dyn`'s per-epoch hill-climb backs the threshold off and
  recovers full bandwidth. That is precisely the "lesser-known alternative
  that wins in a specific situation" the mode work exists to demonstrate, and
  it only shows on real traffic.
- **age_threshold is free.** Same bandwidth as plain FR-FCFS, so the
  starvation bound costs nothing until it engages. It is the mode to reach for
  when in_order is being considered for latency reasons -- in_order costs 17x
  on this pattern.

## PUMICE-021 — paging_sched_cross in_order floor: MISCALIBRATED FLOOR, not an RTL stall
**Status:** closed 2026-09-09 — diagnosed by measurement, floor re-cut by mechanism

The floor failure (`static_close x order_in_order` 37.87%, later joined by
`rbl_static` 37.87% and `rbl_dyn` 44.14%, against IN_ORDER_FLOOR=0.45 whose
comment expected ~56.3%) is the honest cost of the mode. It is NOT a stall
defect and there is nothing to fix in the RTL.

**Discriminator.** Across the eight paging modes under in_order, the split is
exact: every mode that actually drives AUTO-PRECHARGE sits at 37.87-44.14%
(static_close, rbl_static, rbl_dyn) and every mode that does not sits at
exactly 80.33% with stall=94 (build_default, static_open, fixed_open,
adapt_time, and adapt_access -- the last is AP-capable but never closes at the
default counter shape this sweep programs).

**Mechanism, measured** with a command-cadence probe on this exact window
(2026-09-09):

    static_open  x in_order  util 89.51%  ops {ACT:8, WR:64}   gaps 4x63, 8x8
    static_close x in_order  util 36.89%  ops {ACT:26, WRA:26} gaps 4x25, 8x34

Non-AP paging activates a row once and then streams columns at tCCD: ONE
command per access, every gap 4 cycles. AP paging makes every access a pair of
DEPENDENT commands, ACT then column-with-auto-precharge: ACT->col is tRCD
(gap 4) and col->next ACT is the head advancing through the arbiter's 3-stage
pick pipeline (gap 8). A 12-cycle period instead of 4, so about a third of the
utilization. Under FR-FCFS other banks' entries fill those gaps, which is why
the same windows read 100% there; strict ordering cannot fill them by
definition. The 0.45 floor and its 56.3% note predate the pipelined arbiter,
which is why every AP mode landed just under it.

**Resolution.** The test now carries floors split by mechanism -- 0.75 for the
non-AP paging modes, 0.30 for the AP ones -- with the probe numbers recorded
in the comment, plus an assertion that the AP modes are actually present so
the split cannot silently cover nothing. A regression in either class still
fails. Shortening the col->ACT head advance would lift the AP numbers and is
tracked as a performance item under PUMICE-024, not a correctness one.

## PUMICE-020 — multiid read-return accounting: hist total != txn_count (data clean)
**Status:** closed 2026-08-26 — root cause found (AMBA-HISTCH1); 1:1 check moves to the observer path (PUMICE-016) (was: open 2026-08-25, deterministic, observability-only)

`col_major_bl8_multiid` (id_mode=LFSR) at medium@1000 reports a 1:1 violation:
latency-hist total 168409 vs txn_count 64000 (EXTRA returns) — while the DATA
integrity is clean (0 beats mismatched after the device-wrap fix). The value is
byte-identical across all five controller configs, so it is deterministic and
config-independent → an accounting behaviour of the LFSR-ID x chopped-burst
path, not nondeterministic duplication. Sequencing in `measure()` is clean
(clear_stats after programming, freeze before readback), so it is not
cross-scenario accumulation.

First suspect: `axi_perf_latency_hist` transaction-boundary tracking under
many concurrent IDs — one AXI bl8 burst is 8 chopped BL4 DRAM commands, and
per-ID RLAST collapse may be miscounted when IDs interleave. July's basic-scale
run showed the small-N version (64007 vs 64000). Severity: harness
observability only — the 1:1 check is doing its job of flagging it; data-path
1:1 is separately proven by the CRC/mismatch counters.

Repro: `pumice_master.py --char --char-configs baseline --char-level medium
--char-scale 1000` and watch col_major_bl8_multiid; or in sim,
TEST_CHAR_PROFILE with a multiid scenario over the loopback.

**CLOSED 2026-08-26 (direction change).** Root cause FOUND, two layers,
both in the bespoke harness perf path (see AMBA-HISTCH1 in the amba
ledger): (1) hist timestamp FIFO at MAX_OUTSTANDING=8 vs a ~10+ deep
engine admission domain silently dropped samples (sim: up to 6/64 missing
even single-id; fixed by 32 in ddr2_char_macro, after which bl4/8/16/gap
are EXACT 64/64); (2) axi_perf_latency_hist at NUM_CHANNELS=1 decodes ID
BIT 0 as a channel index into a one-entry array — Verilator drops the
odd-id accesses (sim: deterministic 33/64 = the even-id subset), synthesis
aliases them (the board's EXTRA side, 168409 vs 64000). Sean's direction
(2026-08-26): do NOT keep monitor/perf logic inside pumice — the external
observer block (axi4_intf_master_observer) does this job; the shared-
primitive fix is recorded as AMBA-HISTCH1 for when that module is next
touched. PUMICE-016 (adopt the observer) is the vehicle; the 1:1 check
moves there. The cheap "interesting" counters STAY in pumice per the same
direction: PAGE/SCHED/REF *_STATS, OBS_ROW_HIT, refresh-defer histograms.
The sim repro profile (`multiid_min`) stays in pumice_char.py; its multiid
arm remains red until the observer adoption replaces the bespoke hist.

---

## PUMICE-KMAP — real K-maps for the scheduler, CAMs and DFI layer
**Status:** CLOSED 2026-09-10  **Was blocked on:** [[TOOLING-KMAP]] items 1-4

All six criteria of [[signal-contracts-and-kmaps]] are discharged across the 17
computed maps, the artifacts are consolidated, and both halves are gated so they
cannot silently rot again.

**One workbook, one generator.** Four workbooks from three generators across two
directories became `docs/pumice_signal_contracts.xlsx` from
`docs/gen_pumice_signal_contracts.py`, verified to reproduce all 18 original
sheets cell-for-cell. The old flow LOADED the workbook and appended rows, so
re-running duplicated them (the committed Scheduler sheet had 8 such rows); the
new one builds from scratch and is idempotent. An INDEX sheet separates SPEC
tables from COMPUTED grids and opens with the measured RTL status, so the book
cannot be read as a bug list for a controller that meets its targets.

**Criterion 1 (computed, not drawn) was FALSE for four maps**, now gated.
`rd_col_m`/`wr_col_m` modelled 7 terms against 13; `w_ref_safe`, `w_guarded`,
`w_drain_active` each dropped one. `docs/check_kmap_rtl_sync.py` requires every
RTL identifier on a signal's RHS to be NAMED in the documented expression (folds
stay legal, the fold equation is in [brackets]). **16 of 17 machine-checked, 0
drifted**; the generator REFUSES to write on drift.

**Criteria 3/4/5/6.** Axis-term tables with file:line on the four maps whose axes
are folds; relations on all 17 (constraint or explicit independence note); 38
don't-care cells from cited invariants; Quine-McCluskey implicants printed beside
the documented equation on every map.

**Waves: audited, corrected, extended, RENDERED, in the MAS.** The set was drawn
at tCCD=2 with streams captioned "~100% util" -- impossible, and the RTL settles
it (BURST_WORDS=1, so a column every cycle, which is the measured 571.3 MB/s).
Added seven performance diagrams: 13-17 bad-but-correct (admit gate, ring bound,
page thrash, turnaround thrash, refresh storm) and 18-19 pathological, each
captioned with the board number it produced. `design/check_waves.py` found **11
real defects** in the pre-existing diagrams, five of them labels attached to a
logic level instead of a bus slot (WaveDrom silently shifts every label in the
row onto the wrong segment). `design/render_waves.py` produces SVG+PNG for all
19 and **MAS Chapter 7** embeds every one. Rendering itself exposed that every
caption (101-431 chars) overflowed the image and 23 group labels overlapped --
neither visible in the JSON, neither ever seen because nothing had been rendered.

**The lesson.** A spec written during a debugging campaign dates instantly and
silently: these artifacts asserted a 15%-of-peak controller and five live
defects while the board ran at 95% in both directions. Mechanical checks, not
review, are what keep hand-built collateral honest -- every check added here
failed on its first run.

---

## PUMICE-026 — finish the LiteDRAM same-harness A/B (it is already ~80% built)
**Status:** CLOSED 2026-09-10  **Priority:** was P2
**Intent (Sean):** "drop liteddr into the pumice harness so testing is the same."

**START HERE, DO NOT REBUILD:**
`projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/`

That flow already exists and is documented as **WIRED** in its `HARNESS_PLAN.md`:

- `rtl/char_engine_harness.sv` — DUT-agnostic harness (engines + perf meters +
  bandwidth timer + harness_csr + UART bridge) exposing an AXI4 master.
  Verilator-lint-clean standalone.
- `rtl/litedram_char_top.sv` — board top: `litedram_core` + the harness on
  `user_clk`, `init_done`-gated, AXI user port wired.
- `rtl/filelists/litedram_char_harness.f`, `constraints/litedram_char.xdc`,
  `tcl/build_all.tcl`, `tcl/program_fpga.tcl`, `Makefile`, `regen.sh`,
  `litedram_hp.yml`, and a generated `build_board/gateware/litedram_core.v`.
- A `litedram_hp.yml` deliberately mapped onto a high-perf pumice preset, with
  the mapping table written out in its README.

**Progress 2026-09-10 (commit fdaa7db37):**
- ~~regen with BIOS~~ **DONE.** Core regenerated with a functional BIOS (63 KB
  ROM) and `litedram_hp.yml` moved to **75 MHz / 1:2 / 300 MT/s**, matching the
  point pumice is measured at. The stock 100 MHz / 1:4 would have voided the
  comparison.
- ~~XDC reconcile~~ **NOT NEEDED.** The regenerated core xdc has no ddram pins;
  the harness keeps its pin map.
- Five flow bugs fixed to get synthesis running: `REPO_ROOT` two levels short
  (the `../` count was correct at the pre-move path), `CONVERTERS_ROOT` not
  exported, the tcl filelist reader expanding only `$REPO_ROOT`, `.vlt` lint
  waivers handed to Vivado, and `VexRiscv.v` pinned to a path inside the LiteX
  venv. `regen.sh` no longer hardcodes a `/tmp` venv either.

**DONE 2026-09-10 — measured.** Timing-clean LiteDRAM bitstream (WNS +0.195, after
adding the core's CRG reset-strobe false path), `--char-profile matrix --char-scale 1000`,
14/14 integrity, saved as `docs/char_results/litedram_2026-09-10_matrix.csv` with the
write-up `FINDINGS_litedram_ab_2026-09-10.md`. Headline: LiteDRAM reads 564-579 MB/s
(94-97% of peak) through the identical harness where pumice reads 291.7; writes equal
(~554-569 vs 551-570). The read ceiling is pumice's, not the operating point's -- see
PUMICE-025. Ready to close (move the block to closed.md).

**Progress 2026-09-10 (later) — item 0 DONE, harness matches build-perf:**
Sean asked for the LiteDRAM harness to match the current one; the chosen
route was to extract a shared engine block. `char_engine_block.sv` (chargen
regs + generator array + crossbars + perf, one AXI4 master) is pulled out of
`ddr2_char_macro.sv`, which now wraps pumice around it; `char_engine_harness.sv`
is build-perf's `ddr2_char_harness` minus the controller (same UART bridge,
same `bridge_ddr2_char_axil` address map with `ddr2_apb` terminated, same
`harness_csr` with BUILD_ID "LDR2", same timer/LEDs). `make lint` clean;
Makefile on `make/fpga_flow.mk`; `host/host_litedram_char.py` is the pumice
host with the pumice-CSR surface as no-ops. `FPGA_CLK_HZ` in the top was still
100 MHz after the 75 MHz regen (UART divisor wrong) -- fixed. Bitstream build
in flight; then program, `--char-profile matrix --char-scale 1000`, save CSV.

**Was BLOCKING (now resolved as above).** Synthesis reached the harness and
stopped on **41 port mismatches**: `char_engine_harness.sv` is wired
to a `harness_csr` that no longer exists. The whole per-generator config
surface (`o_cfg_wr_*`, `o_cfg_rd_*`, the start pulses, the CRC readback) moved
out of `harness_csr` into `chargen_regs` when the char framework went to a
16-generator array; `harness_csr` is now 75 ports of global/PHY config only.

Rewire `char_engine_harness.sv` against the current framework — `harness_csr`
for the global surface, `chargen_regs` (`chargen_regs.rdl`) for per-generator
config, and the generator array instead of one wr + one rd engine. The pumice
flow's `ddr2_char_macro.sv` is the reference for how the array is driven today.

Then: host variant (copy `ddr2_char.py` + `pumice_master.py`, drop the
pumice-CSR `set_controller_cfg` writes since LiteDRAM self-configures, keep
engine cfg + perf/timer readout; `harness_csr` is at base 0 here), then
`make bitstream && make program && make characterize`.

**RESOLVED 2026-09-10:** `build-litedram/` was an empty duplicate scaffold
(the never-executed destination of a NEXYS-003 move). It cost this session a
rebuild-from-scratch of the LiteX tooling before the real flow surfaced. It is
now DELETED and every reference points at `flows-litedram-uart/`.

**Tooling notes that ARE new and worth keeping** are in
`flows-litedram-uart/2026-09-10_tooling_notes.md`, with two working scripts
beside it (`bin_nexys_bist_soc.py`, `bin_litedram_bist_run.py`): install LiteX
from git not PyPI (PyPI +
Python 3.12 breaks every target on a migen bytecode-inference bug); the RISC-V
toolchain is already at
`/tools/Xilinx/2025.1/gnu/riscv/lin/riscv64-unknown-elf/bin`; PyPI
`pythondata-software-picolibc` ships incomplete sources so the BIOS build
fails; and `--cpu-type=None` yields a clean timing-met bitstream whose BIST
returns garbage because LiteDRAM's DDR2 init and levelling live in the BIOS.
That last point is why item 1 above says `--bios`.

**Why it matters:** LiteDRAM's read is also ~47% of the raw ceiling while its
write reaches 88%; pumice is at 48.6% / 95.0%. Two independent controllers at
the same read fraction on the same board is the strongest evidence that the
read ceiling is a property of this operating point rather than a pumice defect
(PUMICE-025). Same-harness confirmation would redirect or justify that work.

---

## PUMICE-025 — read bandwidth was pinned at 48.7% of peak (FIXED: now 95%, write parity)
**Status:** CLOSED 2026-09-10  **Priority:** was P1. Target was 450 MB/s read; delivered 571.3.
Residual latency work carried forward as [[PUMICE-030]].
**Found by:** PUMICE-022 board characterization (see closed.md for the full table)

Read bandwidth on silicon is **291.7-292.2 MB/s against a 600 MB/s peak** and
does not move with burst length, access pattern, paging mode or scheduling
mode. Write on the same runs reaches 574.0 MB/s (95.7% of peak).

**What the invariance rules out.** bl4 / bl8 / bl16 measure 290.8 / 291.7 /
291.7 -- identical. If the limit were the number of transactions in flight
(generator `GEN_MAX_OUTSTANDING`, ring `RD_RET_DEPTH`, or a Little's-law
round-trip bound) then doubling the bytes per transaction would raise
bandwidth. It does not, so the limit is a per-cycle rate below the transaction
layer, not a concurrency limit. Read latency is a flat 49.2 cycles throughout.

**2026-09-10 ROOT-CAUSED AND LARGELY FIXED: the read intake admitted one
sub-command every TWO cycles.** `pumice_rd_intake` held a single `r_armed` bit
on the AR skid head to mark "the registered snarf probe belongs to this AR".
The bit was cleared by its own admit and could only be re-set the cycle after,
so admits were capped at 0.5/cycle. One admitted sub-command is exactly one
DRAM burst, and on this board (BL4 on x16, 32-bit beat) one burst is ONE AXI
beat -- so the gate was the bandwidth: 0.5 x 8 B x 75 MHz = 300 MB/s, against
291.7 measured (97% of it). Writes have no such stage (`pumice_wr_intake`
runs AW straight from the meta-FIFO head) which is the entire read/write
asymmetry.

Fixed by staging the AR: the skid head is the AR being probed, a new stage
holds the AR being admitted, and the two advance together (1 admit/cycle).
While the stage is held the probe re-points at the stage, so the hit driving
an admit is never more than one cycle old -- the same RAW-forwarding exposure
the arm bit had, rather than a latched hit that would go stale.

Board result (`board_2026-09-10_read_intake_fix.csv`, 14/14 integrity):

| scenario | read before | read after |
|---|---|---|
| row_major_bl8 | 291.8 | **470.9** |
| row_major_bl16 | 291.8 | **471.0** |
| incremental_bl8 | 291.7 | **463.7** |
| row_major_bl4 | 290.8 | **360.4** |

48.6% of peak -> 78.5%. Writes unchanged (551/570). Timing IMPROVED: WNS
+0.285 ns vs +0.039 before, 0 failing of 94060; area +102 LUT / +35 FF.

**SECOND LIMIT, ALSO FIXED: the read return ring was 32 tickets and the board
build never even set it.** `ddr2_char_macro` did not pass `RD_RET_DEPTH`, so
every board bitstream ran the controller default of 32 regardless. Sustained
read rate is bounded by depth / (ticket alloc -> R drain), and this board's PHY
read latency is ~49 MC cycles, so 32 tickets cap reads near 0.78 of the DRAM
rate -- exactly the 78.5% left after the intake fix. Threaded the parameter
from `ddr2_char_top` through the harness and macro, exposed
`PUMICE_RD_RET_DEPTH` as a build define, and set the board default to **64**.

Board sweep (`board_2026-09-10_read_fixed_ring64.csv`, 14/14 integrity):

| scenario | read @ ring 32 | read @ ring 64 | write |
|---|---|---|---|
| row_major_bl8 | 470.9 | **571.3** | 570.2 |
| row_major_bl16 | 471.0 | **571.3** | 570.3 |
| incremental_bl8 | 463.7 | **556.9** | 551.3 |
| row_major_bl4 | 360.4 | 360.4 | 570.3 |

**Reads now match writes** (571.3 vs 570.2, both ~95% of the 600 MB/s peak) and
are within 1.4% of LiteDRAM's 579.5 through the same harness. Timing +0.283 ns,
0 failing of 94415; ring 64 costs ~158 LUT over ring 32.

**2026-09-10 CONCURRENT LOAD -- the workload where pumice's area pays off.**
Every measurement before this ran a write phase then a read phase, so
read/write turnaround was never paid. Running both directions in one window
(new `concurrent` / `multigen` profiles, disjoint regions, both controllers
through the identical harness):

| scenario | pumice total | LiteDRAM total | ratio |
|---|---|---|---|
| row_major bl8, 1w+1r | **570.1** | 285.6 | **2.00x** |
| incremental bl8, 1w+1r | **552.6** | 247.5 | **2.23x** |
| row_major bl8, 1w+2r | **570.2** | 316.4 | **1.80x** |

pumice holds 95% of peak with one, two and three concurrent generators;
LiteDRAM sits near half peak and its read latency rises from 24.7 to 94.5
cycles on incremental. The global FR-FCFS window batches same-direction
columns and amortises tWTR/tRTW; per-bank round-robin pays it per switch.
Files: `board_2026-09-10_{pumice,lite}_{concurrent,multigen}.csv`.

Not measurable this way: `col_major` / `col_major_interleaved` span the whole
device so generators cannot be placed adjacently, and those rows fail
integrity on BOTH controllers (the wrapped-walk hash artifact `strides_for`
documents). `incremental` under multigen likewise falls back to a far-apart
split that measures page thrash. Only bounded-wrap families place adjacently,
so row_major is the trustworthy multi-generator row.

**What is left.** AxLEN=4 still reads 360.4 while writing 570.3, and it did not
move with ring depth, so it is a third and separate mechanism (per-AR overhead
rather than per-column). Read latency is also still ~49 cycles against
LiteDRAM's 24.7 -- bandwidth is fixed, latency is not. Neither blocks the
bandwidth target; track them here rather than reopening the ceiling story.

**(Earlier) SAME-HARNESS A/B DISPROVED THE OPERATING-POINT THEORY BELOW.** LiteDRAM
behind the identical `char_engine_block` / bridge / host, at the identical 75 MHz / 1:2 /
MR0=0x0432 (BL4, CL3) point, reads 564.1 (incremental) / 579.5 (row_major) MB/s and
writes 554/569 -- `docs/char_results/litedram_2026-09-10_matrix.csv`,
`FINDINGS_litedram_ab_2026-09-10.md`. So a column every MC cycle IS sustainable on
this bus for reads: the 48.6% ceiling is pumice's read command path, not BL4. Writes
already match LiteDRAM, which localises it to AR-accept -> column-issue -> R-return
(return ring / rd CAM / AR-order commit). LiteDRAM's read latency is 24.7 cycles vs
pumice's 49.2: ~25 cycles of extra pipeline per access is the other half of the same
story. The analysis below stands as the description of the write path; its
conclusion about reads does not.

**(Superseded framing) Burst length is the fundamental constraint, and it is NOT read-specific.**
The board runs BL4 (host forces `MR0=0x0432` and `bl=4`; the RDL default is
BL8/0x0433). On a x16 device BL4 is 4 transfers = 8 bytes, and 4 transfers at
300 MT/s is 2 CK = exactly ONE MC cycle at 75 MHz. So sustaining 600 MB/s
demands a column command EVERY MC cycle, on a single-issue command bus: 100%
of command slots must be columns, leaving ZERO for ACT, PRE or REF. Every
activate or precharge costs a full column slot -- 8 bytes -- one for one. That
is why the measured split is binary (570 page-open vs 34 page-closed) with
nothing in between, and it caps how much any scheduler can ever recover.

BL8 would halve the command pressure: 16 bytes per column, each burst
occupying 2 MC cycles, so a column every OTHER cycle saturates and the other
half is free for ACT/PRE/REF. That is the single biggest architectural lever
available and it is worth a build.

**Runtime BL8 does NOT work and needs a rebuild.** Tried 2026-09-10 with
`TEST_MR0=0x0433 TEST_DRAM_BL=8` on the BL4 bitstream: a 16 MB memtest passed
4/4 clean, but the characterization workload was **0/8 integrity** and
bandwidth did not move. The simple memtest is not a sufficient check for this
change. `DRAM_BL` is a compile-time parameter in `ddr2_char_top.sv`
(BURST_LEN_MULTIPLE, harness sizing, column stride) as well as a runtime CSR,
so BL8 requires rebuilding the bitstream with `DRAM_BL = 8`, not just an MR
write. Board was restored to BL4 and re-verified clean afterwards.

But note that BL4 does NOT explain the read/write asymmetry: both directions
need the same one-column-per-cycle rate, and writes achieve 95% of it while
reads achieve 49%. The asymmetry below is still an implementation property.

**Hypothesis:** the read return path delivers one AXI beat every other cycle
where the write path delivers one per cycle. 292/600 = 48.7% is close enough to
exactly half to be worth confirming. With the generator ruled out (below), the
limit is inside the controller's return path. Candidates:
1. ~~The char harness's read CRC-check engine consuming R at half rate.~~
   **RULED OUT 2026-09-10 by measurement.** `axi4_master_rd_crc_check` at fub
   level, across all seven slave timing profiles, holds `rready` asserted on
   **100% of run cycles** (140/140, 269/269, 388/388, 325/325, 201/201,
   1925/1925 ...) with a back-pressure count of **exactly zero** in every
   profile, and transfers 128/128 beats each time. With a backtoback slave
   every beat-to-beat gap is 1 cycle. The generator never throttles R, so the
   ceiling is NOT in the harness. Guarded permanently by the
   `rready_never_throttles` scenario in
   `val/amba/test_axi4_master_rd_crc_check.py`.
2. `pumice_rd_return_ring` drain -- one beat per cycle through the BRAM skid
   vs. the write path's rate.
3. `pumice_dfi_rd_aligner` / `pumice_dfi_cdc` read FIFO width or pop rate.
4. `pumice_rd_intake` R-channel assembly.

The latency view (`rtl/schematics/gen_latency.py`) prints per-path flop counts
and names the combinational feedthroughs for each of these blocks, which is the
fastest way to compare the read and write drain structures side by side.

Do NOT start by tuning the scheduler: every scheduling and paging mode gives
the identical 291.7, so the scheduler is not the constraint.

---

## PUMICE-027 — write responses leave pumice out of AW order; the char write bridge routes B by position
**Status:** CLOSED 2026-09-11  **Priority:** was P2
**Found by:** `test_ddr2_char_macro[bank_parallel]` (the only multi-writer scenario), once the
**RESOLVED 2026-09-11 by the bridge generator, not by pumice.** BRIDGE-016 made
fabric IDs master-unique -- each master-side adapter now emits
`{BRIDGE_ID, id}`, so gen0 issues `0_xxxxxxxx` and gen1 `1_xxxxxxxx` and no two
masters can have the same ID in flight. On the strength of that the slave-side
adapter was regenerated to allocate into a `bridge_cam` keyed by AWID and
**deallocate on the returning BID** (`ALLOW_DUPLICATES=1`, "Mode 2: OOO
support") instead of reading an AW-order FIFO head. Owner lookup is now
unambiguous whatever order pumice returns responses in, and the BRIDGE-010
position-order assertion is gone with the mechanism it guarded.

Landed in the pumice tree via `a1e53e5fd` (which regenerated these bridges to
widen the slave IDs). Verified 2026-09-11: `test_ddr2_char_macro[bank_parallel]`
-- the two-writer test that was the standing failure -- PASSES; the full char
framework is 203 passed / 2 xfailed; the pumice component regression is 219/219;
verilator is clean on both board harnesses. Re-running `regen_bridges.sh`
reproduces the committed RTL byte-identically, so the tree is current with the
generator.

Nothing was needed from pumice. Its write responses still leave in FR-FCFS
order rather than AW order, which remains a legitimate AXI4 behaviour; what
changed is that the fabric no longer assumes otherwise.


macro suite could compile again (the `-Wno-PINMISSING` waiver for the bridge regen's
`unmapped_*` ports). Fails identically on HEAD's inline macro and on the extracted
`char_engine_block`, so it predates the refactor.

**Symptom:** `pumice_wr_adapter.sv:168` BRIDGE-010 `$error` at ~31 us: "slave returned B out of
AW order".

**Be precise about where the gap is — the per-generator B handling IS built and
is correct.** `bridge_ddr2_char_wr_xbar.sv:222-224,413-415` steers B to the
owning master by `bid_bridge_id` and gates each master's `bready` so only the
owner's ready reaches the slave; the master-side adapters pass their own B
through. That is exactly the queued-B, per-generator-ready design, and none of
it is the problem.

The problem is the **KEY the ownership lookup indexes on**. `pumice_wr_adapter.sv:99-129`
pushes the issuing master's `bridge_id` into `wr_fifo` at AW accept and reads it
at the HEAD: `bid_bridge_id = wr_fifo[rd_ptr]`. So "who owns this B" resolves to
"whoever issued the OLDEST outstanding AW", not "whoever issued the AW whose ID
this B carries". When pumice returns B out of AW order the head names the wrong
generator, and then the otherwise-correct per-master handshake completes cleanly
against it. The steering works; it is aimed by position.

Worth noting for the fix: the adapter ALREADY records the AWID per slot
(`wr_id_fifo`, :156) — but only inside `ifndef SYNTHESIS`, purely to drive this
assertion. The information needed to route by ID is being captured in
simulation and thrown away in synthesis. Routing by ID means searching the FIFO
for the matching entry instead of taking the head, i.e. a small CAM over
`WR_FIFO_DEPTH`. pumice's write CAM commits in FR-FCFS order (oldest schedulable per row, not
global AW order), so with two writers interleaving, a younger writer's B can come back before an
older one's. The check is sim-only (`translate_off`); on the board the B would silently reach the
WRONG generator (its bresp/count is credited to the other gen). AXI4 permits the slave's
reordering between IDs, so this is a system contract gap, not a protocol violation.

**Not affecting the numbers taken so far:** every board characterization run drives generator 0
alone (one writer, one reader), where position routing cannot misroute. Only bank_parallel /
multi-generator runs are exposed.

**Fix options (decide, do not patch blind):**
1. pumice: return B in AW order -- the write-side twin of `pumice_rd_return_ring` (the read
   path already holds R returns to AR order). Costs a small ticket ring; keeps the bridge
   position-routed as generated.
2. bridge: regenerate `bridge_ddr2_char_wr` with ID-based B routing (each generator already
   owns a distinct AWID space in bank_parallel). The converters/bridge family is in-order by
   design, so this is a generator feature.
3. Test-only: run bank_parallel with `SCHED_POLICY.order_mode=1` (in_order) -- confirms the
   mechanism, does not fix the board exposure.

Of the three, (2) is the smallest change and matches what the crossbar already
wants to do: the per-master steering and ready gating stay exactly as they are,
only the lookup changes from "head of the FIFO" to "the entry whose AWID equals
this BID". Option (1) is the bigger statement -- it would make pumice's write
responses AW-ordered like its reads, which is a controller guarantee rather
than a harness fix and would suit any position-routed interconnect downstream.

Also note the BRIDGE-010 message prints the ID strings garbled (`%0h` applied to the message
continuation) -- cosmetic, in the generated adapter template.

---

---

## PUMICE-031 — REG_LEVEL never reached pumice's TBs; the medium tier had never run
**Status:** CLOSED 2026-09-11  **Priority:** was P2
**Found by:** the TEST_LEVEL conftest-stamp survey (TOOL-016).

The fub, macro and top conftests each stamped `os.environ['TEST_LEVEL'] =
REG_LEVEL`, and cocotb_test copies os.environ over every per-cell export, so
the grid expanded while every cell ran at the stamped depth. In pumice that hid
a second defect. The Group C TBs (rd/wr intake, core_dfi, top_csr, top) grade
on `basic`/`medium`/`full`, but the stamp fed `gate`/`func`/`full`. Gate and
func both fell through to the `basic` default, and **the `medium` tier had
never run in any regression.**

Fix: each wrapper maps the level once at module scope, exports it per cell,
and its depth tables carry gate/func keys beside basic/medium. The stamps are
gone from all three areas. Commits: `33ed558e5` (fub), `b58366f0b` (top +
macro).

Proof: rd_intake read 6 / 24 / 64 bursts at gate / func / full (func had been
6). `test_pumice_top[wr_rd_b2b_multi]` simulated 10.8 / 23.3 / 42.0 us, its
8 / 24 / 48-burst table. fub FULL 96/96; macro + top FULL 123/123; top FUNC
120/120 (the first medium run); no reruns; FULL node sets unchanged.

Left alone: the 17 directed Group B tests. Their loop counts are protocol
structure, not depth, and they never read the level.

---

## PUMICE-032 — three coverage gaps behind green runs
**Status:** CLOSED 2026-09-11  **Priority:** was P2
**Found by:** the PUMICE-031 sweep.

1. **Silicon-bug guards in no regression.** `test_a7ddrphy_bl4_anchored`,
   `_gear_mismatch`, `_read_window` and `test_axi_rd_device_word_check` sat at
   the dv/tests root, which no area collects. They are now the `phy/` area, in
   the dispatcher's AREAS: 16 pass, 2 skip. The skips are gear_mismatch's own,
   disproven on silicon, and it keeps its reason. `4f7dda96b`.
2. **The macro DFI-layer test ran at gear 0.** It never drove `gear_i`,
   `n_subcmd_i` or the strides, which read 0 under Verilator, so a
   DFI_RATE=2 build ran with phase 1's enables masked. A model that only asked
   whether an enable was non-zero passed anyway. It now drives the board
   default and rejects any partial enable; a gear-0 mutant goes red.
   `b53e2b822`.
3. **A requirement cited a skipped test.** design-requirements.md's
   "gear=MAX bit-identical" row cited "macro regression (109)" (3 tests now)
   and the skipped `test_a7ddrphy_gear_mismatch`. It now names the real
   enforcement: the mask is all-ones by construction, every core/top TB runs
   at gear = MAX, and the item-2 check catches a masked phase. `b53e2b822`.

Side effect: the pre-commit filelist check crashed on a tracked `.sby` that
another session's in-flight rename had deleted, blocking every commit in the
repo. Fixed in `36a971588`.

Not done: `dfi_init_complete_i` is still undriven in the DFI-layer test, which
does not exercise init. No test runs gear < MAX, and the requirement does not
ask for one.
