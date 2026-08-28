<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Closed (done)

---

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
**Status:** closed 2026-08-25 — board re-validated on the fresh bitstream; matrix 65/70 with the 5 residuals split to PUMICE-011 (observability only). Issue #42.

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
`projects/NexysA7/ddr2-characterization/char_results/FINDINGS_pumice_board_2026-07-22.md`
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
  are the multiid 1:1 hist anomaly only (data clean) → split to PUMICE-011.
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

## PUMICE-010 — top-tier shared sim_build races under clean parallel runs
**Status:** open 2026-08-23 — mechanism confirmed twice, serial run is the workaround

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

## PUMICE-011 — multiid read-return accounting: hist total != txn_count (data clean)
**Status:** open 2026-08-25 — deterministic, observability-only

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
touched. PUMICE-008 (adopt the observer) is the vehicle; the 1:1 check
moves there. The cheap "interesting" counters STAY in pumice per the same
direction: PAGE/SCHED/REF *_STATS, OBS_ROW_HIT, refresh-defer histograms.
The sim repro profile (`multiid_min`) stays in pumice_char.py; its multiid
arm remains red until the observer adoption replaces the bespoke hist.
