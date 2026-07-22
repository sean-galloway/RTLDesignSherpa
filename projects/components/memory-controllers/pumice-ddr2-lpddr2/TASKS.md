<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# pumice — Open Tasks

## TASK-FEATURES: QoS + advanced scheduling (post-cleanup) — PLANNED

Once pumice is CLEAN (board reads validated at the bring-up tuple, refresh
collision fixed + re-soaked on silicon, deskew fully retired, HAS/MAS in sync),
layer in the more sophisticated features planned for the controller: QoS
(per-master/per-ID priority classes into the arbiter pick, ageing/starvation
bounds) and the other advanced-mode work already cataloged in
`projects/components/memory-controllers/ADVANCED_MODES_ROADMAP.md` and the
design-requirements doc (FR-FCFS variants, paging/refresh policy modes).
Entry gate: tiny-tREFI soak 0-dirty on the rebuilt bitstream.

## TASK-GEAR: Generic AXI data-width gearing — RESOLVED (external converter)

Make host `AXI_DATA_WIDTH` a free parameter (32/64/128/256/512) decoupled from the
core width `DW = DRAM_BEAT_WIDTH × DFI_RATE`. Family-wide (DDR2/3/4/LPDDR2), for
future DDR\* IP where each device/PHY pins its own (beat, rate) but the host SoC
wants a fixed convenient AXI width.

Implemented via the EXTERNAL formally-verified `axi4_dwidth_converter_wr/_rd` in a
wrapper `rtl/top/pumice_top_geared.sv` (host width <-> DW; GEAR-1 = generate bypass,
bit-identical). Core datapath untouched. Verified end-to-end
(`test_pumice_top_geared.py`): write bursts at host ∈ {64, 128, 256} round-trip back
through host-width reads (down-gear / bypass / up-gear). Chose external over the
internal gearbox because the datapath was freshly stabilized and the converters are
already formal; also the rearchitecture already solved the original a7ddrphy forcing
function (AXI = beat×rate = 128, a fine width — no gearing needed for the board).

**Design + rationale + deferred internal-gearbox option:** `docs/AXI_DRAM_GEARING_SCOPE.md`

## TASK-ADDRMAP: single-register AXI-address → {bank,row,col} mapping — RESOLVED

`addr_mapper.sv` is now driven by ONE knob — `ADDR_MAP.bank_lsb` (the CSR register
that replaced the old scheme selector) — plus an optional bank XOR-hash
(`ADDR_MAP.hash_en`/`hash_seed`). The mapping is derived by stacking fields around
the bank position: `col_lo(bank_lsb) | bank | col_hi | row | rank`, row LSB invariant
at `CW+BW`. The classic schemes are just settings, no scheme mux:
`bank_lsb == COL_WIDTH` = ROW_MAJOR; `bank_lsb == log2(cols/burst)` = max
BANK_INTERLEAVE (burst locality preserved by col_lo); `hash_en` = XOR_HASH on top.

Landed: RDL ADDR_MAP register (regenerated CSR + regmap via bin/peakrdl_generate.py);
addr_mapper rewritten (single stacked extraction + hash, 3 generate blocks + mux
gone); bank_lsb/hash_en/hash_seed threaded through pumice_axi4_ifc / wr+rd intakes /
pumice_core / pumice_top (driven from hwif_out.ADDR_MAP); program_defaults +
test_pumice_top_csr + core tests updated. FUB conformance (test_addr_mapper) rewritten
to sweep bank_lsb across [0,COL_WIDTH] + hash on/off vs a Python reference — 5/5.
`addr_map_scheme_e` retained only for the retired OLD macro sentinels
(pumice_core_macro / axi_frontend_macro / pumice_config_block), which were carried to
the new intake interface (candidates for future retirement). Full suite: 407 pass, 0
fail (macro 141 + fub/top 266).

## TASK-LPDDR2-INIT: full LPDDR2 mode-register init — RESOLVED

Implemented the JEDEC JESD209-2F LPDDR2 init sequence in `init_sequencer.sv`
(memtype-gated): MRW Reset(MR63) -> ZQ Init(MR10=0xFF) -> MR1(BL8/nWR3=0x23) ->
MR2(RL3/WL1=0x01) -> MR3(DS 40ohm=0x02). The wide MR index (MA up to MR63) reaches
the CA formatter via the ROW request field packed as {MA[5:0], OP[7:0]}
(`dfi_cmd_formatter` unpacks row[13:8]=MA, row[7:0]=OP) — no 3-bit bank-port limit.
Only MR1/2/3 update the CL/CWL/BL shadow; MR63/MR10 are issued but not shadowed.
`mode_register.sv` LPDDR2 CL/CWL decode made JEDEC-faithful (MR2[3:0] RL&WL enum).
Verified: DFISlavePHY now records decoded MRW ({index:data}); `smoke_lpddr2` asserts
init programmed {63:0x00, 10:0xFF, 1:0x23, 2:0x01, 3:0x02}. Formatter conformance +
init_sequencer FUB updated.

NOTE (silicon): the sim gates PHY-init-complete on config-ready (TB) so the sequencer
latches the correct memtype ("config before init"). Real LPDDR2 silicon needs memtype
stable before init — a strap or gating the sequencer's start on CTRL.init_start. DDR2
(the board target) is unaffected: its reset default IS DDR2.

## TASK-LPDDR2-WRPATH: LPDDR2 write-auto-precharge dropped writes — RESOLVED

RESOLVED (RDS-DV DFISlavePHY fix). `workload_mix_lpddr2` had dropped writes under
LPDDR2's HAPPY_HYBRID row-miss policy, which issues WRA (write-auto-precharge). Root
cause was NOT the CA encoding or write cadence: the DFI slave `_handle_command` had
branches for WR/RD but none for WRA/RDA. DDR2's decoder never returns WRA/RDA (it
returns WR/RD and carries auto-precharge in addr bit 10), but the bit-exact LPDDR2 CA
decoder folds AP into the opcode → returns WRA/RDA → fell through → no pending write →
wrdata_en became "stray data beats" and the write was silently dropped. Fix: fold
WRA→WR and RDA→RD in `_handle_command` (auto-precharge already carried in addr bit 10
for both paths). All LPDDR2 traffic tests now pass; xfail removed.

## TASK-TOPCSR: test_pumice_top_csr wr_rd roundtrip returns zero read beats — OPEN (pre-existing)

`cocotb_test_pumice_top_csr` fails its AXI write-then-read phase: read 0 gets
ZERO R beats in 800 cycles (`got=[]`), i.e. the read path never returns —
while `test_pumice_top` (45 read-heavy tests), core, core_dfi, geared and the
whole fub/macro suite pass. **Bisected 2026-07-21: fails identically at HEAD
(95c9490a) with only the filelist fix applied — predates the deskew removal
and the refresh/tRFC arbiter change.** Suspect the CSR-programmed config path
(hwif-driven init) diverging from the TB-driven config the other tops use.
The top tests were compile-broken (missing gaxi_fifo_async deps in the dv/tb
filelists) for some window, so the regression that introduced this was masked.

## TASK-CONFIGAXES: runtime-config axes corrupt data (board + sim) — OPEN

**Board (2026-07-22, first rearch config-axis run):** baseline/inorder 9/14
(col_major family fails only at scale 1000); bank_interleave / open_page /
reorder 0/14. multiid shows 7 EXTRA read returns (hist 64007 != 64000) —
suspect rd-CAM duplicate issue under reorder. Long col-major + refresh
interplay implicated for the baseline-scale failures. Full map + signatures:
`projects/NexysA7/ddr2-characterization/char_results/FINDINGS_pumice_board_2026-07-22.md`
(+ char_2026-07-22_wrapup.csv). Correctness at the baseline config is SOLID
(soak gate green); these are the runtime page-policy/scheme/reorder paths.
Tools: CMD_HISTORY_EN checker, dfi_rd_return_checker, ILA flow.
**Sim repro available** (re-confirmed post-fixes 2026-07-22):
`test_ddr2_char_char_families` fails the bank_interleave family over the
DFI loopback — the config-axis defect is digital and wave-debuggable in
sim; start there, no board required.

## TASK-CHARSIM: test_ddr2_char_char_families integrity fail (bank_interleave/incremental_bl8) — OPEN (pre-existing, same class as TASK-CONFIGAXES)

`bank_interleave/incremental_bl8` fails integrity in the char-families sim
("read engine did not complete", 42 beats mismatched). **Bisected 2026-07-22:
fails identically at HEAD (95c9490a) — predates the deskew removal, the
refresh/tRFC arbiter change, and the no-rmw shadow writes.** Same masked-
regression window as TASK-TOPCSR (the top/char sims were compile-broken by the
dv/tb filelist drift for a period). Suspect the config-switch path
(ADDR_MAP bank_lsb=0 preset) interacting with the read engine.

## TASK-SCHED-REFRESH: refresh collides with an open row (arbiter registered-feedback hazard) — OPEN

**Bug (#2, command-sequencing).** The arbiter (`pumice_cmd_arbiter`) can grant a
`REFab` immediately after an `ACT` to the same bank WITHOUT a `PRE` in between —
refreshing a row that is still open — and the following `RD` then returns garbage
(zero) for that one read. Root: the per-bank "safe signals" (`pumice_bank_timers`
readiness) are COARSE and REGISTERED (2-cycle event→ready latency, see the
`r_guard` note in the arbiter), so the combinational picker issues the `ACT`, and
the refresh path's precharge-before-REF check does not yet see the just-opened row
→ REF fires with the row open.

**Reproduced pre-silicon** in `engine_mirror[64]` (`test_pumice_top`), gear-2/BL8,
sustained b2b: burst 25 shows `ACT@31920000 → REF@31940000 (no PRE) → RD@31980000`
→ read returns `0x0` (golden `0x190000`); refresh cadence ~10.25 µs lands on one
read. On the BOARD (gear-4, ILA `reports/ila_refresh_collide.csv`) the refresh is
correctly sequenced (`RD→PRE→REF→ACT→RD`, no collision) — so this is NOT the board
blocker (the board fails on the separate device-word / half-DFI-word phase skew),
but it IS a real arbiter defect.

**Instrument (built, needs wiring):** `dv/checkers/pumice_cmd_history_checker.sv` —
a FINE-GRAINED per-(rank,bank) command-history shift register (slot = cycles-since
issue) that binds to the arbiter's `cmd_valid/op/rank/bank` and audits JEDEC
same-bank sequencing the coarse gate misses. Ships the refresh-collision assertion
(no `REFab` with any bank row open) plus optional tRCD/tRP/tRAS positional checks.
Coarse = *permission to issue* (forward, lossy); fine = *record of what issued*
(backward, exact) — you need the fine one to audit the coarse one.

**TODO:**
1. `bind` the checker in the arbiter FUB (`test_pumice_cmd_arbiter`) and/or the
   scheduler MACRO (`test_pumice_core_macro`) TBs; add `--assert` to the verilator
   compile args.
2. Reproduce #2 as a directed pre-silicon test — small `tREFI` + sustained
   same-bank reads → the checker fires RED. **The test MUST also do DATA checking**
   (golden read compare), not just the sequencing assertion.
3. Fix the arbiter refresh sequencing: the precharge-before-REF logic must account
   for a just-issued `ACT` (don't grant `REF`/`REFab` while any bank's most-recent
   row-affecting op is an `ACT`), or block the `ACT` when a refresh is being
   sequenced. Mirror the fix in `refresh_ctrl`/`pumice_cmd_arbiter`.
4. Re-verify: checker GREEN, `engine_mirror[64]` burst-25 read == golden, macro
   109 + gear2 + FUB stay green.

Scope note: this checker catches command-SEQUENCING bugs only. The board's actual
read blocker is the DFI-read device-word/phase skew (data-path) — see
`[[project_pumice_pipeline_board_read_regression]]`; pair this with the
DFI-read-boundary device-word DATA check for that class.

## TASK-BRINGUP: board reads WORK — validated tuple + honest measurement (2026-07-21)

The rate-2/BL4 board (BUILD_ID 0x44445232) reads CLEAN. The blocker was never
the analog read path; it was three stacked measurement/config defects:

1. **Sweep axis**: s7ddrphy asserts `rddata_valid` a FIXED `read_latency` (=
   cl_sys+6 = 8) sys cycles after `rddata_en` (pure delay line; ISERDES capture
   is continuous), so for reads `t_rddata_en` only places valid. The DATA
   arrives at its own physical latency — `DFI_TUNING.rddata_delay` slides the
   data onto the valid window. Every failed sweep held rddata_delay=0 where
   alignment is unreachable. **Validated tuple: t_phy_wrlat=1, t_rddata_en=6,
   rddata_delay=7, bitslip=0, IDELAY tap 8 (eye taps 0..16, width 17).**
   Baked into A7Leveling ctor defaults.
2. **False-pass metric**: `wait_engine` default bails when rd_error latches (a
   mismatch latches it) -> `beats_mismatched` read EARLY; and a HUNG read
   counts nothing -> reads back 0 = fake clean. Fixed in bringup_joint_probe /
   A7Leveling._test / train_per_lane (ignore_error=True + require done; hang
   reported distinctly).
3. **RMW poison**: on pre-CDC-fix bitstreams the pumice APB window returns a
   PRIOR transaction's data, so every `rmw=True` write spliced stale garbage
   into preserved fields (set_deskew after set_controller_cfg silently
   reverted wrlat/rden -> leveling swept at reset timing). pumice_device now
   NEVER rmws: shadowed full-word writes seeded from RDL resets,
   `invalidate_shadow()` on soft_reset. (RTL CDC fix already landed in
   apb_slave_cdc; bitstreams in bitstream/ predate it — rebuild to retire the
   hazard on-silicon.)

Residual: intermittent row-sized (256-beat/2KB) read corruption, strongly
refresh-correlated (soak A/B: tREFI default 0/8 dirty, tREFI=0x40 4/4 dirty at
~32-44/1024 beats, tREFI=0xFFFF 0/8) -> this is TASK-SCHED-REFRESH (REFab
granted after ACT with no PRE), now confirmed ON SILICON, not the read path.
Next: fix the arbiter refresh sequencing (plan below), rebuild bitstream (also
picks up the CDC fix), re-soak at tiny tREFI as the regression gate.

## TASK-DESKEW: per-beat DFI read deskew — SUPERSEDED (was never the board fix)

The board read blocker is a HALF-DFI-WORD PHASE SKEW: the a7ddrphy returns the two
64b beats of a 128b DFI read word at DIFFERENT capture latencies (the two packed
sub-reads arrive skewed in time), so a single whole-word capture takes one beat
correct and the other STALE from the previous read -> exactly 2-of-4 device-words
wrong, EVERY read, INVARIANT to rddata_delay (which shifts both beats together and
so can never fix a skew BETWEEN them). This is why leveling found "no passing tap".

FIX: independent per-64b-beat capture delays. `deskew_lo`/`deskew_hi` slide the
LOW/HIGH beat capture (0..3 DFI cycles) so the earlier beat is delayed to meet the
later one. Class-B leveling knobs (config, trained at bring-up, change only when
idle). Trainable — sweep deskew for beats_mismatched==0; structural + stable
(train-once), like bitslip/tap.

DONE:
- `pumice_dfi_rd_aligner.sv`: per-beat delay lines, runtime max-deskew capture so
  deskew 0/0 is BIT-IDENTICAL, zero added latency. Verified (3 existing aligner
  FUB pass; macro 398 pass — no fallout).
- Red->green FUB: `test_pumice_dfi_rd_aligner_deskew` (deskew_hi=1 realigns a
  modelled skewed stream -> correct) + `_deskew_red` (deskew_hi=0 -> the 2/4
  corruption baseline). No PHY model needed.
- CSR: `PHY_TIMING.deskew_lo[25:24]`/`deskew_hi[27:26]` (regen in lockstep,
  regmap synced). Threaded top->core->dfi_layer->aligner. Top wr_rd_roundtrip
  green (bit-identical at reset default 0/0).

DONE (cont.):
- FAITHFUL model hook: opt-in per-64b-beat skew in DFISlavePHY (RDS-DV,
  `read_hi_skew`/`read_lo_skew`, default 0 = bit-identical; char rate4_x16 skew-off
  3/3 pass). Char env knobs `TEST_READ_HI_SKEW`/`TEST_DESKEW_HI`.
- Host `set_deskew()` (pumice_device -> PHY_TIMING by name) + `train_deskew.py`
  sweep (deskew_lo x deskew_hi, phase-distinct pattern, pick mism==0) + `make
  train-deskew`.

DONE (integration red->green):
- Refined the model to a per-cycle 1-deep DQ-bus pipeline (`_skew_post`, run EVERY
  dfi cycle incl. idle, via `_skew_cur` set by the serve step) so read N's high
  beat lands on cycle N+1 (the trailing-cycle drive the crude hold lacked).
  `test_ddr2_char_uart_pagehit_rate4_x16_deskew` (skew=1 + deskew_hi=1) PASSES
  (mism==0); skew=1/deskew=0 fails (the 2/4). Skew-off rate4_x16 stays green.

SUPERSEDED: the board read fix was the TASK-BRINGUP tuple above (rddata_delay
alignment + honest metrics + no-rmw writes), at deskew 0/0. The deskew RTL +
`PHY_TIMING.deskew_lo/hi` CSR remain a removal candidate (area/timing recovery;
see issue #39) — delete rather than train.
