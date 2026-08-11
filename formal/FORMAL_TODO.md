# Formal Verification TODO

**Last Updated:** 2026-08-09
**Total Proved:** 324 modules (prove+cover PASS), 330 total with prove-only
**Tool Chain:** sv2v + SymbiYosys + yosys + z3 (OSS CAD Suite 0.62)

---

## Summary

| Area | Pass (prove+cover) | Prove-only | Error | Deferred | Total with .sby |
|------|-------------------|------------|-------|----------|-----------------|
| common (non-math) | 53 | 4 | 1 | 0 | 58 |
| common (math) | 165 | 2 | 7 | 0 | 175 |
| amba | 41 | 3 | 0 | 0 | 44 |
| stream | 19 | 10 | 1 | 2 | 30 |
| converters | 16 | 0 | 0 | 0 | 16 |
| bridge | 1 | 0 | 0 | 0 | 1 |
| apb4_xbar | 5 | 0 | 0 | 0 | 5 |
| **Total** | **300** | **19** | **9** | **2** | **329** |

**Notes:**
- "Prove-only" = prove PASS but no cover task in .sby, or cover MISSING
- "Error" = prove ERROR (yosys parse/flatten failures) or cover FAIL
- stream_top_ch8 has no .sby (too large for BMC, verified via simulation)

---

## Infrastructure

### DONE

- [x] SymbiYosys + z3 solver installed and working
- [x] OSS CAD Suite 0.62 installed at /mnt/data/tools/oss-cad-suite
      **on the WORKSTATION** (the machine with /mnt/data/github). The laptop
      does NOT have it — that unrecorded distinction is what mis-directed the
      2026-08-08 investigation. Verified present 2026-08-09.
- [x] sv2v transpiler installed at /mnt/data/tools/sv2v (workstation, v0.0.13)
- [x] Formal directory structure: formal/{common,amba,bridge,stream,converters,apb4_xbar}/
- [x] Per-module pattern: formal_*.sv (wrapper) + *.sby (config) + Makefile (for sv2v modules)
- [x] Root Makefile targets: make formal, formal-common, formal-bridge, formal-quick
- [x] .gitignore for sby output directories
- [x] env_python updated with OSS CAD Suite + sv2v paths
- [x] CI workflow includes formal (make formal-common in coverage.yml)

### TODO

- [ ] Migrate remaining stripped-copy proofs to sv2v pipeline
- [ ] Create formal/stream/Makefile for STREAM proofs
- [ ] Create formal/amba/Makefile for AMBA proofs

### CDC area consolidated (2026-08-10)

`formal/cdc/` had held the real collateral for every rtl/cdc module since
the CDC reorg, but NO Makefile ran it - `make formal` never touched a CDC
proof, while ten 0-sby output-debris twins under `formal/common/` made the
area look covered. Fixed: `formal/cdc/Makefile` created (12 modules,
prove/cover/all), wired as `formal-cdc` into formal/Makefile and the root
Makefile (`make formal` now includes it), the debris deleted (including the
retired fifo_async_div2 and the moved-to-integ_common fifo_sync_multi), and
the CDC modules stripped from formal/common/Makefile's lists. Full area run
green the same day. NOTE: formal/integ_common has the same no-Makefile gap
- its two proofs run by hand; fold it in when someone touches that area.

### New arbiters proved (2026-08-10)

`arbiter_deficit_round_robin` and `arbiter_token_bucket` (the COMMON-007
additions) now carry harnesses, registered in formal/common/Makefile:
- DRR: family safety set (one-hot, subset-of-$past(request), id, reset)
  plus ap_zero_quantum (a disabled client is never granted) with req_cost
  left FREE - the solver may mutate a cost in the completion cycle, which
  is the harshest test of the r_cost_arb pipeline. Covers witness replenish
  accumulation externally (grant only after idle request-held cycles).
- Token bucket: the tokens observability port makes the contract assertable
  - cap invariant every cycle, gate-only-masks, bypass transparency,
  dry/net-of-spend blocking, exact spend debit - against a FREE downstream
  arbiter. Static-config limitation noted in the wrapper (cap-decrease
  clamp is sim-verified, not proved).
- All four new module-specific properties MUTATION-CHECKED: eligibility-
  ignores-quantum, debit-removed, raw-token gate, inverted bypass each
  flipped prove to FAIL and back to PASS on restore.

### pwm prove FAILS - RESOLVED 2026-08-11: stale harness (COMMON-023)

The post-prefix-sweep re-verification (11 of 12 touched modules PASS)
exposed `pwm/prove: FAIL` - ap_done_matches_shadow and ap_duty_full at
step 6. NOT the sweep: the pre-sweep RTL fails identically (verified by
checking out the parent commit's pwm.sv). COMMON-021's audit only re-ran
counter_freq_invariant for common, so this failure has likely hidden
behind stale results for months. The harness carried a shadow FSM
with the PRE-FIX repeat comparison: the RTL's off-by-one repeat-done fix
(Kimi round_2, 3218490c, 2026-07-23) never reached the shadow, and no
formal re-run happened between then and the sweep - 18 days of silent
FAIL behind an April PASS in the records. Shadow repaired to the corrected
contract, prove+cover PASS (5 covers reached), and mutation-checked:
re-breaking the RTL comparison flips prove to FAIL. The rule this buys:
an RTL semantics change on a module with a formal dir carries its proof
re-run in the SAME commit.

---

## Findings (Bugs Found by Formal)

### descriptor_engine multi-driver (FIXED 2026-04-17)

- **descriptor_engine.sv** and **descriptor_engine_beats.sv**: `r_descriptor_error` was
  driven from two separate `always_ff` blocks (main FSM + address-0 detection).
- **Fix**: Consolidated address-0 error detection into the main FSM block.

### stream_core constant-driven user ports (FIXED 2026-04-17)

- **stream_core.sv**: `fub_rd_axi_ruser` and `fub_wr_axi_buser` were tied to `'0`,
  causing yosys to reject the constant-driven output port during flatten.
- **Fix**: Changed to passthrough channel ID (`UW'(fub_rd_axi_arid)`) for traceability.

### latency_bridge over-constrained cover (FIXED 2026-04-17)

- **formal_stream_latency_bridge.sv** and **formal_latency_bridge_beats.sv**: The assumption
  `assume(!(s_valid && !s_ready))` contradicted the `cp_backpressure` cover goal.
- **Fix**: Removed the producer constraint (valid/ready protocol allows valid regardless of ready).

### AXI Handshake Stability (RESOLVED, earlier)

- **axi_read_engine**, **axi_write_engine**: AR/AW outputs are combinational (pre-skid interface).
  Downstream `gaxi_skid_buffer` in `stream_core.sv` registers signals per AMBA IHI0022E A3.2.1.
- **Status**: RESOLVED -- formal wrappers updated to document pre-skid interface.

---

## Non-Passing Modules

### Run list for a machine WITH the toolchain (added 2026-08-08)

**2026-08-09 (workstation): items 1, 2 and 4 are DONE — results inline below.
Item 3 (cover tasks) remains, tracked as COMMON-021 for the common slice.**

Everything below was blocked on `sv2v` / `yosys` / `sby`, which are not
installed on the laptop (they ARE on the workstation). In order:

1. **Audit every checked-in flat file for staleness, not just this one.**
   `counter_freq_invariant_flat.v` was found three months out of date by
   accident. Nothing has checked the rest, and the failure is silent -- a
   proof passes against RTL that no longer exists.

       for d in formal/*/*/; do
         [ -f "$d/Makefile" ] || continue
         git -C . log -1 --format="%ad %h" --date=short -- "$d"*_flat.v
       done
   Compare each against the mtime of the `.sv` sources its Makefile lists, or
   better, regenerate and diff. The `check-flat` target added to
   `formal/common/counter_freq_invariant/Makefile` is the pattern -- it
   compares CONTENT, because these files are committed and `git checkout`
   makes every mtime useless.

2. **Regenerate and re-prove counter_freq_invariant.**

       cd formal/common/counter_freq_invariant
       make check-flat            # expected to FAIL first time -- 3 months stale
       make counter_freq_invariant_flat.v
       make prove cover

   Note the RTL gained a `FREQ_STRATEGY` parameter and a `pow2_freq` function
   since April, so the regenerated flat file will differ substantially. If the
   proof fails after regeneration, that is a REAL result about the current
   design and belongs in this file, not a tooling problem.

3. **Close out the 4 prove-only modules** -- prove PASSes but the `.sby` has no
   cover task, so nothing shows the properties are non-vacuous. Add cover
   tasks; a property that passes because it is unreachable is the formal twin
   of the silent-pass tests found in val/common this month.
   **DONE 2026-08-09 — and the premise had already expired.** All four
   (cam_tag, counter, counter_bin, fifo_sync_multi_sigmap) ALREADY carry
   `[tasks] prove cover` in their .sby — cover tasks were added after this
   table was written (fifo_sync_multi_sigmap's in commit b861ce6f). cam_tag,
   counter and counter_bin re-run fresh 2026-08-09: prove PASS + cover PASS,
   every cover statement reached, zero unreached. fifo_sync_multi_sigmap's
   fresh re-run (prove depth 25 / cover depth 40, ~26 min of z3) completed
   the same day: prove PASS + cover PASS, all 4 covers reached
   (cp_write/cp_read/cp_full/cp_drain). icg's cover ALSO passes now (cp_enabled
   reached — the "unreachable" entry below is history). Note:
   fifo_sync_multi_sigmap's formal dir MOVED to `formal/integ_common/` with
   the July integ_common extraction; the leftover gitignored output debris
   under `formal/common/fifo_sync_multi{,_sigmap}/` was deleted 2026-08-09.

4. **Correct the Infrastructure section of this file.** It states the OSS CAD
   Suite is installed at `/mnt/data/tools/oss-cad-suite`. That is not true of
   the laptop, and the claim is what sent this investigation down the wrong
   path to begin with. Record WHICH machine has it.

### Flat-file staleness audit results (2026-08-09, workstation)

Method: for all 48 dirs with a committed `*_flat.v`, force-regenerate
(`make -B <name>_flat.v`) and content-diff against git. Tree restored to
committed state afterward — the regen is cheap to redo; what is EXPENSIVE is
the re-proving, which each area owns.

**Only 7 of 48 flat files are content-current.** 36 differ after regeneration;
5 cannot regenerate at all. The staleness is real content drift, not tool
noise — even the smallest diffs are functional (e.g. every rapids flat file
carries `fifo_control` `DEPTH = 16` where the RTL default is now 8). Every
proof run against those 36 files validated RTL that no longer exists.

- **Current (7):** common/counter_freq_invariant (the one the alarm was
  raised over, ironically), amba/axi_monitor_addr_check,
  amba/axi_monitor_trans_mgr, converters/peakrdl_to_cmdrsp,
  rapids/axi_read_engine_beats, rapids/scheduler_beats, stream/cmdrsp_router.
- **Stale (36):** 10 amba (the 4 `axi4_*_mon` + base/filtered diffs are
  80-220 lines — the monitor rework landed after the last regen; the rest are
  1-10 lines), 6 converters, 9 rapids (all the 1-line `fifo_control` depth
  drift), 11 stream (scheduler_group_array is 2353 insertions — heavily
  drifted).
- **Regen FAILED (5):** `converters/axi4_to_apb4_shim` (DEPS points at
  `rtl/amba/cdc/cdc_2_phase_handshake.sv`, which moved — DEPS drift, fix with
  `tools/gen_formal_deps.py`), `stream/axi_read_engine`,
  `stream/axi_write_engine`, `stream/monbus_axil_group`, `stream/stream_core`
  (sv2v internal error in `Convert/Package.hs` — package conversion bug or an
  RTL construct sv2v v0.0.13 cannot handle).

Follow-up per area: regenerate, re-prove, commit flat+results together, and
add the `check-flat` content-diff target (the counter_freq_invariant Makefile
is the pattern) so this cannot silently recur. Only the common slice of this
is COMMON-021; amba/stream/rapids/converters staleness belongs to those areas'
task pages.

**Same-day follow-on finding: the ENTIRE math formal suite was unrunnable.**
A sweep of every source `.sby` for file references that no longer resolve
found 147 broken configs — all `formal/common/math_*`, all pointing at
`../../../rtl/common/math_*.sv`, which moved to `rtl/math/` in the math
split. None of the ~165 math proofs could run at all since that split (sby
dies at file-copy, so at least the failure was loud, unlike the flat-file
staleness). Fixed 2026-08-09 by mechanical rewrite (only refs that exist in
`rtl/math/` were rewritten; all 147 verified resolving afterward).
Spot-verified prove+cover PASS on math_adder_brent_kung_008,
math_multiplier_dadda_tree_008, math_bf16_adder, and both fp8 fma modules
(which also gained cover verification: 5 covers reached each, closing their
"prove-only" rows below). The full 147-module re-run belongs to the math
area's backlog, not COMMON-021.

**Full math re-run done 2026-08-10 (MATH-006): 157/171 configs PASS**, plus
math_mod_3_compress newly added (MATH-005, prove + 7/7 covers,
mutation-checked). Of the 14 non-passes at run time:

- 6 known BMC-intractables (softmax_8 x5, bf16_exp2) still ERROR — recorded,
  not regressions.
- 2 REAL: `math_bf16_mantissa_mult` and `math_ieee754_2008_fp32_mantissa_mult`
  prove FAILED — their harnesses still asserted the pre-MATH-001 folded
  sticky (`guard | sticky`). Harnesses updated to the true-sticky + explicit
  guard-bit contract; both now PASS, guard property mutation-checked
  (swapping the guard mux arms fails p_guard_nonorm). A fix has to land in
  generator + RTL + docs + TB + formal, or the next audit relitigates it —
  see the handbook note `generated-rtl-discipline`.
- 5 heavy multipliers timed out at 1800 s under 8-way parallelism:
  dadda_4to2_011, dadda_tree_032, wallace_tree_csa_032 were never proven
  (FORMAL_PRIORITY rows: priority 0, "Too large"/"Odd size" — unchanged);
  dadda_tree_016 and wallace_tree_016 were recorded PASSING pre-split;
  wallace reconfirmed serially (low8 + boundary, ~35 min), dadda's
  prove_boundary does NOT converge (killed at 1 h parallel, 1 h serial and
  3 h serial z3) while its prove_low8 passes -- honest heavy-bucket entry,
  sby dies loudly. Full disposition in vault/Tasks/math (MATH-006, closed).

Operational gotcha for the next sweep: `sby -f <dir>/<cfg>.sby` resolves the
relative `[files]` paths against the CWD, not the .sby location — run from
inside each config dir or every copy step dies pointing outside the repo.

### counter_freq_invariant, re-diagnosed 2026-08-08

The "Yosys SV syntax error at line 150" entry describes a problem that the
sv2v flow already solves -- line 150 is `if (n <= 1) return lo;`, and the
module's Makefile exists precisely because "Yosys can't parse SV function
return statements". The checked-in `counter_freq_invariant_flat.v` is valid
sv2v output and does contain the converted functions.

**The real problem is staleness, and it is worse than a parse error.** The flat
file was last regenerated 2026-04-17; `rtl/common/counter_freq_invariant.sv`
changed 2026-07-25. Every proof run in between was run against a design that
no longer existed -- a passing proof of the wrong RTL, which is a false
assurance rather than a missing one.

It stayed hidden because the Makefile's timestamp dependency cannot see it: the
flat file is CHECKED INTO GIT, so a clone or checkout stamps it newer than its
sources and `make` never rebuilds. Generated files under version control do not
get to use mtime as their correctness signal.

Two fixes landed in `formal/common/counter_freq_invariant/Makefile`:

1. **`sv2v ... > $@` truncated the target before running.** A missing or
   failing sv2v destroyed the checked-in file and left 0 bytes. Writes go to a
   temp and `mv` on success now. This is not theoretical -- it happened on a
   machine without the OSS CAD Suite, and the file had to be restored from git.
2. **A `check-flat` target** that regenerates to a temp and DIFFS against the
   committed file, failing if they differ. Content, not timestamps. Run it
   before trusting any result from this harness, and ideally from CI.

**RESOLVED 2026-08-09 (workstation): the flat file was never stale.**
`make check-flat` passes — regenerated content is identical to the committed
file. The "3 months stale" diagnosis was date-based, and both dates misled:
`FREQ_STRATEGY` + `pow2_freq` landed 2026-04-10, a week BEFORE the last regen
(2026-04-17) and are in the committed flat file; the 2026-07-25 RTL "change"
was the docs kebab-case rename touching only header comments, which sv2v
output does not carry. Content comparison is the only trustworthy signal —
which is the whole reason check-flat exists. Prove and cover re-run
2026-08-09: both PASS, cover points `cp_tick` and `cp_counter_inc` reached
(non-vacuous). The repo-wide audit the entry below asked for has now been run
— see "Flat-file staleness audit results" above; unlike this module, most of
the rest of the repo IS stale.

**Toolchain note (2026-08-08):** `sv2v`, `yosys` and `sby` are NOT installed on
this workstation, and `/mnt/data/tools/oss-cad-suite` -- the location this
document records under Infrastructure -- does not exist. Nothing under
`formal/` can be run or verified here. That is a change from what this file
asserts, and it is why the items above are recorded rather than closed.

### Prove Errors (9 modules)

| Module | Area | Root Cause | Priority |
|--------|------|------------|----------|
| counter_freq_invariant | common | **RESOLVED 2026-08-09: was never stale/broken — prove+cover PASS, see below** | Done |
| math_bf16_exp2 | common | Too complex for BMC | Skip |
| math_bf16_softmax_8 | common | Too complex for BMC | Skip |
| math_fp16_softmax_8 | common | Too complex for BMC | Skip |
| math_fp32_softmax_8 | common | Too complex for BMC | Skip |
| math_fp8_e4m3_softmax_8 | common | Too complex for BMC | Skip |
| math_fp8_e5m2_softmax_8 | common | Too complex for BMC | Skip |
| stream_core | stream | Yosys flatten name collision (2x axi4_master_rd) | Deferred |

### Cover Failures (2 modules, prove PASS)

| Module | Area | Root Cause | Priority |
|--------|------|------------|----------|
| icg | common | **RESOLVED 2026-08-09: cover PASS, both cover points reached** | Done |
| axi_split_combi | amba | 4 cover points unreachable at depth 1 | Fix |

### Prove-Only / Missing Cover (19 modules)

These have prove PASS but no cover task defined, or cover not yet run:

| Module | Area | Notes |
|--------|------|-------|
| cam_tag | common | **RESOLVED 2026-08-09: cover task exists, PASS, 2 covers reached** |
| counter | common | **RESOLVED 2026-08-09: cover task exists, PASS, 2 covers reached** |
| counter_bin | common | **RESOLVED 2026-08-09: cover task exists, PASS, 3 covers reached** |
| fifo_sync_multi_sigmap | integ_common | **RESOLVED 2026-08-09: dir moved to formal/integ_common/; fresh prove+cover PASS, all 4 covers reached** |
| math_fp8_e4m3_fma | math | **RESOLVED 2026-08-09: path-fixed (rtl/math), prove+cover PASS, 5 covers reached** |
| math_fp8_e5m2_fma | math | **RESOLVED 2026-08-09: path-fixed (rtl/math), prove+cover PASS, 5 covers reached** |
| axi_monitor_base | amba | prove_boundary+prove_low8 PASS, no cover |
| axi_monitor_filtered | amba | prove_boundary+prove_low8 PASS, no cover |
| axi_monitor_trans_mgr | amba | prove_boundary+prove_low8 PASS, no cover |
| axi_read_engine | stream | prove_boundary+prove_low8 PASS, no cover |
| axi_read_engine_beats | rapids | prove_boundary+prove_low8 PASS, no cover |
| axi_write_engine | stream | prove_boundary+prove_low8 PASS, no cover |
| axi_write_engine_beats | rapids | prove_boundary+prove_low8 PASS, no cover |
| datapath_rd_test | stream | prove_boundary+prove_low8 PASS, no cover |
| datapath_wr_test | stream | prove_boundary+prove_low8 PASS, no cover |
| descriptor_engine_beats | rapids | prove_boundary+prove_low8 PASS, no cover |
| scheduler | stream | prove_boundary+prove_low8 PASS, no cover |
| scheduler_beats | rapids | prove_boundary+prove_low8 PASS, no cover |
| scheduler_group_array | stream | prove_boundary+prove_low8 PASS, no cover |

### Deferred (not tractable for BMC)

| Module | Area | Reason |
|--------|------|--------|
| stream_core | stream | Yosys flatten name collision (two axi4_master_rd instances) |
| stream_top_ch8 | stream | 40+ source files, 10K+ lines -- state space too large |

---

## Passing Modules by Area

### rtl/common/ -- 218 of 233 PASS

**Non-math (53 prove+cover PASS):**
arbiter_round_robin_simple, arbiter_round_robin, arbiter_round_robin_weighted,
arbiter_priority_encoder, counter_bin_load, counter_bingray, counter_freq_invariant,
counter_johnson, counter_load_clear, counter_ring, bin2gray, gray2bin, johnson2bin,
glitch_free_n_dff_arn, fifo_sync, fifo_async, fifo_control,
fifo_sync_multi, gaxi_skid_buffer, gaxi_skid_buffer_dbldrn, gaxi_skid_buffer_async,
gaxi_skid_buffer_struct, gaxi_fifo_sync, gaxi_fifo_async, gaxi_drop_fifo_sync,
gaxi_regslice, monbus_arbiter, axi_gen_addr, dataint_crc_xor_shift,
dataint_crc_xor_shift_cascade, dataint_ecc_hamming, dataint_parity, dataint_crc,
dataint_checksum, encoder, decoder, encoder_priority_enable, find_first_set,
find_last_set, count_leading_zeros, leading_one_trailing_one, clock_divider,
clock_gate_ctrl, icg, shifter_barrel, shifter_lfsr, shifter_lfsr_fibonacci,
shifter_lfsr_galois, sort, debounce, pwm, reset_sync, cdc_handshake, cdc_synchronizer

**Math -- 165 prove+cover PASS:**
- Adders: 26/26 (brent_kung 8/16/32, han_carlson 16/22/32/44/48/72, kogge_stone, ripple, CLA, carry_save, half, full, full_nbit, addsub)
- Subtractors: 5/5 (full, half, ripple, CLA, full_nbit)
- Multipliers: 14/14 (wallace 8/16/32, dadda 8/16/32, dadda_4to2 8/11/24, wallace_csa 8/16/32, basic_cell, carry_save)
- BF16: 31/33 (all except exp2 ERROR, softmax_8 ERROR)
- FP16: 16/17 (all except softmax_8 ERROR)
- FP32: 16/17 (all except softmax_8 ERROR)
- FP8_E4M3: 20/22 (softmax_8 ERROR, fma prove-only)
- FP8_E5M2: 20/22 (softmax_8 ERROR, fma prove-only)
- IEEE754: 10/10 (fp16 + fp32 adder/multiplier/fma/exponent_adder/mantissa_mult)
- Other: 4/4 (compressor_4to2, prefix_cell, prefix_cell_gray, int_to_bf16)

### rtl/amba/ -- 41 of 44 PASS

apb4_master, apb4_slave, apb5_master, apb5_slave, apb4_monitor, apb5_monitor,
apb4_slave_cdc, apb5_slave_cdc, axis_master, axis_slave, axi_split_combi (prove only),
cdc_handshake, cdc_synchronizer, monbus_arbiter (via common),
axi4_master_rd, axi4_master_wr, axi4_slave_rd, axi4_slave_wr,
axi4_master_rd_cg, axi4_master_wr_cg, axi4_slave_rd_cg, axi4_slave_wr_cg,
axi4_master_rd_mon, axi4_master_wr_mon, axi4_slave_rd_mon, axi4_slave_wr_mon,
axi_master_rd_splitter, axi_master_wr_splitter,
arbiter_monbus_common, arbiter_rr_pwm_monbus, arbiter_wrr_pwm_monbus,
axi_monitor_base (prove only), axi_monitor_filtered (prove only),
axi_monitor_trans_mgr (prove only), axi_monitor_reporter, axi_monitor_timeout,
axi_monitor_timer, amba_clock_gate_ctrl,
gaxi_fifo_async_multi, gaxi_fifo_sync_multi,
gaxi_skid_buffer_multi, gaxi_skid_buffer_multi_sigmap,
gaxi_skid_buffer_async_multi

### projects/components/dmas/stream/ -- 19 of 30 PASS

**FUB (11 PASS):** stream_alloc_ctrl, stream_drain_ctrl, stream_latency_bridge,
axi_read_engine (prove), axi_write_engine (prove), descriptor_engine,
scheduler (prove), sram_controller_unit, sram_controller, apb4todescr, perf_profiler

**FUB_beats (7 PASS):** axi_read_engine_beats (prove), axi_write_engine_beats (prove),
descriptor_engine_beats (prove), scheduler_beats (prove), alloc_ctrl_beats,
drain_ctrl_beats, latency_bridge_beats

**Macro (3 PASS):** scheduler_group, datapath_rd_test (prove), datapath_wr_test (prove),
scheduler_group_array (prove), monbus_axil_group, cmdrsp_router, stream_config_block

**RAPIDS fub_beats SRAM (4 PASS):** snk_sram_controller_beats, snk_sram_controller_unit_beats,
src_sram_controller_beats, src_sram_controller_unit_beats

### projects/components/converters/ -- 16 of 16 PASS

axil4_to_axi4_rd, axil4_to_axi4_wr, axi4_to_axil4_rd, axi4_to_axil4_wr,
axi4_dwidth_converter_rd, axi4_dwidth_converter_wr, axi4_to_apb4_shim,
axi4_to_apb4_convert, axi_data_upsize, axi_data_dnsize, peakrdl_to_cmdrsp,
uart_axil_bridge, uart_rx, uart_tx, axi4_to_axil4, axil4_to_axi4

### projects/components/bridge/ -- 1 of 1 PASS

bridge_1x2_rd (address decode mutex, DDR/SRAM range, AXI handshake model)

### projects/components/apb4_xbar/ -- 5 of 5 PASS

apb4_xbar_wrap_1x2, apb4_xbar_wrap_1x3, apb4_xbar_wrap_2x3,
apb4_xbar_wrap_3x3, apb4_xbar_wrap_4x4

---

## Remaining Work

### Actionable Fixes (3 items)

1. **counter_freq_invariant** -- Fix yosys SV syntax error at line 150 (add sv2v preprocessing)
2. **icg** -- Fix cover point cp_enabled (increase cover depth or relax assumptions)
3. **axi_split_combi** -- Fix 4 cover points (increase cover depth from 1)

### Add Cover Tasks (19 modules)

Many modules only have prove tasks. Adding cover tasks would improve confidence:
- 4 common modules (cam_tag, counter, counter_bin, fifo_sync_multi_sigmap)
- 3 amba modules (axi_monitor_base, axi_monitor_filtered, axi_monitor_trans_mgr)
- 10 stream modules (engines, schedulers, datapaths)
- 2 math modules (fp8_e4m3_fma, fp8_e5m2_fma)

### Skip (Priority 0)

- 6x softmax_8 + bf16_exp2 -- too complex for BMC, low value
- stream_top_ch8 -- too large for BMC (verified via simulation)
