# Formal Verification TODO

**Last Updated:** 2026-04-17
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
| apb_xbar | 5 | 0 | 0 | 0 | 5 |
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
- [x] sv2v transpiler installed at /mnt/data/tools/sv2v
- [x] Formal directory structure: formal/{common,amba,bridge,stream,converters,apb_xbar}/
- [x] Per-module pattern: formal_*.sv (wrapper) + *.sby (config) + Makefile (for sv2v modules)
- [x] Root Makefile targets: make formal, formal-common, formal-bridge, formal-quick
- [x] .gitignore for sby output directories
- [x] env_python updated with OSS CAD Suite + sv2v paths
- [x] CI workflow includes formal (make formal-common in coverage.yml)

### TODO

- [ ] Migrate remaining stripped-copy proofs to sv2v pipeline
- [ ] Create formal/stream/Makefile for STREAM proofs
- [ ] Create formal/amba/Makefile for AMBA proofs

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

Everything below is blocked on `sv2v` / `yosys` / `sby`, which are not
installed on the laptop. In order:

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

4. **Correct the Infrastructure section of this file.** It states the OSS CAD
   Suite is installed at `/mnt/data/tools/oss-cad-suite`. That is not true of
   the laptop, and the claim is what sent this investigation down the wrong
   path to begin with. Record WHICH machine has it.

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

**Still to do, and it needs a machine with the toolchain:** regenerate the flat
file from the current RTL, re-run prove and cover, and confirm the result. The
same staleness question applies to every other checked-in `*_flat.v` in
`formal/` -- this one was found by accident, and nothing has audited the rest.

**Toolchain note (2026-08-08):** `sv2v`, `yosys` and `sby` are NOT installed on
this workstation, and `/mnt/data/tools/oss-cad-suite` -- the location this
document records under Infrastructure -- does not exist. Nothing under
`formal/` can be run or verified here. That is a change from what this file
asserts, and it is why the items above are recorded rather than closed.

### Prove Errors (9 modules)

| Module | Area | Root Cause | Priority |
|--------|------|------------|----------|
| counter_freq_invariant | common | **Re-diagnosed 2026-08-08, see below** | Fix |
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
| icg | common | cp_enabled unreachable (latch gate timing) | Fix |
| axi_split_combi | amba | 4 cover points unreachable at depth 1 | Fix |

### Prove-Only / Missing Cover (19 modules)

These have prove PASS but no cover task defined, or cover not yet run:

| Module | Area | Notes |
|--------|------|-------|
| cam_tag | common | No cover task |
| counter | common | No cover task |
| counter_bin | common | No cover task |
| fifo_sync_multi_sigmap | common | No cover task |
| math_fp8_e4m3_fma | common | prove-only task |
| math_fp8_e5m2_fma | common | prove-only task |
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
arbiter_priority_encoder, counter_bin_load, counter_bingray, counter_freq_invariant (cover only),
counter_johnson, counter_load_clear, counter_ring, bin2gray, gray2bin, johnson2bin,
glitch_free_n_dff_arn, fifo_sync, fifo_async, fifo_control,
fifo_sync_multi, gaxi_skid_buffer, gaxi_skid_buffer_dbldrn, gaxi_skid_buffer_async,
gaxi_skid_buffer_struct, gaxi_fifo_sync, gaxi_fifo_async, gaxi_drop_fifo_sync,
gaxi_regslice, monbus_arbiter, axi_gen_addr, dataint_crc_xor_shift,
dataint_crc_xor_shift_cascade, dataint_ecc_hamming, dataint_parity, dataint_crc,
dataint_checksum, encoder, decoder, encoder_priority_enable, find_first_set,
find_last_set, count_leading_zeros, leading_one_trailing_one, clock_divider,
clock_gate_ctrl, icg (prove only), shifter_barrel, shifter_lfsr, shifter_lfsr_fibonacci,
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

apb_master, apb_slave, apb5_master, apb5_slave, apb_monitor, apb5_monitor,
apb_slave_cdc, apb5_slave_cdc, axis_master, axis_slave, axi_split_combi (prove only),
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
scheduler (prove), sram_controller_unit, sram_controller, apbtodescr, perf_profiler

**FUB_beats (7 PASS):** axi_read_engine_beats (prove), axi_write_engine_beats (prove),
descriptor_engine_beats (prove), scheduler_beats (prove), alloc_ctrl_beats,
drain_ctrl_beats, latency_bridge_beats

**Macro (3 PASS):** scheduler_group, datapath_rd_test (prove), datapath_wr_test (prove),
scheduler_group_array (prove), monbus_axil_group, cmdrsp_router, stream_config_block

**RAPIDS fub_beats SRAM (4 PASS):** snk_sram_controller_beats, snk_sram_controller_unit_beats,
src_sram_controller_beats, src_sram_controller_unit_beats

### projects/components/converters/ -- 16 of 16 PASS

axil4_to_axi4_rd, axil4_to_axi4_wr, axi4_to_axil4_rd, axi4_to_axil4_wr,
axi4_dwidth_converter_rd, axi4_dwidth_converter_wr, axi4_to_apb_shim,
axi4_to_apb_convert, axi_data_upsize, axi_data_dnsize, peakrdl_to_cmdrsp,
uart_axil_bridge, uart_rx, uart_tx, axi4_to_axil4, axil4_to_axi4

### projects/components/bridge/ -- 1 of 1 PASS

bridge_1x2_rd (address decode mutex, DDR/SRAM range, AXI handshake model)

### projects/components/apb_xbar/ -- 5 of 5 PASS

apb_xbar_wrap_1x2, apb_xbar_wrap_1x3, apb_xbar_wrap_2x3,
apb_xbar_wrap_3x3, apb_xbar_wrap_4x4

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
