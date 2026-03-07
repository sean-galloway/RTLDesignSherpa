# RTL Refactoring Status

**Last Updated:** 2026-03-06
**Branch:** `refactor/clog2-and-debug-cleanup`
**Plan File:** `/home/seang/.claude/plans/shiny-growing-sundae.md`

---

## Overview

Two RTL-wide changes across ~60 files:
1. **$clog2 restriction**: Move ALL `$clog2` usage to parameter sections only
2. **Debug code deletion**: Remove ALL `translate_off`/`translate_on` blocks entirely

**Order:** Delete debug code FIRST, then refactor $clog2

---

## Phase 1: Delete All translate_off/on Debug Code

### Status: COMPLETE

| Directory | Files | Status |
|-----------|-------|--------|
| rtl/common/ | 18 files | DONE |
| rtl/amba/gaxi/ | 8 files | DONE |
| rtl/amba/shared/ | 6 files | DONE |
| projects/components/apb_xbar/rtl/ | 1 file | DONE |
| projects/components/retro_legacy_blocks/rtl/ | 1 file | DONE |

### Files Modified in Phase 1

**rtl/common/** (18 files):
- `cam_tag.sv` - Removed flat_r_tag_array debug
- `sync_pulse.sv` - Removed parameter validation
- `reset_sync.sv` - Removed multiple initial blocks and SVA assertions
- `dataint_crc.sv` - Removed ALGO_NAME param and flat_mem
- `clock_divider.sv` - Removed parameter validation
- `leading_one_trailing_one.sv` - Removed INSTANCE_NAME param
- `find_first_set.sv` - Removed INSTANCE_NAME param
- `find_last_set.sv` - Removed INSTANCE_NAME param
- `grayj2bin.sv` - Removed INSTANCE_NAME param and from instantiation
- `math_bf16_adder.sv` - Removed INSTANCE_NAME from CLZ instantiation
- `math_int_to_bf16.sv` - Removed INSTANCE_NAME from CLZ instantiation
- `math_ieee754_2008_fp32_adder.sv` - Removed INSTANCE_NAME from CLZ instantiation
- `dataint_ecc_hamming_decode_secded.sv` - Removed DEBUG initial block
- `fifo_sync.sv` - Removed INSTANCE_NAME, 3 flat_mem variants, simulation debug
- `fifo_async.sv` - Removed INSTANCE_NAME, flat_mem blocks, BRAM warning, simulation debug
- `fifo_async_div2.sv` - Removed INSTANCE_NAME, grayj2bin INSTANCE_NAMEs, flat_mem blocks, simulation debug
- `testcode/fifo_sync_multi.sv` - Removed INSTANCE_NAME param and instantiation param
- `testcode/fifo_sync_multi_sigmap.sv` - Removed INSTANCE_NAME param and instantiation param

**rtl/amba/gaxi/** (8 files):
- `gaxi_fifo_sync.sv` - Removed INSTANCE_NAME, flat_mem (3 variants), simulation debug
- `gaxi_fifo_async.sv` - Removed INSTANCE_NAME, grayj2bin INSTANCE_NAMEs, flat_mem (3 variants), simulation debug
- `gaxi_drop_fifo_sync.sv` - Removed INSTANCE_NAME, flat_mem (3 variants), extensive simulation debug
- `gaxi_skid_buffer.sv` - Removed simulation debug section
- `gaxi_skid_buffer_async.sv` - Removed INSTANCE_NAME in instantiation, simulation debug
- `gaxi_skid_buffer_dbldrn.sv` - Removed simulation debug and assertions
- `gaxi_skid_buffer_struct.sv` - Removed struct_zeros init block, debug monitoring
- `gaxi_regslice.sv` - Removed assertions/diagnostics

**rtl/amba/shared/** (6 files):
- `monbus_arbiter.sv` - Removed one-hot grant verification assertions
- `arbiter_wrr_pwm_monbus.sv` - Removed parameter validation and config display
- `arbiter_rr_pwm_monbus.sv` - Removed parameter validation and config display
- `axi_split_combi.sv` - Removed parameter validation (3 blocks total)
- `axi_master_rd_splitter.sv` - Removed parameter validation and integration assertions
- `axi_master_wr_splitter.sv` - Removed parameter validation and integration assertions

**projects/components/** (2 files):
- `apb_xbar/rtl/apb_xbar_thin.sv` - Removed extensive $fdisplay logging (5 blocks)
- `retro_legacy_blocks/rtl/ioapic/ioapic_core.sv` - Removed design verification assertions

### Verification

```bash
# Verify no translate_off remaining in source RTL
grep -r "synopsys translate_off\|synthesis translate_off" rtl/
grep -r "synopsys translate_off\|synthesis translate_off" projects/components/apb_xbar/rtl/
grep -r "synopsys translate_off\|synthesis translate_off" projects/components/retro_legacy_blocks/rtl/
# All should return: No matches found
```

---

## Phase 2: $clog2 Refactoring

### Status: NOT STARTED

### Goal
Move ALL `$clog2` usage to parameter sections only. If `$clog2` appears in:
- Signal declarations → Create new parameter
- Localparams in module body → Move to parameter section

### Files to Modify (~50 files)

**rtl/common/ (~26 files):**
- `fifo_sync.sv` - `localparam int AW = $clog2(DEPTH)` -> parameter
- `fifo_async.sv` - same pattern
- `fifo_async_div2.sv` - same pattern
- `counter.sv` - `logic [$clog2(MAX+1)-1:0]` -> new parameter
- `counter_load_clear.sv` - signal declaration
- `find_first_set.sv` - localparam N, port width
- `find_last_set.sv` - localparam N, port width
- `leading_one_trailing_one.sv` - localparam N
- `count_leading_zeros.sv` - localparam N
- `shifter_barrel.sv` - signal declaration
- `bin_to_bcd.sv` - derived localparams
- `clock_divider.sv` - localparam ADDR_WIDTH
- `dataint_ecc_hamming_encode_secded.sv` - nested $clog2
- `dataint_ecc_hamming_decode_secded.sv` - nested $clog2
- `arbiter_round_robin_weighted.sv` - derived localparams
- `math_bf16_adder.sv` - CLZ_WIDTH, wire widths
- `math_ieee754_2008_fp32_adder.sv` - CLZ_WIDTH, wire widths
- `math_int_to_bf16.sv` - CLZ_WIDTH
- `math_bf16_max_tree.sv` - derived localparams
- `grayj2bin.sv` - localparam N

**rtl/amba/ (~15 files):**
- `apb_monitor.sv` - signal declarations for idx
- `apb5_monitor.sv` - signal declarations for idx
- `axi_monitor_reporter.sv` - multiple signal declarations
- `axi_split_combi.sv` - LOG2_BYTES_PER_BEAT
- `arbiter_monbus_common.sv` - signal/localparam
- `arbiter_wrr_pwm_monbus.sv` - port declaration
- `arbiter_rr_pwm_monbus.sv` - similar
- Plus gaxi_* files with AW parameters

**projects/components/ (~15+ files):**
- `stream/rtl/macro/stream_core.sv` - array signal widths
- `stream/rtl/macro/stream_core_mon.sv` - array signal widths
- `stream/rtl/fub/stream_latency_bridge.sv` - signal declaration
- `stream/rtl/fub/axi_write_engine.sv` - localparams
- `stream/rtl/fub/axi_read_engine.sv` - localparams
- `stream/rtl/fub/sram_controller_unit.sv` - ADDR_WIDTH
- `rapids/rtl/fub/sink_sram_control.sv` - localparams
- `rapids/rtl/fub/source_sram_control.sv` - SRAM_ADDR_WIDTH
- `bridge/rtl/bridge_cam.sv` - COUNT_WIDTH
- `converters/rtl/*.sv` - PTR_WIDTH, SIZE_VAL
- `apb_xbar/rtl/apb_xbar_thin.sv` - signal declarations
- `delta/rtl/delta_axis_flat_4x16.sv` - signal array
- `misc/rtl/axi4_slave_rom.sv` - ROM_ADDR_WIDTH

### Transformation Patterns

**Pattern A: localparam -> parameter**
```systemverilog
// BEFORE
module fifo #(parameter int DEPTH = 16) (...);
    localparam int AW = $clog2(DEPTH);

// AFTER
module fifo #(
    parameter int DEPTH = 16,
    parameter int AW = $clog2(DEPTH)
) (...);
```

**Pattern B: Signal declaration -> new parameter**
```systemverilog
// BEFORE
logic [$clog2(MAX_TRANS)-1:0] w_idx;

// AFTER
// Add to parameters:
parameter int IDX_WIDTH = $clog2(MAX_TRANS)
// Change signal:
logic [IDX_WIDTH-1:0] w_idx;
```

**Pattern C: Nested $clog2**
```systemverilog
// BEFORE
localparam int ParityBits = $clog2(WIDTH + $clog2(WIDTH) + 1);

// AFTER
parameter int WIDTH_LOG = $clog2(WIDTH),
parameter int ParityBits = $clog2(WIDTH + WIDTH_LOG + 1)
```

---

## Testing Strategy

### After Phase 2 completion:
```bash
# Lint all modified files
verilator --lint-only <modified_files>

# Run tests
pytest val/common/ val/amba/ -v
```

---

## How to Resume

1. Checkout the branch:
   ```bash
   git checkout refactor/clog2-and-debug-cleanup
   ```

2. Phase 1 is COMPLETE - no action needed

3. Start Phase 2 by finding all $clog2 usage outside parameters:
   ```bash
   grep -rn '\$clog2' rtl/ --include="*.sv" | grep -v "parameter"
   ```

4. Apply transformation patterns above to each file

5. Lint and test after each batch of changes

---

## Notes

- Coverage directories (`coverage_merged/`, `coverage_combined/`, etc.) contain generated files that will be refreshed - don't edit these
- The plan file at `/home/seang/.claude/plans/shiny-growing-sundae.md` has the original full plan
- User explicitly said to delete ALL debug code, even if it can't be recreated in bind files
