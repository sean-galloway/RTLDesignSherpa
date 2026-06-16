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

# Build-Time Configuration Reference

> Per HAS §5.2 for the full parameter table and HAS §5.1 for the build-vs-runtime philosophy. This chapter is the **build-script-author's** view: which parameters can be tuned at synthesis time and how each flows through the filelists, includes, and FUB instances.

---

## Setting Parameters

Build parameters are passed via the top-level module's parameter port at instantiation:

```systemverilog
ddr2_lpddr2_ctrl #(
    .MEMTYPE              ("LPDDR2"),
    .N_PHASES             (4),
    .NUM_RANKS            (2),
    .NUM_BANKS            (8),
    .AXI_DATA_WIDTH       (128),
    .AXI_ID_WIDTH         (4),
    .AXI_ADDR_WIDTH       (32),
    .ROW_WIDTH            (14),
    .COL_WIDTH            (10),
    .DFI_DATA_WIDTH       (32),
    .DFI_ADDR_WIDTH       (20),       // 20 for LPDDR2; 14 for DDR2
    .SCHEDULER_MODE       ("OOO"),
    .LOOKAHEAD_DEPTH_MAX  (4),
    .PAGE_POLICY          ("HAPPY_HYBRID"),
    .ODT_RULE_MULTIRANK   ("JEDEC_DDR2"),  // forced OFF when NUM_RANKS == 1
    .REFRESH_DEFER_MAX    (8),
    .REFPB_POLICY         ("DARP")
    // ...
) u_memctrl ( ... );
```

For synthesis-script-driven overrides:

```tcl
# Vivado example
set_property generic {
    NUM_RANKS=4
    PAGE_POLICY=HAPPY_HYBRID
    PAGE_PREDICTOR_TABLE_BITS=12
} [get_filesets sources_1]
```

## Filelist Composition

The build's filelist depends on parameter values. Conditional FUBs are included via top-level generate; the filelists include them unconditionally but the synthesis tool elides unused logic. Recommendations:

| Parameter combination                     | Filelist effect                                          |
|-------------------------------------------|----------------------------------------------------------|
| `MEMTYPE = "DDR2"`                        | LPDDR2 encoder code dead-code-eliminated                  |
| `MEMTYPE = "LPDDR2"`                      | DDR2 encoder code dead-code-eliminated                    |
| `PAGE_POLICY = "HAPPY_HYBRID"`            | `page_predictor_fub.sv` instantiated                       |
| `PAGE_POLICY != "HAPPY_HYBRID"`           | `page_predictor_fub` not instantiated; tied output         |
| `SCHEDULER_MODE = "INORDER"`              | OoO comparator network not synthesized                     |
| `NUM_RANKS = 1`                           | `odt_ctrl_fub` collapses to tie-off; cross-rank logic dead |

For aggressive area control, hand-curate the filelist to exclude unused FUBs entirely (rather than relying on tool's dead-code-elimination).

## `rtl/includes/ddr2_lpddr2_config.svh`

This header is generated from the build parameters and contains derived constants used across FUBs:

```systemverilog
`define DDR2_LPDDR2_CONFIG_SVH

`define MEMTYPE_DDR2   "DDR2"
`define MEMTYPE_LPDDR2 "LPDDR2"

// Build-time
`define BUILD_NUM_RANKS  4
`define BUILD_NUM_BANKS  8

// Derived
`define RANK_WIDTH       2     // $clog2(NUM_RANKS)
`define BANK_WIDTH       3     // $clog2(NUM_BANKS)

// Sanity
`if (`BUILD_NUM_RANKS == 1) && (`ODT_RULE_MULTIRANK != "OFF")
    `error "ODT_RULE_MULTIRANK must be OFF when NUM_RANKS = 1"
`endif
```

The header is regenerated whenever the build parameters change.

## Parameter Sanity Assertions

The top-level generate block contains elaboration-time assertions:

```systemverilog
generate
    if (NUM_RANKS == 1 && ODT_RULE_MULTIRANK != "OFF")
        $error("ODT_RULE_MULTIRANK must be OFF when NUM_RANKS = 1");

    if (MEMTYPE == "LPDDR2" && DFI_ADDR_WIDTH < 20)
        $error("LPDDR2 requires DFI_ADDR_WIDTH >= 20 (CA-bus packing)");

    if (MEMTYPE == "DDR2" && DFI_ADDR_WIDTH < ROW_WIDTH)
        $error("DDR2 requires DFI_ADDR_WIDTH >= ROW_WIDTH");

    if (LOOKAHEAD_DEPTH_MAX < 0 || LOOKAHEAD_DEPTH_MAX > 4)
        $error("LOOKAHEAD_DEPTH_MAX must be 0..4");

    if (REFRESH_DEFER_MAX < 1 || REFRESH_DEFER_MAX > 8)
        $error("REFRESH_DEFER_MAX must be 1..8 (JEDEC ceiling)");

    if (NUM_RANKS != 1 && NUM_RANKS != 2 && NUM_RANKS != 4)
        $error("NUM_RANKS must be 1, 2, or 4");

    // ... more sanity checks ...
endgenerate
```

These catch invalid configs at synthesis time rather than letting them silently produce broken silicon.

## Recommended Build Profiles

### Profile A — Tutorial / Smallest Area

```
MEMTYPE              = "DDR2"
N_PHASES             = 2
NUM_RANKS            = 1
PAGE_POLICY          = "OPEN"           // no HAPPY predictor
SCHEDULER_MODE       = "INORDER"        // no OoO logic
LOOKAHEAD_DEPTH_MAX  = 0
TXN_QUEUE_DEPTH      = 4
ODT_RULE_MULTIRANK   = "OFF"
ADDR_MAP_SCHEMES_SYNTH = {ROW_MAJOR}     // one scheme only
```

Estimated area: ~7,000 LUTs on XC7A100T. Suitable for the smallest embedded SoCs.

### Profile B — Typical Embedded SoC

```
MEMTYPE              = "DDR2"            // or "LPDDR2" depending on board
N_PHASES             = 4
NUM_RANKS            = 1
PAGE_POLICY          = "HAPPY_HYBRID"
PAGE_PREDICTOR_TABLE_BITS = 12
SCHEDULER_MODE       = "OOO"
LOOKAHEAD_DEPTH_MAX  = 4
TXN_QUEUE_DEPTH      = 16
REFRESH_DEFER_MAX    = 8
ADDR_MAP_SCHEMES_SYNTH = {ROW_MAJOR, BANK_INTERLEAVE, XOR_HASH}
```

Estimated area: ~12,000 LUTs. The Nexys A7 bring-up profile.

### Profile C — Multi-Rank DIMM

```
MEMTYPE              = "DDR2"
N_PHASES             = 4
NUM_RANKS            = 4
NUM_BANKS            = 8
PAGE_POLICY          = "HAPPY_HYBRID"
ODT_RULE_MULTIRANK   = "JEDEC_DDR2"
SCHEDULER_MODE       = "OOO"
LOOKAHEAD_DEPTH_MAX  = 4
TXN_QUEUE_DEPTH      = 32
REFRESH_DEFER_MAX    = 8
REFPB_POLICY         = "DARP"           // not used in DDR2; reserved if MEMTYPE switches
```

Estimated area: ~22,000 LUTs (bank machines dominate due to 32 instances). For multi-rank DIMM characterization platforms.

### Profile D — LPDDR2 Single-Rank Mobile

```
MEMTYPE              = "LPDDR2"
N_PHASES             = 4
NUM_RANKS            = 1
NUM_BANKS            = 8
PAGE_POLICY          = "HAPPY_HYBRID"
SCHEDULER_MODE       = "OOO"
REFPB_POLICY         = "DARP"
PAGE_PREDICTOR_TABLE_BITS = 12
POWER_TUNING_DEFAULT  = LPDDR2 with DPD enabled
```

Estimated area: ~13,000 LUTs. Mobile-class designs.

## Synthesis Tool Notes

### Vivado / 7-Series

- `(* ram_style = "block" *)` on the `page_predictor` table → BRAM18
- `(* keep = "TRUE" *)` on `dbg_*` outputs to preserve telemetry through optimization
- `synth_design -directive AreaOptimized_high` for size-constrained builds

### Open-Source Toolchain (Yosys + nextpnr)

- Generic synthesis works for the controller; `page_predictor` table falls into BRAM via Yosys's auto-detect
- For nextpnr-xilinx, the `--no-promote-globals` flag is helpful for the bank-state aggregation buses

## Open Questions / Future Work

- **Hand-curated filelist for ultra-small builds.** When `SCHEDULER_MODE = "INORDER"`, the synthesizer can elide most of the OoO logic; but a curated filelist could exclude the entire FR-FCFS comparator file from the build. Minor area win.
- **Parameter validation script.** A standalone script that takes the parameters and reports the expected utilization could help bring-up. Punt.
- **Configurable assertions for sim vs synth.** Some assertions help in sim but bloat the synthesized netlist. A `BUILD_FOR_SIM` parameter could control. Not in v1.
