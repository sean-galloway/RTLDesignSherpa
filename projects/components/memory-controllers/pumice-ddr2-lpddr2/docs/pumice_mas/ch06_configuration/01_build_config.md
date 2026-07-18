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

> Per HAS §5.2 for the parameter table and §5.1 for the build-vs-runtime philosophy. This chapter is the **build-script-author's** view: the synthesis-time parameters and how the data-width geometry works. Most behavior is runtime CSR-driven (see §4/§5), so the build parameter set is deliberately small — mostly memory geometry.

---

## Parameters

The synthesis-time parameters are the ports of `pumice_top` (`rtl/top/pumice_top.sv`). They are geometry, not policy — memtype / timings / page policy / address map are all runtime CSR fields.

```systemverilog
pumice_top #(
    .AXI_ID_WIDTH    (8),
    .AXI_ADDR_WIDTH  (32),
    .NUM_RANKS       (1),      // board build is single-rank
    .NUM_BANKS       (8),
    .ROW_WIDTH       (14),
    .COL_WIDTH       (10),
    .DFI_RATE        (2),      // DFI phases per MC clock (gear ratio)
    .DRAM_BEAT_WIDTH (64),     // bits per DRAM beat (device data bus)
    .BL              (8),      // DRAM burst length
    .NUM_ENTRIES     (8),      // CAM depth
    .N_SRAM_SLOTS    (8)
    // DW is DERIVED: DW = DRAM_BEAT_WIDTH * DFI_RATE
) u_pumice ( ... );
```

There is **no** `MEMTYPE`, `PAGE_POLICY`, `SCHEDULER_MODE`, `ODT_RULE_*`, `ADDR_MAP_SCHEMES_SYNTH`, or `DFI_ADDR_WIDTH` parameter — those are runtime CSR fields or derived from geometry. `memtype` is `PHY_TIMING.memtype`; page policy is `REFRESH_TUNING.page_policy_or`; address mapping is `ADDR_MAP.bank_lsb`.

## Data-Width Geometry (DW = DRAM_BEAT_WIDTH x DFI_RATE)

The controller's internal / AXI-facing data width is **derived**, not a free parameter:

```
DW = DRAM_BEAT_WIDTH * DFI_RATE          // e.g. 64 * 2 = 128 (default)
```

- **One AXI beat == one DFI word == DFI_RATE DRAM beats.**
- **One AXI burst (BL / DFI_RATE beats) == one DRAM burst (BL beats).**
- The DW -> per-phase split happens in `dfi_signal_pack` / the DFI layer (`DFI_DATA_WIDTH = DW`, `DFI_EN_WIDTH = DFI_RATE`).

The old "AXI_DATA_WIDTH == DRAM_BEAT_WIDTH" coupling is **gone** — do not describe it. The host AXI data width the core presents is exactly `DW`.

### Host-Width Freedom (`pumice_top_geared`)

To let a host SoC use a convenient fixed AXI width regardless of the DRAM point, wrap `pumice_top` in `pumice_top_geared` (`rtl/top/pumice_top_geared.sv`), which adds a free `HOST_AXI_DATA_WIDTH` parameter:

- It inserts the repo's **formally-verified** `axi4_dwidth_converter_wr` / `_rd` between a host-width AXI slave and the fixed-`DW` core.
- `HOST_AXI_DATA_WIDTH == DW` is a **generate bypass** — bit-identical to bare `pumice_top`, no converter, no added latency.
- Verified host widths: 64, 128, 256.
- Burst geometry contract is unchanged at the core's DW side; the converter re-sizes host bursts to DW-width bursts.

Doc: `docs/AXI_DRAM_GEARING_SCOPE.md`.

## Parameter Sanity

The natural elaboration-time constraints:

```systemverilog
generate
    if (NUM_RANKS != 1 && NUM_RANKS != 2 && NUM_RANKS != 4)
        $error("NUM_RANKS must be 1, 2, or 4");
    if (NUM_BANKS != 4 && NUM_BANKS != 8)
        $error("NUM_BANKS must be 4 or 8");
    if (DFI_RATE != 1 && DFI_RATE != 2 && DFI_RATE != 4)
        $error("DFI_RATE must be 1, 2, or 4 (gear ratio)");
    // BL must be an integer multiple of DFI_RATE so a DRAM burst is a whole
    // number of AXI beats.
endgenerate
```

`DFI_RATE` must equal the attached PHY's phase count (e.g., the on-board 300 MT/s point is `DFI_RATE = 4` at sys = 37.5 MHz / CK = 150 MHz; regenerating for a different phase count alone produces a broken hybrid — see project notes).

## Filelists

FUB filelists live in `rtl/filelists/`. The live module hierarchy (top -> core -> `pumice_axi4_ifc` / `pumice_mem_cmd_scheduler` / `pumice_dfi_layer`) is fixed; the DDR2 vs LPDDR2 command paths coexist in `dfi_cmd_formatter` and branch on `memtype`, so a single build supports both families with dead-code elimination handling the unused branch. `page_predictor.sv` / `powerdown_ctrl.sv` are optional/not in the default top build (confirm via the filelists).

## Open Questions / Future Work

- **Multi-rank build.** `NUM_RANKS > 1` requires the per-rank register generation and per-rank init iteration described in §4.2 / §5.3.
- **Curated small-area filelist.** Excluding the optional predictor/power-down FUBs shrinks the smallest build.
- **Geared-top width matrix.** Extending the verified `HOST_AXI_DATA_WIDTH` set beyond {64,128,256} as needed.
