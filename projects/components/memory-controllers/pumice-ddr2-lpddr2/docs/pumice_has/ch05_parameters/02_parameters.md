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

# Top-Level Parameter Table

All build-time parameters for the controller, with type, default, valid range, the section that governs their use, and a one-line purpose summary.

## Parameter Table

The parameters below are the actual elaboration parameters of `pumice_top` / `pumice_core` (with the host-width parameter added by `pumice_top_geared`). Several knobs that earlier revisions listed as build-time — `MEMTYPE`, `WRPHASE`, `RDPHASE`, and the address-map scheme set — are runtime CSR fields in this generation and are called out under "Runtime CSR knobs (not build parameters)" below.

| Parameter             | Type | Default | Range / valid set        | Section | Purpose                                                                 |
|-----------------------|------|---------|--------------------------|---------|-------------------------------------------------------------------------|
| `AXI_ID_WIDTH`        | int  | 8       | 1-16                     | §3.1    | AXI ID tag width (`IW`).                                                 |
| `AXI_ADDR_WIDTH`      | int  | 32      | 24-40                    | §3.1    | AXI flat address width (`AW`).                                          |
| `NUM_RANKS`           | int  | 1       | `{1, 2, 4}`              | §3.3    | Number of physical ranks (per-rank `CS_n`, `CKE`, `ODT`). 1 = single-rank point-to-point; 2 / 4 = DIMM-class. Rank bits stack at the top of the address map (§3.1) and refresh state is tracked per (rank, bank). |
| `NUM_BANKS`           | int  | 8       | `{4, 8}`                 | §3.3    | Per-device bank count (per rank). Sets the bank-machine / lookup count. |
| `ROW_WIDTH`           | int  | 14      | 12-16                    | §3.3    | Row-address width.                                                      |
| `COL_WIDTH`           | int  | 10      | 9-12                     | §3.3    | Column-address width. Also the `ROW_MAJOR` setting of `ADDR_MAP.bank_lsb`. |
| `DFI_RATE`            | int  | 2       | `{1, 2, 4}`              | §3.6    | DFI frequency-ratio gear (phase count). Drives all DFI bus widths and the internal data-unit width. This is the gear parameter formerly called `N_PHASES`. |
| `DRAM_BEAT_WIDTH`     | int  | 64      | `{16, 32, 64}`           | §3.6    | Width of one DRAM data beat (per DFI phase).                            |
| `BL`                  | int  | 8       | `{4, 8}`                 | §3.6    | DRAM burst length in beats. The AXI intake splits host bursts into fixed-`BL` commands; one AXI burst at the core (`DW`) side is `(awlen+1)*DFI_RATE == BL`. |
| `NUM_ENTRIES`         | int  | 8       | 4-32 (power of 2)        | §3.2    | Depth of the read/write command CAMs (in-flight transaction slots). Pointer width is `clog2(NUM_ENTRIES)`. |
| `N_SRAM_SLOTS`        | int  | 8       | 4-32 (power of 2)        | §3.2    | Write-data SRAM slot count (buffered write payloads awaiting commit).   |
| `BYTE_OFFSET_WIDTH`   | int  | 3       | `clog2(beat byte size)`  | §3.1    | Low byte-offset bits stripped before address decode (`log2` of beat byte size). |
| `AGE_WIDTH`           | int  | 16      | 8-24                     | §3.2    | Width of the per-transaction age counter used for FR-FCFS anti-starvation tie-breaking. |
| `HOST_AXI_DATA_WIDTH` | int  | 128     | `{64, 128, 256}` (verified) | §3.1 | **`pumice_top_geared` only.** Free host-side AXI data width. Formally-verified `axi4_dwidth_converter_wr/_rd` shims bridge the host width to the fixed core width `DW`. `HOST_AXI_DATA_WIDTH == DW` is a generate-bypassed, bit-identical direct connection (no converter, no added latency). |

**Derived parameters** (computed at elaboration, not overridable independently):

- `DW = DRAM_BEAT_WIDTH * DFI_RATE` — the fixed core AXI data width **and** the DFI word width (default `64 * 2 = 128`). `DFI_DATA_WIDTH = DW`. One core AXI beat == one DFI word == `DFI_RATE` DRAM beats.
- `SW = DW / 8` — core AXI / DFI strobe width.
- `PHW = clog2(DFI_RATE)` (min 1) — DFI sub-phase index width.
- `DFI_STRB_WIDTH = DW/8`, `DFI_EN_WIDTH = DFI_VALID_WIDTH = DFI_RATE`, `DFI_ADDR_BUS_W = ROW_WIDTH*DFI_RATE`, `DFI_BANK_BUS_W = clog2(NUM_BANKS)*DFI_RATE`, `DFI_CS_BUS_W = NUM_RANKS*DFI_RATE` — the DFI 2.1 pin-bus widths, all scaled by `DFI_RATE`.

**Runtime CSR knobs (not build parameters):**

These select behavior at runtime and have no build-time parameter in this generation. Full field detail is in §6.3.

- `PHY_TIMING.memtype` (1-bit) — `0 = DDR2`, `1 = LPDDR2`. The core decodes `memtype_e` from this field (`pumice_top.sv` `w_memtype`); there is no build-time `MEMTYPE` string.
- `DFI_PHASE.wr_phase` / `DFI_PHASE.rd_phase` (3-bit each, sliced to `PHW` downstream) — which DFI sub-phase carries the WRITE / READ command. Defaults 0/0. These replace the former build-time `WRPHASE` / `RDPHASE`.
- `ADDR_MAP.bank_lsb` (5-bit, reset `0x0A` = `COL_WIDTH` = ROW_MAJOR), `ADDR_MAP.hash_en` (1-bit), `ADDR_MAP.hash_seed` (8-bit) — the single address-map placement knob (+ optional bank XOR-hash). The classic ROW_MAJOR / BANK_INTERLEAVE / XOR_HASH "schemes" are just settings of these fields; there is no `ADDR_MAP_SCHEMES_SYNTH` / `ADDR_MAP_SCHEME_DEFAULT` build parameter and no scheme mux. See `addr_mapper.sv`.
- `REFRESH_TUNING.page_policy_or` (2-bit) — `00 = build-time default`, `01 = OPEN`, `10 = CLOSE`, `11 = HAPPY_HYBRID`.
- `REFRESH_TUNING.refpb_policy_or` (2-bit), `REFRESH_TUNING.refresh_defer_active` (4-bit), `REFRESH_TUNING.zqcs_freq_hz` (16-bit, reset 1 Hz).
- `SCHED_TUNING.lookahead_active` (4-bit), `force_inorder` (1-bit), `happy_enable` (1-bit, reset 1), `age_max_runtime` (8-bit), `txn_queue_high_water` (8-bit); `lookahead_max_obs` (4-bit, RO echo of the build MAX).
- `PAGE_PRED_TUNING.warmup_cycles` (16-bit, reset 1024), `hysteresis` (8-bit, reset 2).
- Timing CSRs — `TIMINGS_RC_RCD_RP_RAS` (tRC/tRCD/tRP/tRAS), `TIMINGS_RFC_REFI` (tRFC/tREFI), `TIMINGS_RRD_FAW_WTR_CCD` (tRRD/tFAW/tWTR/tCCD), `TIMINGS_CL_CWL_WR` (CL/CWL/tWR/tRFCpb), `TIMINGS_RTP_RTW` (tRTP/tRTW).
- `PHY_TIMING.refresh_burst` (4-bit, 1..8), `PHY_TIMING.t_phy_wrlat` (8-bit), `PHY_TIMING.t_rddata_en` (8-bit).
- Init timings — `INIT_TIMING0` (t_init_wait/t_dll_wait), `INIT_TIMING1` (t_mrd_wait/t_rp_wait/t_rfc_wait), `INIT_TUNING.zq_retries` (4-bit, reset 3), `INIT_TUNING.init_timeout_ms` (8-bit, reset 10).

These cost zero silicon area beyond the register flops; making them build-time parameters would have been wrong (and was, in earlier revisions of this document).

## Memtype-Dependent Constraints

`MEMTYPE` is a runtime CSR field (`PHY_TIMING.memtype`) rather than an elaboration parameter, so the DDR2-vs-LPDDR2 selection does not gate elaboration-time asserts. The memtype-dependent behavior is instead enforced at run time within the synthesized datapath:

- `PHY_TIMING.memtype == 1` (LPDDR2) enables the LPDDR2-only features (PASR bank/segment masks, DPD request, temperature-derate readback, per-bank tRFC via `TIMINGS_CL_CWL_WR.tRFCpb`).
- `PHY_TIMING.memtype == 0` (DDR2) uses the DDR2 command encoding and all-bank refresh.
- The DFI address bus is `ROW_WIDTH * DFI_RATE` wide (`DFI_ADDR_BUS_W`) and carries the LPDDR2 CA packing when `memtype == 1`; it must be wide enough for whichever memtype is programmed, which is guaranteed by `ROW_WIDTH >= 14`.

## Timing-Configuration Sanity Checks

The controller expects the following relationships to hold on the loaded timing CSR values. Because timings are runtime CSRs, these are boot-time programming contracts the SoC firmware must honor (they are documented here so the sweep tool and bring-up scripts can assert them):

- `tREFI_cycles >= 100` — the MC clock must be fast enough relative to tREFI that the refresh timer is well-resolved.
- `tRCD_cycles >= 2`, `tRP_cycles >= 2`, `tRC_cycles >= tRAS + tRP` — basic JEDEC consistency checks.
- `tRFC_cycles > tRP_cycles` — the refresh-cycle time must exceed the precharge time.

These are configuration bugs that should be caught at boot time before traffic starts, not preventable run-time faults.

## Parameter Categories

| Category         | Parameters                                                                                          |
|------------------|-----------------------------------------------------------------------------------------------------|
| Geometry         | `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`, `COL_WIDTH`                                                  |
| Multi-rank       | `NUM_RANKS`                                                                                         |
| Bus widths       | `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `DRAM_BEAT_WIDTH`, `BYTE_OFFSET_WIDTH`, `HOST_AXI_DATA_WIDTH`; derived `DW`/`DFI_DATA_WIDTH` |
| Gear / DFI       | `DFI_RATE`, `BL` (with runtime `DFI_PHASE.rd_phase` / `DFI_PHASE.wr_phase`)                         |
| Capacity         | `NUM_ENTRIES`, `N_SRAM_SLOTS`, `AGE_WIDTH`                                                          |
| Characterization | Runtime CSR knobs paired with the geometry above — `SCHED_TUNING.lookahead_active`, `REFRESH_TUNING.page_policy_or` / `refpb_policy_or` / `refresh_defer_active`, `PAGE_PRED_TUNING.*`, `ADDR_MAP.bank_lsb` / `hash_en` (see §5.3 and §6.3) |
