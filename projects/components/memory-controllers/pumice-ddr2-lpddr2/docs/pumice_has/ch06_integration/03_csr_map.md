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

# CSR Register Map

The controller's configuration and observation registers are defined in
`rtl/macro/pumice_csr.rdl` and generated with PeakRDL into a passthrough-cpuif
register block (`bin/peakrdl_generate.py`). The DV mirror is
`dv/tbclasses/pumice_regmap.py`; software addresses every field **by name**
through that generated map — hardcoded offsets are forbidden. This chapter is
the authoritative narrative for that RDL; every register, offset, and reset
value below is reconciled against it.

The map occupies a 4 KB space (12-bit address, `CSR_ADDR_W = 12`). All
registers are 32 bits wide, little-endian, 4-byte aligned. The register bus is
the PeakRDL **passthrough cpuif** (`s_cpuif_*`), not a hand-written APB slave —
see §4.3. Config fields are consumed `hw = r` (`hwif_out.*`) and drive the core
by name; status/observation fields are `hw = w` (`hwif_in.*`).

## Control and Status (0x000 – 0x00F)

### `CTRL` (0x000, R/W)

| Bit  | Field                      | Reset | Description                                        |
|------|----------------------------|-------|----------------------------------------------------|
| 0    | `init_start`               | 0     | Write 1 to start init (self-modifying strobe)      |
| 1    | `init_force_restart`       | 0     | Write 1 to force re-init even mid-sequence         |
| 3:2  | `RSVD_3_2`                 | 0     | Reserved                                           |
| 4    | `pwr_req_low_power`        | 0     | Request power-down state                           |
| 5    | `pwr_req_dpd`              | 0     | Request DPD (LPDDR2 only)                          |
| 6    | `pwr_req_active`           | 0     | Request return to ACTIVE                           |
| 7    | `pwr_req_self_refresh`     | 0     | Request self-refresh                               |
| 30:8 | `RSVD_30_8`                | 0     | Reserved                                           |
| 31   | `soft_reset`               | 0     | Write 1 to assert internal soft reset (self-clearing) |

### `STATUS` (0x004, R only)

| Bit   | Field             | Description                                            |
|-------|-------------------|--------------------------------------------------------|
| 0     | `init_done`       | 1 when init complete                                   |
| 1     | `init_error`      | 1 on init failure                                      |
| 7:4   | `power_state`     | Current power-state FSM state (encoded)                |
| 8     | `pasr_active`     | LPDDR2: PASR mask is non-zero                          |
| 23:16 | `init_step_dbg`   | Current init step number (for bring-up)                |
| 31    | `version_match`   | 1 when build matches expected version                  |

### `STATUS_HISTORY` (0x008, R only)

Last 8 power-state transitions, 4 bits each. Most recent in `[3:0]`; new
transitions push the oldest off. Useful for bring-up debugging of power-state
oscillation.

## Timing Parameters (0x010 – 0x01F)

Packed timing parameters in MC (`aclk`) cycles. All fields are `sw = rw`,
`hw = r` and drive the core scheduler / DFI layer.

### `TIMINGS_RC_RCD_RP_RAS` (0x010, R/W)

| Bits  | Field   | Reset | Description                  |
|-------|---------|-------|------------------------------|
| 7:0   | `tRC`   | 60    | tRC in cycles                |
| 15:8  | `tRCD`  | 15    | tRCD in cycles               |
| 23:16 | `tRP`   | 15    | tRP in cycles                |
| 31:24 | `tRAS`  | 40    | tRAS in cycles               |

### `TIMINGS_RFC_REFI` (0x014, R/W)

| Bits  | Field         | Reset | Description                       |
|-------|---------------|-------|-----------------------------------|
| 15:0  | `tRFC`        | 200   | tRFC (or tRFCab) in cycles        |
| 31:16 | `tREFI`       | 1950  | tREFI in cycles                   |

### `TIMINGS_RRD_FAW_WTR_CCD` (0x018, R/W)

| Bits  | Field   | Reset | Description           |
|-------|---------|-------|-----------------------|
| 7:0   | `tRRD`  | 6     | tRRD                  |
| 15:8  | `tFAW`  | 35    | tFAW                  |
| 23:16 | `tWTR`  | 4     | tWTR                  |
| 31:24 | `tCCD`  | 4     | tCCD                  |

### `TIMINGS_CL_CWL_WR` (0x01C, R/W)

| Bits  | Field          | Reset | Description                    |
|-------|----------------|-------|--------------------------------|
| 7:0   | `CL`           | 6     | CAS latency                    |
| 15:8  | `CWL`          | 4     | CAS write latency              |
| 23:16 | `tWR`          | 15    | Write recovery                 |
| 31:24 | `tRFCpb`       | 70    | LPDDR2 per-bank tRFC           |

## Mode Register Values (0x020 – 0x02F)

### `MR0`, `MR1`, `MR2`, `MR3` (0x020, 0x024, 0x028, 0x02C, R/W)

Low 16 bits (`VAL`) contain the MR value; upper 16 bits reserved. These hold
override MR values; the default init walk uses the JEDEC-standard values built
into `init_sequencer.sv` (§6.2). Reset = 0.

## LPDDR2-Specific (0x030 – 0x03F)

### `PASR_BANK_MASK_RANK0` (0x030, R/W)

| Bits | Field         | Reset | Description                                                       |
|------|---------------|-------|-------------------------------------------------------------------|
| 7:0  | `pasr_banks`  | 0     | LPDDR2 PASR per-bank mask for rank 0 (MR16); bit N = 1 masks bank N |

### `PASR_SEG_MASK_RANK0` (0x034, R/W)

| Bits | Field        | Reset | Description                          |
|------|--------------|-------|--------------------------------------|
| 7:0  | `pasr_segs`  | 0     | LPDDR2 PASR segment mask for rank 0  |

### `TEMP_DERATE_RANK0` (0x038, R only)

| Bits | Field         | Description                                             |
|------|---------------|---------------------------------------------------------|
| 1:0  | `temp_class`  | From rank 0's MR4: 00 = nominal, 01 = 2x refresh, 10 = 4x refresh |

The current RDL defines the single-rank instances only (`NUM_BANKS = 8`,
rank 0). Multi-rank builds would extend this block; the map as generated today
does not allocate per-rank PASR/temperature registers beyond rank 0.

## Scheduler / Refresh / Page / Addr / Init Tuning (0x040 – 0x05F)

### `SCHED_TUNING` (0x040, R/W)

| Bits  | Field                       | Reset | Description                                                                  |
|-------|-----------------------------|-------|------------------------------------------------------------------------------|
| 3:0   | `lookahead_active`          | 0     | Active lookahead window (0..`LOOKAHEAD_DEPTH_MAX`). 0 disables lookahead.     |
| 4     | `force_inorder`             | 0     | 1 = force first-ready FIFO (disable row-hit reordering).                      |
| 5     | `happy_enable`              | 1     | 1 = HAPPY predictor active (only meaningful if synthesized).                  |
| 15:8  | `age_max_runtime`           | 0     | Runtime `AGE_MAX` override (0 = use build-time default).                      |
| 23:16 | `txn_queue_high_water`      | 0     | Backpressure-assertion threshold for the txn queue.                          |
| 27:24 | `lookahead_max_obs`         | —     | (R only, `hw = w`) Echo of build-time `LOOKAHEAD_DEPTH_MAX`.                  |

### `PAGE_PRED_TUNING` (0x044, R/W)

| Bits  | Field              | Reset | Description                              |
|-------|--------------------|-------|------------------------------------------|
| 15:0  | `warmup_cycles`    | 1024  | Warmup cycles before predictor is trusted |
| 23:16 | `hysteresis`       | 2     | Saturating-counter hysteresis            |

### `REFRESH_TUNING` (0x048, R/W)

| Bits  | Field                       | Reset | Description                                                                |
|-------|-----------------------------|-------|----------------------------------------------------------------------------|
| 1:0   | `refpb_policy_or`           | 0     | 00 = build-time; 01 = RR; 10 = OLDEST_FIRST; 11 = DARP.                    |
| 3:2   | `page_policy_or`            | 0     | 00 = build-time; 01 = OPEN; 10 = CLOSE; 11 = HAPPY_HYBRID.                 |
| 7:4   | `refresh_defer_active`      | 1     | Active refresh deferral count (1..`REFRESH_DEFER_MAX`). 1 = no batching.   |
| 31:16 | `zqcs_freq_hz`              | 1     | Periodic ZQCS interval in Hz. 0 disables periodic ZQCS.                    |

### `ADDR_MAP` (0x04C, R/W)

Replaces the retired `ADDR_MAP_TUNING` register. The AXI-to-DRAM mapping is
driven by a single knob rather than a scheme selector — see §5.4 and §3.1, and
`rtl/fub/addr_mapper.sv`.

| Bits  | Field        | Reset | Description                                                                       |
|-------|--------------|-------|-----------------------------------------------------------------------------------|
| 4:0   | `bank_lsb`   | 0x0A  | Bank-field LSB in the word address. Default 10 = `COL_WIDTH` = ROW_MAJOR placement. RTL clamps to `[0, COL_WIDTH]`. |
| 8     | `hash_en`    | 0     | Enable bank XOR-hash: `bank ^= fold(row) ^ hash_seed`.                             |
| 23:16 | `hash_seed`  | 0     | XOR-hash seed (`seed[BW-1:0]`).                                                    |

The register reset value is `0x0000000A` (`bank_lsb = 10`, hash off). Setting
`bank_lsb = COL_WIDTH` gives ROW_MAJOR; `bank_lsb = log2(cols/burst)` gives
maximum bank interleave with burst locality preserved; `hash_en` folds an
XOR-hash on top of any placement (the old XOR_HASH scheme). There is no separate
scheme-selector field.

### `INIT_TUNING` (0x050, R/W)

| Bits | Field            | Reset | Description                                                                          |
|------|------------------|-------|--------------------------------------------------------------------------------------|
| 3:0  | `zq_retries`     | 3     | ZQ calibration retry count before raising `init_error`. Range 1–8.                  |
| 15:8 | `init_timeout_ms`| 10    | Per-step init timeout in ms. Range 1–255.                                            |

### `INIT_TIMING0` (0x058, R/W)

JEDEC init-sequence waits (MC cycles), consumed by `init_sequencer.sv`.
Previously hardcoded.

| Bits  | Field         | Reset | Description               |
|-------|---------------|-------|---------------------------|
| 15:0  | `t_init_wait` | 512   | CKE / tINIT settle        |
| 31:16 | `t_dll_wait`  | 256   | DLL lock (tDLLK)          |

### `INIT_TIMING1` (0x05C, R/W)

| Bits  | Field        | Reset | Description               |
|-------|--------------|-------|---------------------------|
| 7:0   | `t_mrd_wait` | 8     | tMRD (post mode-reg)      |
| 15:8  | `t_rp_wait`  | 8     | tRP (post precharge)      |
| 23:16 | `t_rfc_wait` | 16    | tRFC (post refresh)       |

### `TIMINGS_RTP_RTW` (0x054, R/W)

Read-to-precharge and read-to-write turn-around. Previously `tRTP` was hardcoded
(8'd4) and `tRTW` was tied to it; both are now independent configs.

| Bits  | Field   | Reset | Description         |
|-------|---------|-------|---------------------|
| 7:0   | `tRTP`  | 4     | Read to precharge   |
| 15:8  | `tRTW`  | 6     | Read to write       |

## DFI / PHY Timing (0x060 – 0x067)

### `DFI_PHASE` (0x060, R/W)

Which DFI sub-phase carries the READ vs WRITE command, to match the PHY's
`rdphase` / `wrphase` contract (see §4.2). Fields are sliced to
`clog2(DFI_RATE)` bits downstream; upper bits are ignored when
`DFI_RATE` is narrower than the field. Defaults 0/0 preserve the
legacy all-on-phase-0 behavior.

| Bits | Field      | Reset | Description                    |
|------|------------|-------|--------------------------------|
| 2:0  | `rd_phase` | 0     | READ command DFI sub-phase     |
| 6:4  | `wr_phase` | 0     | WRITE command DFI sub-phase    |

### `PHY_TIMING` (0x064, R/W)

PHY / DFI data timing plus memory-type selection. All fields `hw = r` so they
drive the controller core.

| Bits  | Field           | Reset | Description                                                    |
|-------|-----------------|-------|----------------------------------------------------------------|
| 7:0   | `t_phy_wrlat`   | 0     | WRITE command -> `dfi_wrdata_en` (0 for a7ddrphy pre-pull)     |
| 15:8  | `t_rddata_en`   | 6     | RD command -> `dfi_rddata_en` window                          |
| 16    | `memtype`       | 0     | 0 = DDR2, 1 = LPDDR2 (drives the whole core `memtype_e` path)  |
| 23:20 | `refresh_burst` | 1     | REFs drained per request (1..8)                               |

`PHY_TIMING.memtype` is the runtime memory-type select. It is decoded into the
`memtype_e` enum at the top and fanned out to the addr/scheduler/DFI/init logic;
geometry (DFI_RATE, DRAM_BEAT_WIDTH, NUM_BANKS, ROW/COL width, BL) remains
build-time — see §5.1.

## Per-Bank Observation (0x080 – 0x0DF)

Single-rank (rank 0), `NUM_BANKS = 8`. Each is a `regfile` of 8 word-wide
registers striding by 4 bytes.

### `OBS_ROW_HIT[0..7]` (0x080 + N×4, R/W with clear-on-read)

Rolling row-hit count per bank. `VAL[31:0]`, `onread = rclr` (reset on read or
`soft_reset`).

### `OBS_REF_LATENCY[0..7]` (0x0C0 + N×4, R only)

Average refresh-blocking cycles per bank. `VAL[31:0]`, `hw = w`.

## System Observation (0x100 – 0x1FF)

All `hw = w`, `sw = r`.

| Offset | Register                     | Description                                  |
|--------|------------------------------|----------------------------------------------|
| 0x100  | `OBS_TXN_QUEUE_DEPTH_MAX`    | Max queue depth observed                     |
| 0x104  | `OBS_TXN_QUEUE_DEPTH_AVG`    | Time-averaged depth                          |
| 0x108  | `OBS_REFRESH_PENDING_MAX`    | Max `refresh_pending` value observed         |
| 0x10C  | `OBS_REFRESH_DEFER_HIST_0`   | Refresh deferral histogram bin 0             |
| 0x110  | `OBS_REFRESH_DEFER_HIST_1`   | Histogram bin 1                              |
| 0x114  | `OBS_REFRESH_DEFER_HIST_2`   | Histogram bin 2                              |
| 0x118  | `OBS_REFRESH_DEFER_HIST_3`   | Histogram bin 3                              |
| 0x120  | `OBS_PAGE_PRED_ACCURACY`     | HAPPY mode: rolling prediction accuracy (%)  |
| 0x130  | `OBS_AXI_R_LATENCY_AVG`      | Avg AXI read latency in cycles               |
| 0x134  | `OBS_AXI_R_LATENCY_P99`      | 99th-percentile read latency                 |
| 0x138  | `OBS_AXI_W_LATENCY_AVG`      | Avg AXI write latency                        |

### `OBS_WORDS[0..8]` (0x1C0 + N×4, R only)

Nine 32-bit read-only words carrying the packed `obs_*` signal harvest from the
FUB internals (see `docs/csr_obs_layout.md`). `VAL[31:0]`, `hw = w`.

## Module Identification (0xFF0 – 0xFFC)

### `ID` (0xFF0, R only, reset = 0xD2020001)

| Bits  | Field        | Reset | Description                            |
|-------|--------------|-------|----------------------------------------|
| 7:0   | `version`    | 0x01  | Build version                          |
| 15:8  | `memtype`    | 0x00  | 0 = DDR2, 1 = LPDDR2                   |
| 23:16 | `n_phases`   | 0x02  | Gear ratio (1, 2, or 4)                |
| 31:24 | `module_id`  | 0xD2  | Fixed 0xD2                             |

### `BUILD` (0xFF4, R only)

Build hash word. `VAL[31:0]`, reset = 0.

## Notes on This Revision

- `ADDR_MAP_TUNING` (with `scheme_or` / `synth_mask_obs`) has been **retired**
  and replaced by `ADDR_MAP` at 0x04C. No scheme-selector field exists in RTL.
- `TIMINGS_RTP_RTW` (0x054), `INIT_TIMING0` (0x058), `INIT_TIMING1` (0x05C),
  `DFI_PHASE` (0x060), and `PHY_TIMING` (0x064) expose knobs that were formerly
  hardcoded in the FUBs; they are now runtime CSRs.
- `PHY_TIMING.memtype` and `PHY_TIMING.refresh_burst` are new runtime fields.
- The observation block is single-rank as generated; the multi-rank per-rank
  layout described in earlier revisions is not present in the current RDL.
