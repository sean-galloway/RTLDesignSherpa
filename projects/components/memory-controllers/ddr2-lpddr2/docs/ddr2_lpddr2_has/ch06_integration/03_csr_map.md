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

The APB CSR slave exposes a 4 KB address space (12-bit `paddr`). All registers are 32 bits wide.

## Control and Status (0x000 – 0x00F)

### `CTRL` (0x000, R/W)

| Bit  | Field                      | Reset | Description                                        |
|------|----------------------------|-------|----------------------------------------------------|
| 0    | `init_start`               | 0     | Write 1 to start init                              |
| 1    | `init_force_restart`       | 0     | Write 1 to force re-init even mid-sequence         |
| 4    | `pwr_req_low_power`        | 0     | Request power-down state                           |
| 5    | `pwr_req_dpd`              | 0     | Request DPD (LPDDR2 only)                          |
| 6    | `pwr_req_active`           | 0     | Request return to ACTIVE                           |
| 7    | `pwr_req_self_refresh`     | 0     | Request self-refresh                               |
| 31   | `soft_reset`               | 0     | Write 1 to assert internal soft reset              |

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

Last 8 power-state transitions, 4 bits each. New transitions push the oldest off. Useful for bring-up debugging of power-state oscillation.

## Timing Parameters (0x010 – 0x01F)

Packed timing parameters. Each register holds three to four 8-bit timing values.

### `TIMINGS_RC_RCD_RP` (0x010, R/W)

| Bits  | Field   | Description                  |
|-------|---------|------------------------------|
| 7:0   | `tRC`   | tRC in cycles                |
| 15:8  | `tRCD`  | tRCD in cycles               |
| 23:16 | `tRP`   | tRP in cycles                |
| 31:24 | `tRAS`  | tRAS in cycles               |

### `TIMINGS_RAS_RFC_REFI` (0x014, R/W)

| Bits  | Field         | Description                       |
|-------|---------------|-----------------------------------|
| 15:0  | `tRFC`        | tRFC (or tRFCab) in cycles        |
| 31:16 | `tREFI`       | tREFI in cycles                   |

### `TIMINGS_RRD_FAW_WTR` (0x018, R/W)

| Bits  | Field   | Description           |
|-------|---------|-----------------------|
| 7:0   | `tRRD`  | tRRD                  |
| 15:8  | `tFAW`  | tFAW                  |
| 23:16 | `tWTR`  | tWTR                  |
| 31:24 | `tCCD`  | tCCD                  |

### `TIMINGS_CL_CWL_WR` (0x01C, R/W)

| Bits  | Field          | Description                    |
|-------|----------------|--------------------------------|
| 7:0   | `CL`           | CAS latency                    |
| 15:8  | `CWL`          | CAS write latency              |
| 23:16 | `tWR`          | Write recovery                 |
| 31:24 | `tRFCpb`       | LPDDR2 per-bank tRFC           |

## Mode Register Values (0x020 – 0x02F)

### `MR0`, `MR1`, `MR2`, `MR3` (0x020, 0x024, 0x028, 0x02C, R/W)

Low 16 bits contain the MR value loaded during init. Upper 16 bits reserved.

## LPDDR2-Specific (0x030 – 0x03F)

### `PASR_BANK_MASK_RANK<R>` (0x030 + R×4, R/W; R = 0 .. NUM_RANKS−1)

| Bits  | Field          | Description                                              |
|-------|----------------|----------------------------------------------------------|
| 7:0   | `pasr_banks`   | Per-rank bank mask (MR16); bit N = 1 means bank N is masked off on this rank |

One register per rank. For `NUM_RANKS=1` only `PASR_BANK_MASK_RANK0` (0x030) exists; higher ranks return `pslverr`.

### `PASR_SEG_MASK_RANK<R>` (0x080 + R×4 within the multi-rank reserved area is reused — see register layout note)

For implementation simplicity, segment masks share the rank-indexed pattern: `PASR_SEG_MASK_RANK0` lives at 0x034, and additional ranks consume successive 32-bit slots in the same window. Implementations that ship with `NUM_RANKS > 1` may instead place the additional masks in the per-rank observation window (0x0C0+, see below) — the CSR map vector exposed at `0xFF8` provides discovery.

### `TEMP_DERATE_RANK<R>` (0x038 + R×4, R only)

| Bits | Field         | Description                                             |
|------|---------------|---------------------------------------------------------|
| 1:0  | `temp_class`  | From this rank's MR4: 00 = nominal, 01 = 2x refresh, 10 = 4x refresh |

One register per rank — LPDDR2 ranks can run at different temperatures (e.g., one DRAM near a hot SoC die, another further away), so refresh derating is computed per-rank.

## Scheduler / Refresh / Page Tuning (0x040 – 0x04F)

### `SCHED_TUNING` (0x040, R/W)

| Bits  | Field                       | Description                                                                  |
|-------|-----------------------------|------------------------------------------------------------------------------|
| 3:0   | `lookahead_active`          | Active lookahead window (0..`LOOKAHEAD_DEPTH_MAX`). 0 disables lookahead at runtime, forcing the page-policy fallback. Reset value matches build-time default. |
| 4     | `force_inorder`             | 0 = OoO FR-FCFS scheduling (default). 1 = force first-ready FIFO at runtime; row-hit reordering disabled. For debug, formal verification, or real-time-mode runs. Takes effect at next quiet point. |
| 5     | `happy_enable`              | 0 = HAPPY predictor disabled at runtime (lookup returns "weakly hit-likely" regardless of training). 1 = predictor active. Reset = 1 if `PAGE_POLICY` ∈ `HAPPY_HYBRID` was synthesized; else 0. Useful for A/B'ing predictor contribution without rebuild. |
| 15:8  | `age_max_runtime`           | Runtime override for `AGE_MAX` (clipped to ≤ build-time `AGE_MAX`). 0 = use build-time default. |
| 23:16 | `txn_queue_high_water`      | Backpressure-assertion threshold (≤ build-time `TXN_QUEUE_DEPTH`). |
| 27:24 | `lookahead_max_obs`         | (R only) Echo of build-time `LOOKAHEAD_DEPTH_MAX`. Lets software discover the synthesized ceiling. |

### `PAGE_PRED_TUNING` (0x044, R/W, only when HAPPY enabled)

| Bits  | Field              | Description                              |
|-------|--------------------|------------------------------------------|
| 15:0  | `warmup_cycles`    | Cycles before predictor is trusted       |
| 23:16 | `hysteresis`       | Saturating-counter hysteresis            |

### `REFRESH_TUNING` (0x048, R/W)

| Bits  | Field                       | Description                                                                |
|-------|-----------------------------|----------------------------------------------------------------------------|
| 1:0   | `refpb_policy_or`           | Runtime override: 00 = use build-time; 01 = RR; 10 = OLDEST_FIRST; 11 = DARP. Takes effect at next quiet point. |
| 3:2   | `page_policy_or`            | Runtime override for `PAGE_POLICY`: 00 = build-time default; 01 = force OPEN; 10 = force CLOSE; 11 = force HAPPY_HYBRID (only valid when HAPPY was synthesized). Takes effect at next quiet point. |
| 7:4   | `refresh_defer_active`      | Active refresh deferral count (1..`REFRESH_DEFER_MAX`). 1 = no batching. Larger values batch deferrals up to the synthesized MAX. |
| 31:16 | `zqcs_freq_hz`              | Periodic ZQCS interval in Hz. 0 disables periodic ZQCS (init-only mode). Reset = 1 Hz. |

### `ADDR_MAP_TUNING` (0x04C, R/W)

| Bits | Field             | Description                                                                                       |
|------|-------------------|---------------------------------------------------------------------------------------------------|
| 1:0  | `scheme_or`       | Runtime mux among synthesized schemes: 00 = build-time default; 01 = ROW_MAJOR; 10 = BANK_INTERLEAVE; 11 = XOR_HASH. Only schemes selected for synthesis via `ADDR_MAP_SCHEMES_SYNTH` are switchable; writing an unsynthesized scheme returns `pslverr`. |
| 7:4  | `synth_mask_obs`  | (R only) Bitmask of schemes synthesized: bit 0 = ROW_MAJOR, bit 1 = BANK_INTERLEAVE, bit 2 = XOR_HASH. Lets software discover the available choices. |

### `INIT_TUNING` (0x050, R/W)

| Bits | Field            | Description                                                                          |
|------|------------------|--------------------------------------------------------------------------------------|
| 3:0  | `zq_retries`     | ZQ calibration retry count before raising `init_error`. Reset = 3. Range 1–8.       |
| 15:8 | `init_timeout_ms`| Per-step init timeout in ms (scaled by `SIM_INIT_SCALE` in sim). Reset = 10. Range 1–255. |

All runtime overrides take effect at the next configuration quiet point (no DRAM commands in flight, no refresh sequence in progress). The CSR slave does not enforce quiet points; the SoC may force a brief drain by strobing `CTRL.config_apply`.

## Per-(Rank, Bank) Observation (0x080 – 0x0FF)

For each (rank R, bank N) pair within `NUM_RANKS × NUM_BANKS`, two registers. The address layout interleaves bank-first within rank-block; the per-rank stride is `NUM_BANKS × 4` (32 bytes for 8-bank parts).

### `OBS_ROW_HIT_RANK<R>_BANK<N>` (0x080 + (R × NUM_BANKS + N) × 4, R only)

Rolling row-hit count, rank R bank N. Resets when read or on `soft_reset`. For `NUM_RANKS=1` this collapses to the single-rank `OBS_ROW_HIT_BANK<N>` layout at 0x080–0x09C.

### `OBS_REF_LATENCY_RANK<R>_BANK<N>` (0x0C0 + (R × NUM_BANKS + N) × 4, R only)

Average refresh blocking time for rank R bank N. Per-rank tracking matters because per-rank PASR masks, temperature derating, and DARP scheduling can produce different refresh-blocking profiles across ranks even on the same DIMM.

## System Observation (0x100 – 0x1FF)

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

## Module Identification (0xFF0 – 0xFFC)

### `ID` (0xFF0, R only)

| Bits  | Field        | Description                            |
|-------|--------------|----------------------------------------|
| 7:0   | `version`    | Build version                          |
| 15:8  | `memtype`    | 0 = DDR2, 1 = LPDDR2                   |
| 23:16 | `n_phases`   | Gear ratio (1, 2, or 4)                |
| 31:24 | `module_id`  | 0xD2 (fixed)                           |

### `BUILD` (0xFF4, R only)

Build hash / version word; lowered to upper bits at synthesis.
