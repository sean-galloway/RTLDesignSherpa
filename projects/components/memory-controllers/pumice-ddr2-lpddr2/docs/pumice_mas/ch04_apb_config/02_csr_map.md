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

# Register Map

> This MAS chapter is the **authoritative field-level register map**, transcribed directly from `rtl/macro/pumice_csr.rdl` and mirrored by the generated `dv/tbclasses/pumice_regmap.py`. If this table and the RDL ever disagree, the RDL wins. Offsets are byte addresses in the 4 KB (12-bit) region.

---

## Source of Truth

The register map is a SystemRDL source, `rtl/macro/pumice_csr.rdl`. It is compiled by `bin/peakrdl_generate.py` into:

| Artifact                                | Consumer                                                        |
|-----------------------------------------|-----------------------------------------------------------------|
| `regs/generated/rtl/pumice_csr.sv` + `pumice_csr_pkg.sv` | The PeakRDL passthrough register block instantiated in `pumice_top` (`hwif_in`/`hwif_out` structs) |
| `dv/tbclasses/pumice_regmap.py`         | The DV `RegisterMap` by-name access model (offset/field/default) |

`pumice_top` drives `hwif_out.*` fields **by name** straight into `pumice_core` — there is no hand-written register file and no APB slave inside the controller (see §4.1). DV programs every register by name via `pumice_regmap.py`; hardcoded offsets are forbidden.

## Register Summary

| Offset | Register                  | Purpose                                                   |
|--------|---------------------------|-----------------------------------------------------------|
| 0x000  | `CTRL`                    | Init / power / soft-reset request bits                    |
| 0x004  | `STATUS`                  | Init / power / version status (RO, hw-written)            |
| 0x008  | `STATUS_HISTORY`          | Last 8 power-state transitions (RO)                       |
| 0x010  | `TIMINGS_RC_RCD_RP_RAS`   | tRC / tRCD / tRP / tRAS                                    |
| 0x014  | `TIMINGS_RFC_REFI`        | tRFC / tREFI                                              |
| 0x018  | `TIMINGS_RRD_FAW_WTR_CCD` | tRRD / tFAW / tWTR / tCCD                                  |
| 0x01C  | `TIMINGS_CL_CWL_WR`       | CL / CWL / tWR / tRFCpb                                    |
| 0x020  | `MR0`                     | Mode Register 0 value                                     |
| 0x024  | `MR1`                     | Mode Register 1 value                                     |
| 0x028  | `MR2`                     | Mode Register 2 value                                     |
| 0x02C  | `MR3`                     | Mode Register 3 value                                     |
| 0x030  | `PASR_BANK_MASK_RANK0`    | LPDDR2 PASR per-bank mask (rank 0)                        |
| 0x034  | `PASR_SEG_MASK_RANK0`     | LPDDR2 PASR segment mask (rank 0)                         |
| 0x038  | `TEMP_DERATE_RANK0`       | LPDDR2 MR4 temperature class (rank 0, RO)                 |
| 0x040  | `SCHED_TUNING`            | Scheduler runtime knobs                                    |
| 0x044  | (unmapped)                | was `PAGE_PRED_TUNING` — retired with the HAPPY predictor |
| 0x048  | `REFRESH_TUNING`          | Refresh policy + page-policy override + ZQCS interval     |
| 0x04C  | `ADDR_MAP`                | Address-map: bank_lsb + XOR-hash (replaces ADDR_MAP_TUNING) |
| 0x050  | `INIT_TUNING`             | ZQ retries + per-step init timeout                        |
| 0x054  | `TIMINGS_RTP_RTW`         | tRTP / tRTW                                               |
| 0x058  | `INIT_TIMING0`            | Init waits: tINIT / tDLLK                                 |
| 0x05C  | `INIT_TIMING1`            | Init waits: tMRD / tRP / tRFC                             |
| 0x060  | `DFI_PHASE`               | DFI READ/WRITE command sub-phase placement                |
| 0x064  | `PHY_TIMING`              | t_phy_wrlat / t_rddata_en / memtype / refresh_burst       |
| 0x080..0x09C | `OBS_ROW_HIT[8]`     | Per-bank row-hit count (RO, read-clear)                   |
| 0x0C0..0x0DC | `OBS_REF_LATENCY[8]` | Per-bank refresh-blocking cycles (RO)                     |
| 0x100..0x138 | `OBS_*`              | System observation / telemetry (RO)                       |
| 0x1C0..0x1E0 | `OBS_WORDS[9]`       | Packed obs_* harvest words (RO)                           |
| 0xFF0  | `ID`                      | Module ID (version / memtype / n_phases / 0xD2)           |
| 0xFF4  | `BUILD`                   | Build hash                                                |

## Field-Level Detail

All registers are 32-bit; unlisted bits are reserved (`RSVD`, `sw = r`). "Default" is the RDL reset value.

### CTRL @ 0x000 (rw)

| Bits | Field                   | Default | Notes                                       |
|------|-------------------------|---------|---------------------------------------------|
| 0    | `init_start`            | 0       | Write 1 to start init (swmod)               |
| 1    | `init_force_restart`    | 0       | Write 1 to force re-init mid-sequence (swmod) |
| 4    | `pwr_req_low_power`     | 0       | Request power-down                          |
| 5    | `pwr_req_dpd`           | 0       | Request DPD (LPDDR2 only)                    |
| 6    | `pwr_req_active`        | 0       | Request return to ACTIVE                     |
| 7    | `pwr_req_self_refresh`  | 0       | Request self-refresh                         |
| 31   | `soft_reset`            | 0       | Write 1 to assert internal soft reset (self-clearing, swmod) |

### STATUS @ 0x004 (RO, hw-written)

| Bits  | Field            | Notes                                     |
|-------|------------------|-------------------------------------------|
| 0     | `init_done`      | Init complete                             |
| 1     | `init_error`     | Init error                                |
| 7:4   | `power_state`    | Current power-state FSM state (encoded)   |
| 8     | `pasr_active`    | LPDDR2: PASR mask is non-zero             |
| 23:16 | `init_step_dbg`  | Current init step number (bring-up)       |
| 31    | `version_match`  | Build matches expected version            |

### STATUS_HISTORY @ 0x008 (RO)

| Bits | Field     | Notes                                            |
|------|-----------|--------------------------------------------------|
| 31:0 | `history` | 8 x 4-bit power-state history; most recent in [3:0] |

### TIMINGS_RC_RCD_RP_RAS @ 0x010 (rw)

| Bits  | Field  | Default (dec) | Notes |
|-------|--------|---------------|-------|
| 7:0   | `tRC`  | 60            | MC cycles |
| 15:8  | `tRCD` | 15            |       |
| 23:16 | `tRP`  | 15            |       |
| 31:24 | `tRAS` | 40            |       |

### TIMINGS_RFC_REFI @ 0x014 (rw)

| Bits  | Field   | Default (dec) | Notes            |
|-------|---------|---------------|------------------|
| 15:0  | `tRFC`  | 16            | or tRFCab; mission-mode REF recovery (arbiter down-counter) |
| 31:16 | `tREFI` | 1950          |                  |

### TIMINGS_RRD_FAW_WTR_CCD @ 0x018 (rw)

| Bits  | Field  | Default (dec) |
|-------|--------|---------------|
| 7:0   | `tRRD` | 6             |
| 15:8  | `tFAW` | 35            |
| 23:16 | `tWTR` | 4             |
| 31:24 | `tCCD` | 4             |

### TIMINGS_CL_CWL_WR @ 0x01C (rw)

| Bits  | Field    | Default (dec) | Notes               |
|-------|----------|---------------|---------------------|
| 7:0   | `CL`     | 6             | CAS latency         |
| 15:8  | `CWL`    | 4             | CAS write latency   |
| 23:16 | `tWR`    | 15            | Write recovery      |
| 31:24 | `tRFCpb` | 70            | LPDDR2 per-bank tRFC |

### MR0..MR3 @ 0x020 / 0x024 / 0x028 / 0x02C (rw)

| Bits | Field | Default | Notes                                    |
|------|-------|---------|------------------------------------------|
| 15:0 | `VAL` | 0       | Mode-register value loaded during init   |

### PASR_BANK_MASK_RANK0 @ 0x030 (rw)

| Bits | Field        | Default | Notes                              |
|------|--------------|---------|------------------------------------|
| 7:0  | `pasr_banks` | 0       | LPDDR2 MR16; bit N=1 masks bank N  |

### PASR_SEG_MASK_RANK0 @ 0x034 (rw)

| Bits | Field       | Default | Notes             |
|------|-------------|---------|-------------------|
| 7:0  | `pasr_segs` | 0       | LPDDR2 segment mask |

### TEMP_DERATE_RANK0 @ 0x038 (RO, hw-written)

| Bits | Field        | Notes                                             |
|------|--------------|---------------------------------------------------|
| 1:0  | `temp_class` | LPDDR2 MR4: 00 nominal, 01 2x refresh, 10 4x refresh |

### SCHED_TUNING @ 0x040 (rw)

| Bits  | Field                  | Default | Access | Notes                                        |
|-------|------------------------|---------|--------|----------------------------------------------|
| 3:0   | `lookahead_active`     | 0       | rw     | Active lookahead window (0 disables)         |
| 4     | `force_inorder`        | 0       | rw     | 1 = force first-ready FIFO                    |
| 5     | `RSVD_5`               | 0       | r      | Reserved (was `happy_enable` — retired)      |
| 15:8  | `age_max_runtime`      | 0       | rw     | Runtime AGE_MAX override (0 = build default) |
| 23:16 | `txn_queue_high_water` | 0       | rw     | Backpressure threshold                        |
| 27:24 | `lookahead_max_obs`    | 0       | RO     | Echo of build-time LOOKAHEAD_DEPTH_MAX       |

### PAGE_PRED_TUNING @ 0x044 (rw)

| Bits  | Field           | Default (dec) | Notes         |
|-------|-----------------|---------------|---------------|
| 15:0  | `warmup_cycles` | 1024          |               |
| 23:16 | `hysteresis`    | 2             |               |

### REFRESH_TUNING @ 0x048 (rw)

| Bits  | Field                  | Default | Notes                                          |
|-------|------------------------|---------|------------------------------------------------|
| 1:0   | `refpb_policy_or`      | 0       | 00 build-time, 01 RR, 10 OLDEST_FIRST, 11 DARP |
| 3:2   | `page_policy_or`       | 0       | 00 build-time, 01 OPEN, 10 CLOSE, 11 reserved (was HYBRID) |
| 7:4   | `refresh_defer_active` | 1       | Active refresh deferral count                   |
| 31:16 | `zqcs_freq_hz`         | 1       | Periodic ZQCS interval in Hz (0 disables)       |

### ADDR_MAP @ 0x04C (rw) — replaces the retired ADDR_MAP_TUNING

| Bits  | Field       | Default | Notes                                                        |
|-------|-------------|---------|--------------------------------------------------------------|
| 4:0   | `bank_lsb`  | 0x0A (=COL_WIDTH, ROW_MAJOR) | Bank-field LSB in the byte-offset-stripped word address; RTL clamps to [0, COL_WIDTH] |
| 8     | `hash_en`   | 0       | Enable bank XOR-hash: `bank ^= fold(row) ^ hash_seed`         |
| 23:16 | `hash_seed` | 0       | XOR-hash seed (`seed[BW-1:0]`)                                |

There is no scheme selector, `scheme_or`, or `synth_mask_obs`. ROW_MAJOR / BANK_INTERLEAVE / XOR_HASH are just settings of this one register (see §4.4 and `rtl/fub/addr_mapper.sv`).

### INIT_TUNING @ 0x050 (rw)

| Bits  | Field             | Default (dec) | Notes            |
|-------|-------------------|---------------|------------------|
| 3:0   | `zq_retries`      | 3             | ZQ retries (1..8) |
| 15:8  | `init_timeout_ms` | 10            | Init timeout ms   |

### TIMINGS_RTP_RTW @ 0x054 (rw)

| Bits | Field  | Default (dec) | Notes             |
|------|--------|---------------|-------------------|
| 7:0  | `tRTP` | 4             | Read to precharge |
| 15:8 | `tRTW` | 6             | Read to write     |

### INIT_TIMING0 @ 0x058 (rw)

| Bits  | Field         | Default (dec) | Notes             |
|-------|---------------|---------------|-------------------|
| 15:0  | `t_init_wait` | 512           | CKE/tINIT settle  |
| 31:16 | `t_dll_wait`  | 256           | DLL lock (tDLLK)  |

### INIT_TIMING1 @ 0x05C (rw)

| Bits  | Field        | Default (dec) | Notes               |
|-------|--------------|---------------|---------------------|
| 7:0   | `t_mrd_wait` | 8             | post mode-reg (tMRD) |
| 15:8  | `t_rp_wait`  | 8             | post precharge (tRP) |
| 23:16 | `t_rfc_wait` | 16            | post refresh (tRFC)  |

### DFI_PHASE @ 0x060 (rw)

| Bits | Field      | Default | Notes                             |
|------|------------|---------|-----------------------------------|
| 2:0  | `rd_phase` | 0       | READ command DFI sub-phase        |
| 6:4  | `wr_phase` | 0       | WRITE command DFI sub-phase       |

Sliced to `clog2(DFI_RATE)` bits downstream; upper bits ignored when `DFI_RATE` is small. On the Nexys A7 a7ddrphy, rd_phase=0 (the PHY handles rdphase internally).

### PHY_TIMING @ 0x064 (rw)

| Bits  | Field           | Default (dec) | Notes                                    |
|-------|-----------------|---------------|------------------------------------------|
| 7:0   | `t_phy_wrlat`   | 0             | WR cmd -> dfi_wrdata_en (Nexys A7 bring-up tuple programs 1) |
| 15:8  | `t_rddata_en`   | 6             | RD cmd -> dfi_rddata_en window           |
| 16    | `memtype`       | 0             | 0 = DDR2, 1 = LPDDR2                      |
| 23:20 | `refresh_burst` | 1             | REFs drained per request (1..8)          |

### Observation registers (RO)

| Offset       | Register / array       | Field       | Notes                              |
|--------------|------------------------|-------------|------------------------------------|
| 0x080..0x09C | `OBS_ROW_HIT[8]`       | `VAL[31:0]` | Per-bank row-hit count; read-clear (`onread = rclr`) |
| 0x0C0..0x0DC | `OBS_REF_LATENCY[8]`   | `VAL[31:0]` | Per-bank refresh-blocking cycles   |
| 0x100        | `OBS_TXN_QUEUE_DEPTH_MAX` | `VAL`    | Max queue depth observed           |
| 0x104        | `OBS_TXN_QUEUE_DEPTH_AVG` | `VAL`    | Time-averaged queue depth          |
| 0x108        | `OBS_REFRESH_PENDING_MAX` | `VAL`    | Max refresh_pending observed       |
| 0x10C..0x118 | `OBS_REFRESH_DEFER_HIST_0..3` | `VAL` | Refresh-deferral histogram bins    |
| 0x120        | (unmapped)               | —        | was `OBS_PAGE_PRED_ACCURACY` — retired; see `PAGE_STATS_*` |
| 0x130        | `OBS_AXI_R_LATENCY_AVG`  | `VAL`    | Avg AXI read latency (cycles)      |
| 0x134        | `OBS_AXI_R_LATENCY_P99`  | `VAL`    | 99th-pct AXI read latency          |
| 0x138        | `OBS_AXI_W_LATENCY_AVG`  | `VAL`    | Avg AXI write latency              |
| 0x1C0..0x1E0 | `OBS_WORDS[9]`         | `VAL`       | Packed obs_* harvest words         |

### ID @ 0xFF0 (RO) — reset 0xD2020001

| Bits  | Field       | Value | Notes               |
|-------|-------------|-------|---------------------|
| 7:0   | `version`   | 0x01  | Build version       |
| 15:8  | `memtype`   | 0x00  | 0 = DDR2, 1 = LPDDR2 |
| 23:16 | `n_phases`  | 0x02  | Gear ratio (1/2/4)  |
| 31:24 | `module_id` | 0xD2  | Fixed 0xD2          |

### BUILD @ 0xFF4 (RO)

| Bits | Field | Default | Notes           |
|------|-------|---------|-----------------|
| 31:0 | `VAL` | 0       | Build hash word |

## Multi-Rank / Multi-Bank Registers

The RDL declares per-bank observation arrays with `NUM_BANKS = 8` for rank 0 (`OBS_ROW_HIT[8]` at 0x080, `OBS_REF_LATENCY[8]` at 0x0C0). PASR / temperature registers are declared per rank as `*_RANK0` for the default single-rank build. The generated `pumice_regmap.py` flattens arrays into indexed register names (e.g., `OBS_ROW_HIT0_ROW_HIT`, `OBS_REF_LATENCY7_REF_LAT`, `OBS_WORDS8_WORD`). Multi-rank builds add the corresponding `*_RANK{N}` registers; there is no separate capability vector register in this RDL — software reads memtype/n_phases from `ID` (0xFF0).

## Reset Values

Reset defaults come straight from the RDL `= <value>` initializers (echoed in the `default`/`offset` entries of `pumice_regmap.py`). They are chosen so a "do nothing" bring-up sees a sane DDR2 baseline; DV programs the workload-specific values by name before triggering init.

## Open Questions / Future Work

- **Observation readback wiring.** The RO/telemetry registers are declared and generated, but `pumice_top` currently ties `hwif_in` to 0 (see §4.1). Connecting the live counters is a follow-up.
- **Multi-rank register generation.** The single-rank build declares only `*_RANK0`. A `NUM_RANKS`-driven RDL loop for the PASR/temp/observation windows is the natural extension.
- **RDL <-> regmap drift check.** `pumice_regmap.py` is generated from the RDL; a CI diff would catch manual edits.
