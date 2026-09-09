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
| 0x040  | `SCHED_TUNING`            | Retired — reserved in full (scheduling is `SCHED_POLICY`)  |
| 0x044  | (unmapped)                | was `PAGE_PRED_TUNING` — retired with the HAPPY predictor |
| 0x048  | `REFRESH_TUNING`          | Page-policy override (the refresh fields are retired)     |
| 0x04C  | `ADDR_MAP`                | Address-map: bank_lsb + XOR-hash (replaces ADDR_MAP_TUNING) |
| 0x068  | `SCHED_POLICY`            | Axis 1 scheduling: order_mode / prio_sub / row_sel / col_sel / access_pref / qos_en / age_thresh |
| 0x06C  | `SCHED_WR_WM`             | Write-batching drain watermarks                            |
| 0x070  | `PAGE_POLICY_CFG`         | Axis 2 paging mode select + adapt_access counter shape     |
| 0x074  | `PAGE_TIMEOUT_CFG`        | fixed_open / adapt_time timeout bounds                     |
| 0x078  | `PAGE_ADAPT_CFG`          | adapt_time mistake-counter thresholds                      |
| 0x07C  | `PAGE_RBL_CFG`            | RBLA miss-counter table shape (modes 6/7)                  |
| 0x140  | `REF_CTRL`                | Axis 3 refresh mode + JEDEC postpone/pull-in credits       |
| 0x144  | `REF_TIMING_PB`           | REFpb intervals                                            |
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

### SCHED_TUNING @ 0x040 (retired — reserved in full)

| Bits  | Field  | Default | Access | Notes                                    |
|-------|--------|---------|--------|------------------------------------------|
| 31:0  | `RSVD` | 0       | r      | Reserved (retired scheduler knobs)        |

> **RETIRED 2026-09-09.** Every field of this register belonged to the
> pre-rearchitecture scheduler: `lookahead_active`, `force_inorder`,
> `age_max_runtime`, `txn_queue_high_water` and the `lookahead_max_obs` echo
> (plus `happy_enable`, retired earlier with the HAPPY predictor). The
> CAM + arbiter scheduler has never read any of them, so a write here was a
> silent no-op — the host's `inorder` characterization preset was programming
> this bit and getting FR-FCFS on silicon.
>
> Scheduling is [`SCHED_POLICY` @ 0x068](#sched_policy--0x068-rw):
> `order_mode` selects in_order / age_threshold, and FR-FCFS reorders across
> the whole CAM so there is no lookahead window to size. The address is kept
> reserved rather than reused so the map does not shift.

### PAGE_PRED_TUNING @ 0x044 (rw)

| Bits  | Field           | Default (dec) | Notes         |
|-------|-----------------|---------------|---------------|
| 15:0  | `warmup_cycles` | 1024          |               |
| 23:16 | `hysteresis`    | 2             |               |

### REFRESH_TUNING @ 0x048 (rw)

| Bits  | Field            | Default | Access | Notes                                          |
|-------|------------------|---------|--------|------------------------------------------------|
| 1:0   | `RSVD_1_0`       | 0       | r      | Reserved (was `refpb_policy_or`) |
| 3:2   | `page_policy_or` | 0       | rw     | 00 build-time, 01 OPEN, 10 CLOSE, 11 reserved (was HYBRID) |
| 15:4  | `RSVD_15_4`      | 0       | r      | Reserved (was `refresh_defer_active`) |
| 31:16 | `RSVD_31_16`     | 0       | r      | Reserved (was `zqcs_freq_hz`) |

> **PARTIALLY RETIRED 2026-09-09.** `page_policy_or` is live and is the static
> OPEN/CLOSE override. The three refresh fields are not: refresh mode and the
> JEDEC postpone/pull-in credits are [`REF_CTRL` @ 0x140](#ref_ctrl--0x140-rw),
> and no ZQCS engine ever consumed the interval.

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

### Advanced-mode registers (0x068-0x07C, 0x140-0x144)

> **Added to this chapter 2026-09-09.** These registers have existed in
> `pumice_csr.rdl` since the PUMICE-006 mode work and are cited by
> [ch02/07 Command Arbiter](../ch02_blocks/07_scheduler.md) and
> [ch02/08 Page Policy](../ch02_blocks/08_page_policy.md), but the register map
> never listed them. They are the three mode axes: scheduling (`SCHED_POLICY`,
> `SCHED_WR_WM`), paging (`PAGE_*_CFG`) and refresh (`REF_*`). Every field
> encodes 0 as "build default", so a zeroed register block is bit-identical to
> the pre-mode controller.

### SCHED_POLICY @ 0x068 (rw)

Axis 1 (Rixner FR-FCFS variants). All fields 0 = build default.

| Bits  | Field | Default | Access | Notes |
|-------|-------|---------|--------|-------|
| 1:0 | `order_mode` | 0x0 | rw | 0=build default, 1=in_order, 2=fr_fcfs, 3=age_threshold |
| 3:2 | `prio_sub` | 0x0 | rw | Priority sub-policy: 0=default, 1=none, 2=load_over_store, 3=age_boost |
| 5:4 | `row_sel` | 0x0 | rw | Row-arbiter select: 0=default(oldest), 1=most_pending, 2=fewest_pending |
| 7:6 | `col_sel` | 0x0 | rw | Column-arbiter select: 0=default(oldest), 1=most_pending, 2=fewest_pending |
| 9:8 | `access_pref` | 0x0 | rw | Address-arbiter class preference: 0=default, 1=column_first, 2=row_first, 3=precharge_first |
| 10:10 | `RSVD_10` | 0x0 | r | Reserved (was auto_precharge_en, never consumed: auto-precharge is driven by PAGE_POLICY_CFG.policy_mode -- static_close and the modes 5..7 predictors) |
| 11:11 | `qos_en` | 0x0 | rw | 1 = factor AxQOS into the pick (highest ready first, age tie-break) |
| 15:12 | `RSVD_15_12` | 0x0 | r | Reserved |
| 23:16 | `age_thresh` | 0x0 | rw | age_threshold mode: age (MC cycles/16) above which a reference is boosted |
| 31:24 | `RSVD_31_24` | 0x0 | r | Reserved |

### SCHED_WR_WM @ 0x06C (rw)

Write-batching drain hysteresis. 0/0 = build default (no batching).

| Bits  | Field | Default | Access | Notes |
|-------|-------|---------|--------|-------|
| 7:0 | `wr_high_wm` | 0x0 | rw | Start back-to-back write drain when the write buffer crosses this |
| 15:8 | `wr_low_wm` | 0x0 | rw | Stop the drain when occupancy falls to this |
| 31:16 | `RSVD` | 0x0 | r | Reserved |

### PAGE_POLICY_CFG @ 0x070 (rw)

Axis 2 mode select + adapt_access counter shape. 0 = build default.

| Bits  | Field | Default | Access | Notes |
|-------|-------|---------|--------|-------|
| 2:0 | `policy_mode` | 0x0 | rw | 0=build default, 1=static_open, 2=static_close, 3=fixed_open, 4=adapt_time, 5=adapt_access, 6=rbl_static, 7=rbl_dyn |
| 3:3 | `policy_scope` | 0x0 | rw | 0 = per-bank decision state, 1 = global |
| 5:4 | `RSVD_5_4` | 0x0 | r | Reserved (was ctr_width; the adapt_access counter is the 2-bit saturating counter of the paper, not selectable) |
| 9:6 | `ctr_open_max` | 0x0 | rw | adapt_access: counter value at/above which the row is CLOSED |
| 13:10 | `ctr_init` | 0x0 | rw | adapt_access: counter init value |
| 31:14 | `RSVD` | 0x0 | r | Reserved |

### PAGE_TIMEOUT_CFG @ 0x074 (rw)

fixed_open / adapt_time timeout register bounds (MC cycles).

| Bits  | Field | Default | Access | Notes |
|-------|-------|---------|--------|-------|
| 7:0 | `tr_init` | 0x0 | rw | TR init (fixed_open uses this alone; ~tRC) |
| 15:8 | `tr_min` | 0x0 | rw | adapt_time TR lower clamp |
| 23:16 | `tr_max` | 0x0 | rw | adapt_time TR upper clamp |
| 31:24 | `tr_step` | 0x0 | rw | adapt_time TR adjustment step |

### PAGE_ADAPT_CFG @ 0x078 (rw)

adapt_time (Happy adaptive-timeout) mistake-counter thresholds.

| Bits  | Field | Default | Access | Notes |
|-------|-------|---------|--------|-------|
| 3:0 | `mc_high_thr` | 0x0 | rw | MC high threshold (TR += step above) |
| 7:4 | `mc_low_thr` | 0x0 | rw | MC low threshold (TR -= step below) |
| 11:8 | `mc_init` | 0x0 | rw | MC init value |
| 15:12 | `RSVD` | 0x0 | r | Reserved |
| 31:16 | `check_interval` | 0x0 | rw | Cycles between MC evaluations |

### PAGE_RBL_CFG @ 0x07C (rw)

RBLA/Yoon miss-counter table shape. rbl_dyn hill-climb weights land with that mode.

| Bits  | Field | Default | Access | Notes |
|-------|-------|---------|--------|-------|
| 7:0 | `miss_thresh` | 0x0 | rw | Miss count above which a row is low-locality (auto-precharge) |
| 9:8 | `ways` | 0x0 | rw | log2 table ways |
| 13:10 | `sets` | 0x0 | rw | log2 table sets |
| 15:14 | `RSVD` | 0x0 | r | Reserved |
| 31:16 | `reset_interval` | 0x0 | rw | Epoch length: counters reset every N cycles (0=never) |

### REF_CTRL @ 0x140 (rw)

Axis 3 mode + JEDEC +-8 credit limits. tREFI/tRFCab live in TIMINGS_RFC_REFI (not duplicated).

| Bits  | Field | Default | Access | Notes |
|-------|-------|---------|--------|-------|
| 1:0 | `mode` | 0x0 | rw | 0=build default (REFab), 1=REFab, 2=REFpb round-robin (LPDDR2) |
| 3:2 | `RSVD_3_2` | 0x0 | r | Reserved |
| 7:4 | `postpone_limit` | 0x0 | rw | Max refreshes postponed under demand (0..8; 0 = strict) |
| 11:8 | `pullin_limit` | 0x0 | rw | Max refreshes pulled in on idle (0..8; 0 = strict) |
| 12:12 | `perbank_supported` | 0 | r | Capability strap: 1 = the DRAM supports per-bank refresh |
| 31:13 | `RSVD_31_13` | 0x0 | r | Reserved |

### REF_TIMING_PB @ 0x144 (rw)

REFpb intervals (MC cycles). All-bank tREFI/tRFCab stay in TIMINGS_RFC_REFI.

| Bits  | Field | Default | Access | Notes |
|-------|-------|---------|--------|-------|
| 15:0 | `trefi_pb` | 0x0 | rw | tREFIpb (~tREFI/8; 0 = derive from tREFI) |
| 23:16 | `trfc_pb` | 0x0 | rw | tRFCpb recovery |
| 31:24 | `RSVD` | 0x0 | r | Reserved |


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
