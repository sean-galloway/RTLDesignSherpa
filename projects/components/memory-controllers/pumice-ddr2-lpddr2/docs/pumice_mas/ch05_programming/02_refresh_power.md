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

# Refresh and Power-State Programming

> Per HAS §3.4 / §3.5 for architecture and §2.11 for FUB detail. This chapter is the **software-side** view of refresh and power configuration. Register writes are the PeakRDL cpuif (`csr_write`/`csr_read`); there is no apply/commit handshake — fields drive the core live (see §4.3).

---

## Tuning Refresh Behavior

```c
void configure_refresh(refresh_config_t* cfg) {
    // Base tREFI / tRFC (also set during init; retunable at runtime)
    csr_write(TIMINGS_RFC_REFI, REFI_PACK(cfg->trfc, cfg->trefi));

    // REFRESH_TUNING packs deferral count, page/refpb policy, ZQCS interval.
    uint32_t v = REFRESH_DEFER_ACTIVE(cfg->defer_active);   // 1..8

    // REFpb policy override (LPDDR2 only): 01 RR, 10 OLDEST_FIRST, 11 DARP
    if (cfg->refpb_policy == DARP)             v |= REFPB_POLICY_OR(3);
    else if (cfg->refpb_policy == OLDEST)      v |= REFPB_POLICY_OR(2);
    else if (cfg->refpb_policy == ROUND_ROBIN) v |= REFPB_POLICY_OR(1);

    // Periodic ZQCS interval in Hz (0 = disable)
    v |= ZQCS_FREQ_HZ(cfg->zqcs_freq_hz);

    csr_write(REFRESH_TUNING, v);   // live on the next refresh event boundary
}
```

`PHY_TIMING.refresh_burst` (1..8) additionally controls how many REFs are drained per refresh request.

### When to Tune

| Workload                                | Recommended config                       |
|-----------------------------------------|------------------------------------------|
| Streaming (DMA, video)                  | `defer_active = 8`, ZQCS = 1 Hz          |
| Low-latency bursty (CPU access)         | `defer_active = 1` (no batching), ZQCS = 0.1 Hz |
| Power-sensitive (sleep-heavy)           | `defer_active = 4`, ZQCS = 0.1 Hz        |
| Real-time / safety-critical             | `defer_active = 1`, deterministic refresh latency |

## LPDDR2 PASR (Partial Array Self-Refresh)

PASR masks DRAM regions that hold no data, reducing refresh power.

```c
void set_pasr_rank0(uint8_t bank_mask, uint8_t seg_mask) {
    csr_write(PASR_BANK_MASK_RANK0, bank_mask);
    csr_write(PASR_SEG_MASK_RANK0,  seg_mask);
    // Propagated to DRAM via MR16/MR17 at the next self-refresh entry.
}
```

The single-rank build exposes `PASR_BANK_MASK_RANK0` / `PASR_SEG_MASK_RANK0`; multi-rank `*_RANK{N}` registers are a follow-up (see §4.2). The PASR mask is propagated lazily — typically at the next self-refresh entry — to avoid an extra bus-blocking MR write during normal operation.

## Temperature Compensation (LPDDR2)

LPDDR2 devices expose temperature classification in MR4. The SoC reads this via PHY-side mechanisms (out of scope for the controller; the PHY signals temperature change via interrupt or polled register).

Software updates the controller's tREFI scaling:

`TEMP_DERATE_RANK0.temp_class` (0 = nominal, 1 = 2x refresh, 2 = 4x refresh) is a **read-only, hardware-written** field in this build — the controller captures the LPDDR2 MR4 class rather than software programming it. Software reads it to inform its own tREFI scaling via `TIMINGS_RFC_REFI`:

```c
uint8_t temp = csr_read(TEMP_DERATE_RANK0) & 0x3;
// Scale tREFI down for 2x/4x refresh as temp rises
csr_write(TIMINGS_RFC_REFI, REFI_PACK(trfc, trefi >> temp));  // live next reload
```

## Self-Refresh Entry

For periods of inactivity, software (or auto-detection) can put the DRAM into self-refresh:

The power-state request bits live in `CTRL`: `pwr_req_low_power`, `pwr_req_self_refresh`, `pwr_req_active`, `pwr_req_dpd`. `STATUS.power_state[7:4]` reports the current encoded state (RO, hw-written).

```c
void enter_self_refresh(void) {
    csr_write(CTRL, CTRL_PWR_REQ_SELF_REFRESH);
    while (STATUS_POWER_STATE(csr_read(STATUS)) != POWER_STATE_SELF_REFRESH);
}

void exit_self_refresh(void) {
    csr_write(CTRL, CTRL_PWR_REQ_ACTIVE);
    while (STATUS_POWER_STATE(csr_read(STATUS)) != POWER_STATE_ACTIVE);
}
```

Note: any AXI traffic to a rank will auto-wake it from SR. Explicit exit is only needed when the application wants to be ready before issuing.

There is no `POWER_TUNING` register in this build — idle-threshold auto-APD/SRF is not a CSR knob here. Power-state entry is software-requested via `CTRL`. (An auto-low-power threshold register is a possible follow-up; see below.)

## DPD (LPDDR2 Deep Power Down)

DPD is the deepest power state on LPDDR2 — DRAM is fully off; software must full-init to exit. The request bit is `CTRL.pwr_req_dpd` (inert on DDR2). Check the build memtype via `ID` (0xFF0) rather than a capability vector (there is no `0xFF8`):

```c
void enter_dpd(void) {
    if (((csr_read(ID) >> 8) & 0xFF) != MEMTYPE_LPDDR2) {
        log_error("DPD is LPDDR2-only");
        return;
    }
    csr_write(CTRL, CTRL_PWR_REQ_DPD);
    while (STATUS_POWER_STATE(csr_read(STATUS)) != POWER_STATE_DPD);
}

void exit_dpd(void) {
    start_dram_init();   // full re-init
}
```

DPD is rare in practice (DRAM fully unused for hours). Note the runtime family select is `PHY_TIMING.memtype`; `ID.memtype` is the build-time echo.

## Open Questions / Future Work

- **Auto power-down thresholds.** This build has no `POWER_TUNING` register — APD/SRF is request-driven. Adding idle-threshold CSRs for automatic low-power entry is a candidate feature.
- **Per-rank power control.** `CTRL.pwr_req_*` is channel-wide. Per-rank request registers are a multi-rank follow-up.
- **Observation readback.** `STATUS.power_state`, `STATUS_HISTORY`, and the `OBS_REFRESH_DEFER_HIST_*` telemetry are declared but `hwif_in` is tied off in `pumice_top` today (see §4.1); wiring them enables telemetry-driven auto-tuning.
