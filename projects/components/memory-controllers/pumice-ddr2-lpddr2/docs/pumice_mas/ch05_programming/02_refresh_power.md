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

> Per HAS §3.4 / §3.5 for architecture and §2.11 / §2.13 for FUB detail. This chapter is the **software-side** view of refresh and power configuration.

---

## Tuning Refresh Behavior

```c
void configure_refresh(refresh_config_t* cfg) {
    // Base tREFI (already set during init; can be retuned at runtime via TIMINGS_RAS_RFC_REFI)
    apb_write(TIMINGS_RAS_RFC_REFI, REFI_PACK(cfg->trfc, cfg->trefi));

    // Postponer batch depth (1..REFRESH_DEFER_MAX)
    // 1 = no batching; 8 = maximum batching (default)
    uint32_t v = REFRESH_DEFER_ACTIVE(cfg->defer_active);

    // REFpb policy override (LPDDR2 only)
    if (cfg->refpb_policy == DARP)            v |= REFPB_POLICY_OR_DARP;
    else if (cfg->refpb_policy == OLDEST)     v |= REFPB_POLICY_OR_OLDEST;
    else if (cfg->refpb_policy == ROUND_ROBIN) v |= REFPB_POLICY_OR_ROUND_ROBIN;

    // Periodic ZQCS interval (0 = disable, else Hz)
    v |= ZQCS_FREQ_HZ(cfg->zqcs_freq_hz);

    apb_write(REFRESH_TUNING, v);

    // Commit (quiet-point)
    apb_write(CTRL, CTRL_CONFIG_APPLY);
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED));
    apb_write(CTRL, 0);
}
```

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
void set_pasr_per_rank(uint8_t rank, uint8_t bank_mask, uint8_t seg_mask) {
    apb_write(PASR_BANK_MASK_RANK0 + rank*4, bank_mask);
    apb_write(PASR_SEG_MASK_RANK0 + rank*4,  seg_mask);

    // Wait for next self-refresh entry to propagate to DRAM via MR16/MR17
    // OR force immediate via quiet-point:
    apb_write(CTRL, CTRL_CONFIG_APPLY);
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED));
    apb_write(CTRL, 0);
}
```

The PASR mask is propagated lazily — typically at the next self-refresh entry — to avoid an extra bus-blocking MR write during normal operation. Forcing immediate propagation via `config_apply` is the right call when the application has decided "we just freed half the DRAM, refresh-power matters NOW."

## Temperature Compensation (LPDDR2)

LPDDR2 devices expose temperature classification in MR4. The SoC reads this via PHY-side mechanisms (out of scope for the controller; the PHY signals temperature change via interrupt or polled register).

Software updates the controller's tREFI scaling:

```c
void update_temperature_class(uint8_t rank, uint8_t temp_class) {
    // temp_class: 0 = nominal, 1 = 2x refresh, 2 = 4x refresh
    // Per-rank because ranks can be at different temperatures
    uint32_t v = apb_read(TEMP_DERATE_RANK0 + rank*4);
    v = (v & ~TEMP_CLASS_MASK) | TEMP_CLASS(temp_class);
    apb_write(TEMP_DERATE_RANK0 + rank*4, v);

    // Live — no quiet point needed (just scales the next t_refi_cnt reload)
}
```

The refresh manager scales tREFI by the per-rank class on the next reload.

## Self-Refresh Entry

For periods of inactivity, software (or auto-detection) can put the DRAM into self-refresh:

```c
void enter_self_refresh(void) {
    // Channel-wide request (v1)
    apb_write(CTRL, CTRL_PWR_REQ_SELF_REFRESH);

    // Poll for SR state
    while (1) {
        uint32_t s = apb_read(STATUS);
        uint8_t pstate = STATUS_POWER_STATE(s);
        if (pstate == POWER_STATE_SELF_REFRESH) break;
    }
}

void exit_self_refresh(void) {
    apb_write(CTRL, CTRL_PWR_REQ_ACTIVE);

    while (STATUS_POWER_STATE(apb_read(STATUS)) != POWER_STATE_ACTIVE);
}
```

Note: any AXI traffic to a rank will auto-wake it from SR. Explicit exit is only needed when the application knows it wants to be ready before issuing.

## Auto Power-Down Tuning

```c
void configure_auto_power_down(uint32_t apd_threshold, uint32_t srf_threshold) {
    apb_write(POWER_TUNING,
              POWER_TUNING_APD(apd_threshold) |
              POWER_TUNING_SRF(srf_threshold));

    apb_write(CTRL, CTRL_CONFIG_APPLY);
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED));
    apb_write(CTRL, 0);
}
```

| Threshold                    | Effect                                                                |
|------------------------------|----------------------------------------------------------------------|
| `apd_threshold = 1024`       | Default; ~5 µs idleness → APD                                          |
| `apd_threshold = 0xFFFF`     | Effectively disabled                                                  |
| `srf_threshold = 16M`        | Default; ~80 ms idleness → SRF                                         |
| `srf_threshold = 0xFFFFFF`   | Effectively disabled                                                  |

Per-rank idleness counters mean each rank enters APD/SRF independently if traffic concentrates on a subset.

## DPD (LPDDR2 Deep Power Down)

DPD is the deepest power state on LPDDR2 — DRAM is fully off; software must full-init to exit.

```c
void enter_dpd(void) {
    // Sanity: LPDDR2 only
    if (!(apb_read(0xFF8) & CAP_DPD)) {
        log_error("DPD not supported on this build");
        return;
    }

    apb_write(CTRL, CTRL_PWR_REQ_DPD);

    while (STATUS_POWER_STATE(apb_read(STATUS)) != POWER_STATE_DPD);
}

void exit_dpd(void) {
    // Re-init the rank
    start_dram_init();
}
```

DPD is rare in practice — typical use is "DRAM is fully unused for hours" (long-suspend laptop). The full-init exit takes ~250 µs.

## Open Questions / Future Work

- **Per-rank CSR control.** Channel-wide power request is v1. Per-rank request (`CTRL.pwr_req_low_power_rank_R<R>`) for partial low-power without affecting active ranks would be useful for many workloads. Not in v1; see §2.13 open questions.
- **SR lock.** Software-forced SR can be woken by AXI traffic. A "stay in SR until I say go" mode would be useful for guaranteed-low-power testing. Punt to v2.
- **Auto-tune from telemetry.** The refresh-deferral histogram (`OBS_REFRESH_DEFER_HIST_*`) hints at what `defer_active` should be. Could a kernel/firmware loop auto-tune? Likely yes; needs characterization data first.
