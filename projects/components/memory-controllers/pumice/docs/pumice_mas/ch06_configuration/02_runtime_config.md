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

# Runtime Configuration Reference

> Per HAS §6.3 for the full CSR map. Per §4.3 for the staging-vs-live commit protocol. This chapter is the **driver author's** cookbook for runtime tunables: what to tune, when, and what to watch for.

---

## Bring-Up Configuration Order

When bring-up software first comes up after init, recommended order:

1. **Verify capability vector** — `apb_read(0xFF8)`. Confirm `cap_max_ranks`, `cap_n_phases`, `cap_memtype` match expectations.
2. **Set address-map scheme** — `ADDR_MAP_TUNING.scheme_or` to match the SoC's physical-address layout.
3. **Set page policy** — `REFRESH_TUNING.page_policy_or` if not using build default.
4. **Set lookahead depth** — `SCHED_TUNING.lookahead_active`. Start at MAX, tune down if area-sensitive.
5. **Set refresh deferral** — `REFRESH_TUNING.refresh_defer_active`. Start at MAX; tune for workload.
6. **Set ZQCS frequency** — `REFRESH_TUNING.zqcs_freq_hz`. 1 Hz default; 0 to disable.
7. **Set ODT rule** (multi-rank only) — `RANK_TUNING.odt_rule_or` per board design.
8. **Set power thresholds** — `POWER_TUNING.apd_idle_threshold`, `POWER_TUNING.srf_idle_threshold`.

Issue `CTRL.config_apply = 1` once at the end to commit all in a single quiet-point drain (per §4.3 batch commit).

## Characterization Sweep Order

For tuning on a specific workload:

| Sweep order | Knob                                  | Why first                                  |
|-------------|---------------------------------------|--------------------------------------------|
| 1           | `ADDR_MAP_TUNING.scheme_or`           | Largest impact on row-hit rate              |
| 2           | `ADDR_MAP_TUNING.xor_seed_runtime`     | For XOR_HASH, hunt for pathological collisions |
| 3           | `SCHED_TUNING.lookahead_active`        | Direct trade between issue rate and lookahead area |
| 4           | `REFRESH_TUNING.page_policy_or`        | OPEN vs CLOSE vs HAPPY for the workload mix |
| 5           | `SCHED_TUNING.happy_enable`            | A/B test the predictor (HAPPY only)        |
| 6           | `REFRESH_TUNING.refresh_defer_active`  | Trade refresh latency vs sustained BW       |
| 7           | `SCHED_TUNING.age_max_runtime`         | Anti-starvation tuning                      |
| 8           | `SCHED_TUNING.txn_queue_high_water`    | Backpressure timing                         |

Re-run at each step; observe telemetry (next section) to decide which way to tune.

## Telemetry to Watch

| Telemetry register                       | What it tells you                                    | Tune action                                  |
|------------------------------------------|------------------------------------------------------|----------------------------------------------|
| `OBS_AXI_R_LATENCY_AVG`                  | Average AXI read latency                              | Tune scheduler / lookahead / page policy     |
| `OBS_AXI_R_LATENCY_P99`                  | Tail read latency                                    | Tune anti-starvation, age_max                |
| `OBS_AXI_W_LATENCY_AVG`                  | Average AXI write latency                            | Tune CWL alignment / wr_data_path             |
| `OBS_ROW_HIT_RANK<R>_BANK<N>`            | Per-bank row-hit rate                                 | Tune address mapping, page policy            |
| `OBS_REF_LATENCY_RANK<R>_BANK<N>`        | Per-bank refresh blocking                            | Tune refresh deferral / REFpb policy         |
| `OBS_TXN_QUEUE_DEPTH_MAX/AVG`            | Queue pressure                                        | Tune high water mark                         |
| `OBS_REFRESH_PENDING_MAX`                | How close to refresh-deadline-miss                    | Lower refresh_defer_active                   |
| `OBS_REFRESH_DEFER_HIST_0..3`            | Refresh batch histogram                               | Validate refresh_defer_active choice         |
| `OBS_PAGE_PRED_ACCURACY`                 | HAPPY accuracy (when enabled)                        | Tune warmup / hysteresis                     |
| `OBS_INORDER_FALLBACKS`                  | How often OoO would have helped                      | Decide if force_inorder costs too much       |
| `OBS_LOOKAHEAD_HITS`                     | Conclusive-lookahead rate                            | Decide if increasing lookahead_active helps  |
| `OBS_XRANK_SWITCHES`                     | Cross-rank traffic frequency (NR>1)                  | Address mapping might cluster traffic better |
| `OBS_TFAW_HITS_RANK<R>`                  | Per-rank tFAW pressure                                | Workload-dependent — high values flag thermal limits |
| `OBS_TWTR_HITS`                          | Write-to-read turnaround pressure                     | Workload mix issue                          |
| `OBS_ODT_PULSE_PCT_R<R>` (NR>1)          | Fraction of cycles per-rank ODT is on                | Power telemetry                              |

## Workload-Specific Recipes

### Streaming (DMA, video, audio capture)

```c
// Maximize row-hit, batch refresh
apb_write(SCHED_TUNING, LOOKAHEAD_ACTIVE(4) | HAPPY_ENABLE);
apb_write(REFRESH_TUNING, REFRESH_DEFER_ACTIVE(8) | PAGE_POLICY_OR_OPEN | ZQCS_FREQ_HZ(1));
apb_write(ADDR_MAP_TUNING, SCHEME_OR(BANK_INTERLEAVE));
apb_write(CTRL, CTRL_CONFIG_APPLY);
```

### Low-Latency Bursty (CPU)

```c
// Prioritize first-beat latency, minimal refresh deferral
apb_write(SCHED_TUNING, LOOKAHEAD_ACTIVE(2) | HAPPY_ENABLE);
apb_write(REFRESH_TUNING, REFRESH_DEFER_ACTIVE(1) | PAGE_POLICY_OR_HAPPY | ZQCS_FREQ_HZ(0.1));
apb_write(ADDR_MAP_TUNING, SCHEME_OR(XOR_HASH));
apb_write(CTRL, CTRL_CONFIG_APPLY);
```

### Real-Time / Safety-Critical

```c
// Deterministic; predictable refresh, no OoO
apb_write(SCHED_TUNING, FORCE_INORDER | LOOKAHEAD_ACTIVE(0));
apb_write(REFRESH_TUNING, REFRESH_DEFER_ACTIVE(1) | PAGE_POLICY_OR_CLOSE);
apb_write(CTRL, CTRL_CONFIG_APPLY);
```

### Power-Sensitive (Sleep-Heavy)

```c
apb_write(SCHED_TUNING, LOOKAHEAD_ACTIVE(4) | HAPPY_ENABLE);
apb_write(REFRESH_TUNING, REFRESH_DEFER_ACTIVE(4));
apb_write(POWER_TUNING, APD(512) | SRF(8000000));   // aggressive auto-low-power
apb_write(CTRL, CTRL_CONFIG_APPLY);
```

### Multi-Rank DIMM Workload Distribution

```c
// LPDDR2 with 4 ranks, DARP refresh, JEDEC_DDR2 ODT
apb_write(REFRESH_TUNING, REFPB_POLICY_OR(DARP) | REFRESH_DEFER_ACTIVE(8));
apb_write(RANK_TUNING, ODT_RULE_OR(JEDEC_DDR2));
apb_write(POWER_TUNING, APD(2048) | SRF(16000000));   // larger thresholds for multi-rank
apb_write(CTRL, CTRL_CONFIG_APPLY);
```

## Telemetry-Driven Auto-Tuning Loop

For SoCs with firmware capable of background loops:

```c
void periodic_autotune(void) {
    static uint8_t defer = 8;
    uint32_t pending_max = apb_read(REFRESH_PENDING_MAX);

    if (pending_max > REFRESH_DEFER_MAX * 7 / 8) {
        // Approaching deadline miss; back off batching
        if (defer > 1) defer--;
    }
    else if (pending_max < REFRESH_DEFER_MAX / 4) {
        // Plenty of headroom; allow more batching
        if (defer < REFRESH_DEFER_MAX) defer++;
    }

    uint32_t v = apb_read(REFRESH_TUNING);
    v = (v & ~REFRESH_DEFER_ACTIVE_MASK) | REFRESH_DEFER_ACTIVE(defer);
    apb_write(REFRESH_TUNING, v);
    apb_write(CTRL, CTRL_CONFIG_APPLY);
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED));
    apb_write(CTRL, 0);
}
```

Run this every 100 ms or so. The CSR commits are cheap (small quiet-point drain) and the workload-dependent tuning is automatic.

## Open Questions / Future Work

- **Recommended-default switching by workload identifier.** Some SoCs identify the workload (graphics vs CPU vs idle). Could the controller accept a "profile select" CSR that switches all knobs at once? Adds CSR area; useful for firmware-controlled systems. Punt.
- **Telemetry-based ML tuning.** Long-horizon ML could optimize the entire knob set per workload. Out of scope for the controller; would live in firmware.
- **Per-application priority via QoS.** v2 feature using `awqos`/`arqos`. The hooks are in the scheduler interface; just not wired in v1.
