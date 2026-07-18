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

> Per §4.2 for the full CSR map and §4.3 for the config-drive model (fields drive the core live; no apply/commit step). This chapter is the **driver author's** cookbook for runtime tunables: what to tune, when, and what to watch for. Register access is the PeakRDL cpuif (`csr_write`/`csr_read`).

---

## Bring-Up Configuration Order

When bring-up software first comes up, recommended order (address map and memtype are set **before** init — see §5.1):

1. **Family + address map (pre-init)** — `PHY_TIMING.memtype`; `ADDR_MAP.bank_lsb` / `.hash_en` / `.hash_seed`.
2. **Set page policy** — `REFRESH_TUNING.page_policy_or` (00 build-time, 01 OPEN, 10 CLOSE, 11 HAPPY_HYBRID).
3. **Set lookahead depth** — `SCHED_TUNING.lookahead_active` (0 disables).
4. **Set refresh deferral** — `REFRESH_TUNING.refresh_defer_active`; `PHY_TIMING.refresh_burst`.
5. **Set ZQCS frequency** — `REFRESH_TUNING.zqcs_freq_hz` (1 Hz default; 0 to disable).

Each write is live immediately at the core boundary; there is no `config_apply` and no quiet-point drain. Quiesce AXI traffic before changing a field that would corrupt in-flight state (see §4.3).

## Address-Map Tuning (single knob)

Address mapping is `ADDR_MAP.bank_lsb` alone (plus the optional XOR-hash). There is no scheme selector, `scheme_or`, or `xor_seed_runtime`:

```c
// ROW_MAJOR: bank field above the whole column
csr_write(ADDR_MAP, BANK_LSB(COL_WIDTH));

// Max BANK_INTERLEAVE: bank field just above the burst's low column bits
csr_write(ADDR_MAP, BANK_LSB(log2_cols_per_burst));

// XOR_HASH folded on top of any placement
csr_write(ADDR_MAP, BANK_LSB(COL_WIDTH) | HASH_EN | HASH_SEED(seed));
```

RTL clamps `bank_lsb` to `[0, COL_WIDTH]`; keep `log2(BL/DFI_RATE) <= bank_lsb <= COL_WIDTH` so a DRAM burst stays inside one bank (see §4.4 and `rtl/fub/addr_mapper.sv`). Change address mapping only before init or with the datapath idle.

## Characterization Sweep Order

| Sweep order | Knob                                   | Why                                        |
|-------------|----------------------------------------|--------------------------------------------|
| 1           | `ADDR_MAP.bank_lsb`                     | Largest impact on row-hit / bank parallelism |
| 2           | `ADDR_MAP.hash_en` / `.hash_seed`       | Defeat power-of-two-stride hot-banking     |
| 3           | `REFRESH_TUNING.page_policy_or`         | OPEN vs CLOSE vs HAPPY for the workload mix |
| 4           | `SCHED_TUNING.lookahead_active`         | Issue rate vs lookahead depth              |
| 5           | `SCHED_TUNING.happy_enable`             | A/B test the predictor (HAPPY only)        |
| 6           | `REFRESH_TUNING.refresh_defer_active`   | Refresh latency vs sustained BW            |
| 7           | `SCHED_TUNING.age_max_runtime`          | Anti-starvation tuning                     |
| 8           | `SCHED_TUNING.txn_queue_high_water`     | Backpressure timing                        |

## Telemetry to Watch

Observation registers per §4.2 (RO; note `hwif_in` readback is tied off in `pumice_top` today — see §4.1):

| Telemetry register              | What it tells you                    | Tune action                          |
|---------------------------------|--------------------------------------|--------------------------------------|
| `OBS_AXI_R_LATENCY_AVG` / `_P99`| AXI read latency (avg / tail)        | scheduler / lookahead / page policy / age_max |
| `OBS_AXI_W_LATENCY_AVG`         | AXI write latency                    | write-path / CWL alignment           |
| `OBS_ROW_HIT[bank]`             | Per-bank row-hit rate (read-clear)   | address mapping (`bank_lsb`/`hash`), page policy |
| `OBS_REF_LATENCY[bank]`         | Per-bank refresh blocking            | refresh deferral / refpb policy      |
| `OBS_TXN_QUEUE_DEPTH_MAX/AVG`   | Queue pressure                       | `txn_queue_high_water`               |
| `OBS_REFRESH_PENDING_MAX`       | Proximity to refresh-deadline miss   | lower `refresh_defer_active`         |
| `OBS_REFRESH_DEFER_HIST_0..3`   | Refresh batch histogram              | validate `refresh_defer_active`      |
| `OBS_PAGE_PRED_ACCURACY`        | HAPPY prediction accuracy            | `warmup_cycles` / `hysteresis`       |
| `OBS_WORDS[9]`                  | Packed obs_* harvest                 | FUB-internal diagnostics             |

## Workload-Specific Recipes

### Streaming (DMA, video, audio capture)

```c
// Maximize row-hit, batch refresh, interleave banks
csr_write(SCHED_TUNING,   LOOKAHEAD_ACTIVE(4) | HAPPY_ENABLE);
csr_write(REFRESH_TUNING, REFRESH_DEFER_ACTIVE(8) | PAGE_POLICY_OR(1 /*OPEN*/) | ZQCS_FREQ_HZ(1));
csr_write(ADDR_MAP,       BANK_LSB(log2_cols_per_burst));   // bank-interleave (pre-init)
```

### Low-Latency Bursty (CPU)

```c
csr_write(SCHED_TUNING,   LOOKAHEAD_ACTIVE(2) | HAPPY_ENABLE);
csr_write(REFRESH_TUNING, REFRESH_DEFER_ACTIVE(1) | PAGE_POLICY_OR(3 /*HAPPY*/));
csr_write(ADDR_MAP,       BANK_LSB(COL_WIDTH) | HASH_EN | HASH_SEED(seed));  // pre-init
```

### Real-Time / Safety-Critical

```c
csr_write(SCHED_TUNING,   FORCE_INORDER | LOOKAHEAD_ACTIVE(0));
csr_write(REFRESH_TUNING, REFRESH_DEFER_ACTIVE(1) | PAGE_POLICY_OR(2 /*CLOSE*/));
```

## Telemetry-Driven Auto-Tuning Loop

For SoCs with firmware capable of background loops (once observation readback is wired):

```c
void periodic_autotune(void) {
    static uint8_t defer = 8;
    uint32_t pending_max = csr_read(OBS_REFRESH_PENDING_MAX);

    if (pending_max > DEFER_BUDGET * 7 / 8)      { if (defer > 1) defer--; }
    else if (pending_max < DEFER_BUDGET / 4)     { if (defer < 8) defer++; }

    uint32_t v = csr_read(REFRESH_TUNING);
    v = (v & ~REFRESH_DEFER_ACTIVE_MASK) | REFRESH_DEFER_ACTIVE(defer);
    csr_write(REFRESH_TUNING, v);   // live on the next refresh event boundary
}
```

Run every ~100 ms. Writes are cheap (no commit drain) and workload-dependent tuning is automatic.

## Open Questions / Future Work

- **Observation readback.** The telemetry recipes assume `hwif_in` is wired; it is tied off today (§4.1).
- **Profile-select CSR.** A single "workload profile" field that switches all knobs at once would simplify firmware; adds CSR area. Punt.
- **QoS priority.** `awqos`/`arqos` are on the AXI port but not yet consumed by the scheduler; a v2 hook.
