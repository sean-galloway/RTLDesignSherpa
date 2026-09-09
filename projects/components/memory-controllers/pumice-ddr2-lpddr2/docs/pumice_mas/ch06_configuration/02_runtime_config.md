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
2. **JEDEC timings** — the `TIMINGS_*` registers. These do **not** default to
   anything usable for a given part and clock; leaving them at reset runs the
   DRAM at the RDL defaults, which is how the board spent a long time at a
   fraction of its bandwidth. Derive them from the part and the MC clock.
3. **Static page policy** — `REFRESH_TUNING.page_policy_or` (00 build-time,
   01 OPEN, 10 CLOSE; 11 reserved).
4. **Adaptive page policy (optional)** — `PAGE_POLICY_CFG.policy_mode`
   (0 build default, 1 static_open, 2 static_close, 3 fixed_open,
   4 adapt_time, 5 adapt_access, 6 rbl_static, 7 rbl_dyn). Program the table
   shape **before** the mode select so the predictor starts from a known
   table: `PAGE_POLICY_CFG.ctr_open_max` / `.ctr_init` for mode 5,
   `PAGE_RBL_CFG` for modes 6/7, `PAGE_TIMEOUT_CFG` for modes 3/4.
5. **Scheduling order** — `SCHED_POLICY.order_mode` (0 FR-FCFS, 1 in_order,
   3 age_threshold) plus `.age_thresh` for mode 3. See the build-tier note
   below.
6. **Refresh** — `REF_CTRL.mode` / `.postpone_limit` / `.pullin_limit`, and
   `TIMINGS_RFC_REFI.tREFI`; `PHY_TIMING.refresh_burst`.

> **Build tier.** `order_mode = 1` (in_order) is per-channel FIFO on the base
> bitstream: each CAM issues only its oldest entry and the arbiter's normal
> read/write preference chooses the side. GLOBAL read-versus-write age order
> additionally requires a `+define+PUMICE_ENHANCED` build. A base bitstream
> accepts the write either way, so software cannot detect the difference by
> readback — check the build, not the register.

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
| 3           | `REFRESH_TUNING.page_policy_or`         | OPEN vs CLOSE for the workload mix         |
| 4           | `PAGE_POLICY_CFG.policy_mode`           | Adaptive paging: 4 adapt_time, 5 adapt_access, 6/7 RBLA |
| 5           | `SCHED_POLICY.access_pref`              | column_first vs row_first vs precharge_first |
| 6           | `REF_CTRL.postpone_limit` / `.pullin_limit` | Refresh latency vs sustained BW        |
| 7           | `SCHED_POLICY.order_mode` / `.age_thresh` | Ordering guarantee vs bandwidth          |
| 8           | `SCHED_WR_WM.wr_high_wm` / `.wr_low_wm` | Write-batching turnaround                  |

## Telemetry to Watch

Observation registers per §4.2 (RO; note `hwif_in` readback is tied off in `pumice_top` today — see §4.1):

| Telemetry register              | What it tells you                    | Tune action                          |
|---------------------------------|--------------------------------------|--------------------------------------|
| `OBS_AXI_R_LATENCY_AVG` / `_P99`| AXI read latency (avg / tail)        | scheduler / lookahead / page policy / age_max |
| `OBS_AXI_W_LATENCY_AVG`         | AXI write latency                    | write-path / CWL alignment           |
| `OBS_ROW_HIT[bank]`             | Per-bank row-hit rate (read-clear)   | address mapping (`bank_lsb`/`hash`), page policy |
| `OBS_REF_LATENCY[bank]`         | Per-bank refresh blocking            | refresh deferral / refpb policy      |
| `OBS_TXN_QUEUE_DEPTH_MAX/AVG`   | Queue pressure                       | `SCHED_WR_WM` watermarks             |
| `OBS_REFRESH_PENDING_MAX`       | Proximity to refresh-deadline miss   | lower `REF_CTRL.postpone_limit`      |
| `OBS_REFRESH_DEFER_HIST_0..3`   | Refresh batch histogram              | validate `REF_CTRL.postpone_limit`   |
| `OBS_PAGE_PRED_ACCURACY`        | HAPPY prediction accuracy            | `warmup_cycles` / `hysteresis`       |
| `OBS_WORDS[9]`                  | Packed obs_* harvest                 | FUB-internal diagnostics             |

## Workload-Specific Recipes

### Streaming (DMA, video, audio capture)

```c
// Maximize row-hit, credit refresh, interleave banks
csr_write(REFRESH_TUNING, PAGE_POLICY_OR(1 /*OPEN*/));
csr_write(SCHED_POLICY,   ORDER_MODE(0 /*FR-FCFS*/));   // reorders across the whole CAM
csr_write(REF_CTRL,       POSTPONE_LIMIT(8) | PULLIN_LIMIT(8));
csr_write(ADDR_MAP,       BANK_LSB(log2_cols_per_burst));   // bank-interleave (pre-init)
```

### Low-Latency Bursty (CPU)

```c
// Adaptive close: let the per-row predictor decide when to shut the page.
// Table shape FIRST, then the mode select.
csr_write(PAGE_POLICY_CFG, CTR_OPEN_MAX(2) | CTR_INIT(0));
csr_write(PAGE_POLICY_CFG, CTR_OPEN_MAX(2) | CTR_INIT(0) | POLICY_MODE(5 /*adapt_access*/));
csr_write(REFRESH_TUNING,  PAGE_POLICY_OR(1 /*OPEN*/));
csr_write(REF_CTRL,        POSTPONE_LIMIT(1) | PULLIN_LIMIT(1));
csr_write(ADDR_MAP,        BANK_LSB(COL_WIDTH) | HASH_EN | HASH_SEED(seed));  // pre-init
```

### Real-Time / Safety-Critical

```c
// in_order = per-channel FIFO (global rd-vs-wr age order needs an
// ENHANCED build). Expect a bandwidth cost: under the auto-precharge paging
// modes each access is two dependent commands, so it pays the arbiter's pick
// pipeline twice -- see ch02 §7 and PUMICE-021.
csr_write(SCHED_POLICY,   ORDER_MODE(1 /*in_order*/));
csr_write(REFRESH_TUNING, PAGE_POLICY_OR(2 /*CLOSE*/));
csr_write(REF_CTRL,       POSTPONE_LIMIT(0) | PULLIN_LIMIT(0));   // strict tREFI
```

If strict ordering is not actually required and the goal is only bounded
latency, prefer `ORDER_MODE(3 /*age_threshold*/)` with `AGE_THRESH(n)`: it runs
FR-FCFS until a reference ages past `16*n` MC cycles and only then narrows to
the aged set, which bounds starvation at a fraction of the bandwidth cost.

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
