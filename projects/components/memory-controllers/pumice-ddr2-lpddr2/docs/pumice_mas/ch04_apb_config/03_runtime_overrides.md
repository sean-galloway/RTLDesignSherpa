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

# Runtime Overrides and Quiet Points

> Per HAS §5.1 for the build-time-vs-runtime principle and HAS §6.3 for the field-level register map. This MAS chapter is the **implementation protocol** for how runtime overrides actually commit to the live datapath.
>
> Quiet-point detection lives in `power_state_fub` (§2.13); the override staging registers and APB↔MC CDC live in `csr_apb_fub` (referenced throughout §2).

---

## Override Categories

| Category                          | Examples                                          | Commit point              |
|-----------------------------------|---------------------------------------------------|---------------------------|
| Synthesized-MAX, runtime-active   | `lookahead_active`, `refresh_defer_active`         | Next quiet point          |
| Synthesized-set, runtime-mux      | `scheme_or`, `refpb_policy_or`, `page_policy_or`   | Next quiet point          |
| Pure runtime                      | `zqcs_freq_hz`, `init_timeout_ms`, idle thresholds | Live (no quiet point)     |
| Behavioral kill-switch            | `force_inorder`, `happy_enable`                    | Next quiet point          |

The "pure runtime" category commits immediately on the APB write because the fields don't gate any in-flight DRAM state — they're consumed by counter reload-comparators that sample on the next event boundary anyway.

The other three categories require a quiet point because changing them mid-cycle could corrupt scheduler decisions, refresh sequencing, or address-mapping state.

## Quiet Point Definition

Per §2.13:

```
quiet_point = (txn_queue empty OR all entries PENDING)
            AND (refresh_mgr.dbg_state == IDLE)
            AND (init_engine.init_in_progress == 0)
            AND (cmd_encoder pipeline drained)
            AND (all ranks' power state == ACTIVE)
```

The detector is combinational; `csr_apb_fub` samples it on the rising edge of each MC clock.

## Software-Side Sequence

```c
// Pseudocode for runtime override commit
void write_override(uint32_t reg_offset, uint32_t value) {
    // 1. Write the staging field (returns immediately)
    apb_write(reg_offset, value);

    // 2. Request immediate commit (otherwise wait for natural quiet point)
    apb_write(CTRL, CTRL_CONFIG_APPLY);

    // 3. Poll for completion
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED)) {
        // typically settles in < 256 MC cycles
    }

    // 4. Clear config_apply
    apb_write(CTRL, 0);
}
```

The drain phase between step 2 and step 3 is bounded — typically < 256 MC cycles for a healthy queue, longer if there's an active refresh batch.

## Hardware-Side Sequence

```
cycle T:    APB write to staging field; staging register updates immediately
cycle T:    cfg_apply asserts via APB (separate write)
cycle T+1:  csr_apb_fub assert quiet_drain_request
cycle T+1:  scheduler stops accepting new issues; txn_queue drains
cycle T+1:  refresh_mgr completes any in-flight batch, then idles
cycle T+1:  cmd_encoder pipeline naturally drains over a few cycles
cycle T+1+N (N=drain): power_state_fub.quiet_point = 1
cycle T+1+N+1: csr_apb_fub copies staging → live for ALL R/W fields with pending writes
cycle T+1+N+1: csr_apb_fub releases quiet_drain_request; STATUS.config_settled = 1
cycle T+1+N+2: scheduler resumes normal operation with the new live values
```

The "ALL R/W fields with pending writes" behavior means **batch commit**: software can write multiple staging fields, then issue one `config_apply`, and all commit atomically.

## Batch Commit Example

To swap from `PAGE_POLICY = OPEN` to `PAGE_POLICY = HAPPY_HYBRID` and bump lookahead:

```c
// Stage all the changes
apb_write(REFRESH_TUNING, REFRESH_TUNING_PAGE_POLICY_OR_HAPPY_HYBRID);
apb_write(SCHED_TUNING, SCHED_TUNING_LOOKAHEAD_ACTIVE(4) | SCHED_TUNING_HAPPY_ENABLE);

// Single commit
apb_write(CTRL, CTRL_CONFIG_APPLY);
while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED)) { /* ... */ }
apb_write(CTRL, 0);

// All three fields are now live, with the same quiet-point edge
```

This is the recommended pattern for any multi-field configuration change.

## Quiet-Point Drain Latency

Empirical bounds:

| Scenario                                          | Drain latency               |
|---------------------------------------------------|----------------------------|
| Idle controller (no in-flight)                    | ~5 MC cycles                 |
| Light traffic (queue < 4 entries)                 | ~20 MC cycles                |
| Heavy traffic (queue near full)                   | ~100–256 MC cycles           |
| Active refresh batch                              | + REFRESH_DEFER_MAX × tRFCpb |
| Active ZQCS (rare)                                | + tZQCS                      |

For software that must complete a config swap in bounded time, time the wait against the worst-case bound:

```c
uint32_t timeout = WORST_CASE_DRAIN_CYCLES / mc_clk_to_apb_clk_ratio;
while (timeout-- && !(apb_read(STATUS) & STATUS_CONFIG_SETTLED));
if (!timeout) {
    // Timeout — diagnostic; should never happen on a healthy controller
}
```

## Conflicting Override Detection

If software writes the same field twice before commit, the second write supersedes the first. The staging register holds the latest value; there's no queue of pending changes.

If software issues `config_apply` while a previous commit is still in flight (`STATUS.config_settled = 0`), the new request is honored — the next quiet point will commit all pending changes.

## Open Questions / Future Work

- **Priority commits.** When refresh fires during a commit drain, refresh wins (per the priority hierarchy in §2.7). The commit waits. For software with hard real-time bounds, an "abort current refresh" mechanism could let commit win — but it violates JEDEC. Punt; rely on the worst-case bound.
- **Per-field commit.** Currently all pending stagings commit at once. A "commit-this-field-only" mode could reduce drain pressure. Adds CSR area; minor benefit. Punt.
- **Notification interrupt.** Software currently polls `STATUS.config_settled`. An IRQ option (`irq_config_settled`) would save polling cycles. Worth considering for SoCs with constrained CPU budget.
