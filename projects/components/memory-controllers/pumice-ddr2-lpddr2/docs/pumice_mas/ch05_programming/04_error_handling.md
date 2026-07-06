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

# Error Handling

> The controller's error reporting paths and the recommended software response model. Per HAS §2.4 §4 for the IRQ port list and the per-FUB CSR-hook sections in MAS Ch 2.

---

## Error Categories

| Category                       | Detection                                | Reporting                                          |
|--------------------------------|------------------------------------------|----------------------------------------------------|
| Init failure                   | `init_engine_fub` WAIT_FOR_BIT timeout or ZQ retries exhausted | `STATUS.init_error = 1`, `irq_init_error` pulse |
| AXI queue overflow             | Hard backpressure exceeded (rare)         | `STATUS.txn_queue_full_pulses` + `irq_overflow`     |
| Refresh deadline miss          | `refresh_owed` exceeds safety margin     | `irq_overflow`                                     |
| DFI rddata-valid timeout       | RD issued, no rddata arrived in CL × N + slack | `irq_overflow` + `SLVERR` on the AXI R           |
| AXI burst boundary violation   | Per §3.1                                  | `SLVERR` on B/R; no IRQ                            |
| ZQ calibration failure (silicon issue) | DFI signal-integrity check via training | Caught at PHY layer, not this controller          |
| Multi-bit DRAM error           | Out of scope (no inline ECC in v1)        | Would need ECC sideband                            |

## IRQ Topology

Per HAS §2.4 §4:

| IRQ                    | Source                                       | Latch behavior            |
|------------------------|----------------------------------------------|---------------------------|
| `irq_init_done`        | `init_engine.END` step                       | One-cycle pulse           |
| `irq_init_error`       | `init_engine.INIT_ERROR` state               | Latched until CSR-cleared |
| `irq_overflow`         | OR of queue overflow, refresh miss, rddata timeout | Latched               |

IRQs assert in the `mc_clk` domain. The SoC's interrupt controller is responsible for any re-synchronization to its own clock if different.

## Software Response Patterns

### Init Failure

```c
void handle_init_error_irq(void) {
    uint32_t s = apb_read(STATUS);
    uint8_t step = STATUS_INIT_STEP_DBG(s);

    log_error("DRAM init failed at step %d", step);

    // Inspect step-specific telemetry
    switch (step) {
        case INIT_STEP_WAIT_DFI_INIT_COMPLETE:
            log_error("PHY init did not complete — check PHY config");
            break;
        case INIT_STEP_ZQ_CAL:
            log_error("ZQ calibration failed — check VDDQ supply, board impedance");
            break;
        case INIT_STEP_MRS_LOAD:
            log_error("MRS load failed — verify CSR-loaded MR values");
            break;
        // ... more cases per step table ...
    }

    // Clear the latched error
    apb_write(STATUS, STATUS_INIT_ERROR_CLEAR);   // W1C semantics

    // Attempt re-init
    apb_write(CTRL, CTRL_INIT_FORCE_RESTART);
}
```

### AXI Queue Overflow

```c
void handle_overflow_irq(void) {
    uint32_t s = apb_read(STATUS);
    uint32_t pulses = apb_read(TXN_QUEUE_FULL_PULSES);

    log_warn("AXI queue overflow: %u pulses", pulses);

    // Read the high-water threshold and current depth
    uint32_t sched = apb_read(SCHED_TUNING);
    log_warn("High-water threshold: %u, current depth: %u",
             (sched >> 16) & 0xFF, STATUS_TXN_QUEUE_OCC(s));

    // Mitigation: drop the high-water threshold to backpressure earlier
    sched = (sched & ~0xFF0000) | ((current_depth - 4) << 16);
    apb_write(SCHED_TUNING, sched);
    apb_write(CTRL, CTRL_CONFIG_APPLY);
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED));
}
```

### Refresh Deadline Miss

```c
void handle_refresh_miss(void) {
    uint32_t owed = apb_read(REFRESH_PENDING_MAX);
    log_error("Refresh deadline missed; owed = %u", owed);

    // Inspect refresh manager state
    uint32_t state = STATUS_REFRESH_MGR_STATE(apb_read(STATUS));
    log_error("Refresh FSM stuck in state %u", state);

    // Mitigation: temporarily disable batching to catch up
    uint32_t v = apb_read(REFRESH_TUNING);
    v = (v & ~REFRESH_DEFER_ACTIVE_MASK) | REFRESH_DEFER_ACTIVE(1);
    apb_write(REFRESH_TUNING, v);
    apb_write(CTRL, CTRL_CONFIG_APPLY);
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED));

    // After catch-up, optionally re-enable batching
}
```

## STATUS_HISTORY for Bring-Up

The `STATUS_HISTORY` register captures the last 8 power-state transitions (4 bits each). Useful when the controller is oscillating between states (e.g., entering and exiting APD repeatedly):

```c
void dump_state_history(void) {
    uint32_t hist = apb_read(STATUS_HISTORY);
    for (int i = 0; i < 8; i++) {
        uint8_t state = (hist >> (i * 4)) & 0xF;
        log_info("State[-%d]: %s", i, power_state_name(state));
    }
}
```

This is more useful than polling current state — it captures fast transitions that polling would miss.

## Diagnostic Sequence for Suspected Bug

```
1. Read STATUS.init_done (must be 1)
2. Read STATUS.power_state (should be ACTIVE)
3. Read STATUS_HISTORY (look for oscillation)
4. Read STATUS.txn_queue_occ + STATUS.refresh_pending_max (check for backlog)
5. Read OBS_AXI_R_LATENCY_P99 (tail latency telemetry)
6. Read OBS_ROW_HIT_RANK<R>_BANK<N> (per-bank traffic distribution)
7. Read OBS_REF_LATENCY_RANK<R>_BANK<N> (per-bank refresh fairness)
8. Check IRQ status; clear and re-arm if needed
```

This is the bring-up team's first-pass diagnostic flow.

## Soft Reset vs. Re-Init

`CTRL.soft_reset` (bit 31 of `CTRL`) asserts an internal soft reset that re-clears all FUB state without affecting the CSR contents. Use this when the controller is in an inconsistent state but the software's CSR config is correct:

```c
void soft_reset(void) {
    apb_write(CTRL, CTRL_SOFT_RESET);
    // Self-clearing; wait a few cycles
    for (int i = 0; i < 16; i++) asm volatile("nop");

    // Re-trigger init (CSRs are preserved)
    apb_write(CTRL, CTRL_INIT_START);
}
```

For hard cases (silicon bug, persistent failure), the SoC PMU should drive the asynchronous reset and software should re-bring-up from scratch.

## Open Questions / Future Work

- **Per-rank error reporting.** When a fault is localized to one rank (signal integrity, board fault), it would be useful to report which rank. Currently the IRQs are channel-wide. v2 enhancement.
- **Error histogram.** A short rolling history of recent errors (last 16) would help post-mortem analysis. Costs CSR area; punt.
- **Auto-recovery vs. report-only.** The controller could auto-recover from some errors (e.g., refresh deadline miss → drop batching automatically). Currently report-only; software must intervene.
