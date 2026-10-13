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

# HIVE-C Firmware Architecture

HIVE-C runs bare-metal RV32IM firmware. The architecture below is the
reference structure; module boundaries are a firmware convention, not an RTL
constraint.

```
main.c              - Initialization and main loop
  ├── rapids_mgr.c  - DMA descriptor management
  ├── config_mgr.c  - Network reconfiguration
  ├── stats_mgr.c   - Performance monitoring aggregation
  ├── interrupt.c   - IRQ handlers (RAPIDS completion, SERV alerts)
  └── host_if.c     - UART/AXI4-Lite command interface
```

: HIVE-C firmware module structure

**Responsibilities by module:**

| Module | Responsibility |
|--------|----------------|
| `main.c` | Hardware init, context load, main loop |
| `rapids_mgr.c` | Descriptor pool, batching, channel-aware S2MM programming |
| `config_mgr.c` | Context selection, quiesce/activate orchestration |
| `stats_mgr.c` | SERV status collection, congestion policy, performance model updates |
| `interrupt.c` | RAPIDS completion, SERV alert routing, error handling |
| `host_if.c` | Command parsing, response formatting, firmware load support |

: Firmware module responsibilities

## Main Loop

```c
void hive_main_loop(void) {
    init_hardware();
    load_network_config(CONTEXT_MESH); // Start in mesh mode (Context 1)

    while (1) {
        if (host_command_pending()) {
            handle_host_command();
        }
        if (timer_expired(STATS_INTERVAL)) {
            collect_serv_statistics();
            update_performance_model();
        }
        if (congestion_detected()) {
            adaptive_route_balancing();
        }
        if (rapids_ready() && desc_queue_has_work()) {
            issue_descriptor_batch(MAX_INFLIGHT);
        }
        if (irq_pending()) {
            process_interrupts();
        }
    }
}
```

The loop is poll-plus-interrupt: fast paths (descriptor issue) poll, slow
paths (statistics, host commands) share the same iteration. No RTOS; latency
comes from staying in this loop.

## Descriptor Injection API

```c
// Inject one 256-bit CDA descriptor toward RAPIDS (virtual tile 16).
// Blocks until the AXIS master accepts the beat.
void inject_descriptor(const descriptor_t *desc);
```

`inject_descriptor` is the single path by which descriptors reach RAPIDS —
firmware never writes RAPIDS descriptor registers directly. The injection
firmware sets `tuser = PKT_CDA`, `tdest = 16`, and waits for `tready`.

## Interrupts

| Source | Signal | Handler action |
|--------|--------|----------------|
| RAPIDS | Descriptor completion | Bookkeeping, next-batch issue |
| RAPIDS | Error | Log, halt or degrade per policy |
| SERV (via control network) | Congestion alert | Policy decision: throttle, reroute, or context switch |
| SERV (via control network) | Error notification | Mark tile, notify host |
| Host interface | Command ready | Wake command parser |

: HIVE-C interrupt inventory

---

**Last Updated:** 2026-10-12
