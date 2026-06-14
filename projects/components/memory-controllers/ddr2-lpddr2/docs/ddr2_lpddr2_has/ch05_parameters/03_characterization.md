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

# Characterization Knobs

A subset of the build-time parameters is intentionally left configurable for **characterization sweeping**. These are the algorithmic choices that have research-backed alternatives where the best choice depends on workload. Rather than baking in a one-size-fits-all default, we expose them as parameters so the verification plan can sweep them on representative AXI traffic and pick defaults from data.

## Characterization Parameters

| Parameter                  | Choices                                  | Recommended default          | Rationale                                                                                  |
|----------------------------|------------------------------------------|------------------------------|--------------------------------------------------------------------------------------------|
| `LOOKAHEAD_DEPTH`          | 0 / 1 / 2 / 4                            | 1                            | Same-bank lookahead window for **exact** auto-precharge decisions when the next same-bank request is already in the queue (typical for streaming / DMA). Falls back to `PAGE_POLICY` when the queue is shallow. 0 disables; 2 or 4 buys diminishing returns at modest comparator cost. |
| `PAGE_POLICY`              | `OPEN` / `CLOSE` / `HAPPY_HYBRID`        | `HAPPY_HYBRID` (LPDDR2), `OPEN` (DDR2) | Fallback for when lookahead is inconclusive. Streaming workloads favor `OPEN`; mobile-mixed favors `HAPPY_HYBRID`. Ghasempour 2015 reports near-optimal accuracy with small storage. |
| `PAGE_PREDICTOR_TABLE_BITS`| 8 – 16                                   | 12                           | 4 KB predictor is sufficient for typical mobile workloads. Larger tables marginal improvement. |
| `REFPB_POLICY`             | `ROUND_ROBIN` / `OLDEST_FIRST` / `DARP`  | `DARP`                       | Chang HPCA 2014: DARP wins over round-robin on uneven bank activity (real workloads).      |
| `REFRESH_DEFER_MAX`        | 1 – 8                                    | 8 (JEDEC ceiling)            | Stuecheli MICRO 2010: deferring up to 8 maximizes Elastic Refresh benefit. Set to 1 for real-time predictability. |
| `TXN_QUEUE_DEPTH`          | 4 – 64                                   | 16                           | Larger queues help bandwidth on multi-master AXI; smaller queues reduce area.              |
| `AGE_MAX`                  | 32 – 1024                                | 256                          | Caps FR-FCFS starvation; larger values let row-hits dominate longer at the cost of tail latency. |
| `N_PHASES`                 | 1 / 2 / 4                                | depends on PHY               | 4 typical for FPGA SoCs; 2 for slower mobile platforms; 1 for simulation-only.             |
| `ADDR_MAP_SCHEME`          | ROW_MAJOR / BANK_INTERLEAVE / XOR_HASH   | ROW_MAJOR                    | Default works for streaming; BANK_INTERLEAVE for random; XOR_HASH for adversarial.         |

## Sweep Plan

The verification plan (see §6.4) includes a characterization sweep that runs each parameter through its choices on a small benchmark suite:

### Benchmark Suite

A key open question for the sweep is the **interaction between `LOOKAHEAD_DEPTH` and `PAGE_POLICY`**. With deep queues and conclusive lookahead, the choice of `PAGE_POLICY` barely matters because the fallback rarely fires. With shallow queues, `PAGE_POLICY` dominates. The sweep matrix should cover both extremes.

| Workload          | Pattern                                                                            |
|-------------------|------------------------------------------------------------------------------------|
| `stream-read`     | Sequential 4 KB read bursts                                                        |
| `stream-write`    | Sequential 4 KB write bursts                                                       |
| `stream-mixed`    | Interleaved sequential read and write                                              |
| `random-narrow`   | Random small AXI bursts (1–4 beats)                                                |
| `random-wide`     | Random large AXI bursts (16–64 beats)                                              |
| `mobile-mixed`    | Bursty traffic with periodic large writes (modeled on smartphone GPU + display)    |
| `multi-master`    | Two AXI masters issuing concurrent traffic with different patterns                 |

### Metrics Collected

For each (workload, parameter) combination, the sweep records:

- **Sustained read bandwidth** (% peak)
- **Sustained write bandwidth** (% peak)
- **Average read latency**
- **99th-percentile read latency**
- **Refresh blocking time** (% of cycles where the bus was blocked by refresh)
- **Row-hit rate** (per-bank, averaged)
- **Refresh deferral utilization** (avg `refresh_pending` over time)

### Default Selection

After the sweep, each parameter's default is set to the value that:

1. Maximizes sustained bandwidth across the benchmark suite
2. Subject to: 99th-percentile latency does not regress by more than 20%
3. Subject to: area cost is within budget

The defaults shown in the parameter table above are the **expected** outcomes based on the cited research. The actual defaults will be confirmed by the sweep.

## Runtime Overrides via CSR

Some characterization parameters are also accessible at runtime via CSR (see §6.3). This allows in-system tuning without rebuild:

- `PAGE_POLICY` runtime override
- `REFPB_POLICY` runtime override
- Page predictor warm-up cycles and hysteresis

Runtime overrides take effect at the next "quiet point" (no commands in flight). The SoC is responsible for ensuring no DRAM traffic during the transition.

## Observability for Sweep

The CSR exposes the following observation counters (described in §6.3):

- Per-bank row-hit count
- Average refresh latency
- Max transaction queue depth
- Page-predictor accuracy (HAPPY mode)
- Refresh deferral histogram

These feed back into the sweep tool for in-loop default selection.
