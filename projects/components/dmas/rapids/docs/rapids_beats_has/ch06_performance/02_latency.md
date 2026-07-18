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

# Latency Characteristics

Latency is dominated by the one-time pipeline fill from a channel kick to the
first data beat. Once running, both paths sustain the throughput of Section 6.1;
control descriptors add a bounded synchronization delay.

## Latency Components

### Kick-to-First-Beat Breakdown

| Stage | Typical Cycles (100 MHz) | Notes |
|-------|--------------------------|-------|
| Kick decode (APB / kick window) | 2-4 | Descriptor address latched |
| Descriptor fetch (AXI read, 256-bit) | AXI read latency + 1 | Overlapped by prefetch on chains |
| Descriptor parse | 1-2 | Opcode + fields decoded |
| SRAM fill (sink) / AXI read issue (source) | AXI/AXIS latency | First beat into the buffer |
| First beat out | 1-2 | Drain to memory (sink) / AXIS (source) |

### Total Latency Formula

```
L_first_beat  =  L_kick + L_desc_fetch + L_parse + L_pipeline_fill
```

`L_desc_fetch` is hidden on chained descriptors when the descriptor engine has
prefetched the next descriptor (`DESCENG_CONFIG.PREFETCH_EN`).

---

## First-Beat Latency

The dominant term is the memory/network round trip to fill the pipeline. For a
sink transfer the first AXIS beat must arrive and be buffered before the first
AXI write can drain; for a source transfer the first AXI read must return before
the first AXIS egress beat. After the first beat the pipeline is full and
throughput is bandwidth-bound, not latency-bound.

---

## Control-Descriptor Latency

Control descriptors are latency, not throughput (Section 6.1):

| Opcode | Latency |
|--------|---------|
| `CTRL_WRITE` (doorbell) | One single-beat AXI write: AW->W->B round trip |
| `CTRL_READ` (gate) | One poll per retry (AXI read + compare); retries paced by `tick_1us`, up to `CTRL_CONFIG.CTRLRD_MAX_TRY` (default 16, max 511) |

A `CTRL_READ` gate blocks its descriptor (and the chain) until the polled value
matches. The retry budget bounds the worst case: an unsatisfied gate cannot hang
the channel -- after `CTRLRD_MAX_TRY` polls the engine raises `ctrlrd_error`
instead of waiting forever.

---

## Latency Variability

### Sources of Variability

- Memory read latency (descriptor fetch, source reads) and write-response timing.
- AXIS backpressure (`s_axis_tready` / `m_axis_tready`) on the network end.
- Multi-channel arbitration for the shared AXI master.
- `CTRL_READ` retry count when a gate is not yet satisfied.

### Worst-Case Latency

Bounded by: memory timeout (`SCHED_TIMEOUT_CYCLES` / `SCHED_TIMEOUT_LIMIT`
escalation on the scheduler side) and the control-read retry budget
(`CTRL_CONFIG.CTRLRD_MAX_TRY`). Both convert an otherwise-unbounded wait into a
reported error so a channel is never permanently stalled.

---

## Latency Optimization

### Software Recommendations

- Chain descriptors so the descriptor engine prefetches the next while the
  current transfers (hides `L_desc_fetch`).
- Keep the AXIS consumer/producer ready to avoid backpressure stalls.
- Size `CTRL_READ` gates so the expected value is already (or soon) present to
  minimize poll retries.

### Hardware Configuration

- Adequate `SRAM_DEPTH` so the buffer covers memory/network latency without
  stalling.
- Tune `AXI_XFER_CONFIG` (RD/WR beats, ALLOC/DRAIN) so bursts amortize AXI setup.

---

**Last Updated:** 2026-07-13
