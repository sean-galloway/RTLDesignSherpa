# DMA Utilization Measurement — Methodology Reference

**Scope:** scatter-gather, multi-channel, AXI-Stream DMA engine moving data between SRAM endpoints.
**Purpose:** establish a common vocabulary for utilization measurement, enumerate the candidate definitions, and propose a primary + complementary reporting pair. Final choice should be validated against the engine's actual microarchitecture by the design-side agent.

---

## 1. Why this matters

"Utilization" is not a single number. Different start/end events yield numbers that can differ by 10–20 percentage points on the same engine running the same workload. Choosing the wrong definition produces one of two failure modes:

- **Marketing-grade overstatement** — measuring only the steady-state data phase hides real overhead the rest of the system pays for. Customers and architects making bandwidth budgets get a number that doesn't match what they observe.
- **Pessimistic understatement** — measuring end-to-end including one-time setup costs on a single short descriptor exaggerates overhead that would amortize away on a realistic workload.

The remedy is to define the window precisely, report what's included, and ideally publish two complementary numbers so the reader can see where overhead is going.

---

## 2. Candidate definitions

Listed from highest-reported to most-honest. None is universally "correct" — the choice depends on what question is being answered.

### 2.1 Burst-only / steady-state utilization

- **Start event:** first beat of the first data burst leaves the DMA on the destination interface
  (AXI-Stream: first `TVALID && TREADY` after warmup; AXI-MM write: first `WVALID && WREADY`)
- **End event:** last beat of the last data burst
  (AXI-Stream: final `TVALID && TREADY && TLAST`; AXI-MM write: final `WVALID && WREADY && WLAST`)
- **Excludes:** descriptor fetch, address-phase latency on first burst, write-response drain, channel arbitration setup, completion signaling
- **Answers:** "Does the datapath have internal bubbles once warmed up?"
- **Reports:** typically 95–99% in well-designed SRAM↔SRAM engines

This is the cleanest measure of the data engine itself. It is also the number vendors prefer to publish without saying so.

### 2.2 Per-descriptor utilization

- **Start event:** descriptor parsed, first data beat issued for that descriptor
- **End event:** completion event for that descriptor (last data beat or write-response, depending on interface)
- **Excludes:** descriptor fetch, inter-descriptor gaps, channel arbitration between descriptors
- **Answers:** "How efficiently does the engine execute one unit of work?"

Common in academic papers because it isolates the engine's per-transfer behavior from system-level effects. Hides multi-descriptor and multi-channel costs.

### 2.3 End-to-end transfer utilization

- **Start event:** "go" command latched, or first descriptor-fetch transaction issued by the engine
- **End event:** completion event visible to the rest of the system. Candidate end events in order of strictness:
  1. Last data beat written to destination (`WVALID && WREADY && WLAST` of the final descriptor)
  2. Last write-response from destination (`BVALID && BREADY` of the final write)
  3. Status writeback completed (B response for the writeback transaction)
  4. Completion descriptor posted to completion queue / doorbell asserted
  5. Interrupt asserted to host
- **Includes:** descriptor fetch, address phase, data phase, write-response drain, completion signaling — everything between "go" and "done"
- **Answers:** "How long does it actually take to move N bytes, soup to nuts?"

This is the system-architect-relevant number. Use #2 (last B response) as the default end event for a typical engineering report; software-visible measurements may need #4 or #5.

### 2.4 Sustained-rate (PMU window) utilization

- **Start event:** programmable performance counter starts at an arbitrary cycle
- **End event:** counter stops at a later arbitrary cycle
- **Measurement:** `productive_beats × bus_width / (window_cycles × bus_width × num_channels)`
- **Includes:** everything that happens inside the window — descriptor chains, idle gaps, multi-channel arbitration, backpressure
- **Answers:** "What fraction of theoretical bandwidth does this engine deliver under realistic workloads?"

Closest to what an end customer observes. Best for steady-state characterization across long workloads. Requires careful workload design to be meaningful.

---

## 3. AXI-Stream signal-level instrumentation

For an AXI-Stream destination interface, the four cycle classifications are:

| Condition | Meaning | Bucket |
|-----------|---------|--------|
| `TVALID && TREADY` | Productive beat — data delivered | `productive_cycles` |
| `TVALID && !TREADY` | DMA wants to send, downstream stalls | `backpressure_cycles` |
| `!TVALID && TREADY` | Downstream ready, DMA not producing | `starvation_cycles` |
| `!TVALID && !TREADY` | Both sides idle | `idle_cycles` |

Sum of the four equals total elapsed cycles in the measurement window.

### 3.1 Diagnostic interpretation

- High `backpressure_cycles` → destination is the bottleneck. SRAM port contention, downstream FIFO full, or write-response credit exhaustion.
- High `starvation_cycles` → DMA is the bottleneck. Descriptor-fetch on critical path, address-phase latency, channel arbitration bubbles, or upstream source starved.
- High `idle_cycles` between bursts → inter-descriptor gap. Indicates serial descriptor fetch without prefetch.

### 3.2 Per-channel vs. aggregate

For multi-channel engines, instrument both:

- **Per-channel counters** — diagnose which channel is starved, backpressured, or under-utilized
- **Aggregate counters** — capture total engine throughput across all channels

The two together reveal whether the engine is bandwidth-limited (aggregate saturated, channels balanced) or arbitration-limited (channels imbalanced, aggregate below sum-of-channel-bandwidths).

### 3.3 Source-side instrumentation

Mirror the same four-bucket classification on the source-side AXI-Stream interface. Cross-correlating source and destination buckets distinguishes:

- Source starvation propagating to destination (`!TVALID && TREADY` on both)
- Destination backpressure propagating to source (`TVALID && !TREADY` on both)
- DMA-internal bubble (`TVALID && TREADY` on source, idle on destination, or vice versa) — indicates internal pipeline depth or FIFO depth issues

---

## 4. Recommended instrumentation block

Per channel, plus one aggregate set:

```
// Window control
start_cycle_q             // latched cycle counter at start_event
end_cycle_q               // latched cycle counter at end_event
window_active_q           // 1 while measurement window is open

// Cycle counters (free-running while window_active)
productive_cycles_q       // (valid && ready)
backpressure_cycles_q     // (valid && !ready)
starvation_cycles_q       // (!valid && ready)
idle_cycles_q             // (!valid && !ready)

// Transaction counters
descriptor_count_q        // descriptors completed
burst_count_q             // AXI bursts issued (if MM destination)
beat_count_q              // productive beats (same as productive_cycles for stream)
bytes_count_q             // beats × bytes_per_beat, accounting for TKEEP/TSTRB

// Latency histograms (optional, valuable)
descriptor_fetch_latency  // AR-issued to first data beat available
first_beat_latency        // descriptor accepted to first TVALID
last_beat_to_done_latency // last TLAST to completion event
```

Expose via APB or AXI-Lite CSR. Software computes utilization flavors from these primitives — measurement *policy* lives in software, measurement *mechanism* lives in hardware. This separation lets the same RTL support multiple reporting conventions without redesign.

### 4.1 Start/end event selection

Make start and end events configurable rather than hard-coded:

```
start_event_sel[2:0]:
  3'b000 : go-bit asserted (CSR write)
  3'b001 : first descriptor-fetch AR issued
  3'b010 : first descriptor accepted into engine
  3'b011 : first productive beat (TVALID && TREADY)
  3'b100 : external trigger pin

end_event_sel[2:0]:
  3'b000 : last productive beat (TVALID && TREADY && TLAST)
  3'b001 : final write-response received (BVALID && BREADY)
  3'b010 : status writeback completed
  3'b011 : completion descriptor posted
  3'b100 : interrupt asserted
  3'b101 : external trigger pin
```

Same RTL, multiple reporting flavors, controlled by software at runtime.

### 4.2 Implementation status (RFC Stage E option 2 — IMPLEMENTED, in-core)

The instrumentation in Sections 3-4 is now realized **in the STREAM core itself**,
read back over the regblock perf CSRs (no MonBus packets). The legacy
characterization-harness `axi_bus_meter` blocks (CSRs at `HARNESS_CSR_BASE +
0x100`/`0x180`) have been **retired** — datapath utilization is now sourced from
the in-core monitors. Equivalence was proven in cosim (the in-core per-channel
meter matched the harness meter bit-for-bit before retirement).

Measurement mechanism, by stage:

- **Aggregate four buckets + beat/byte/burst counts** (Section 3): two
  `axi4_master_rd_mon` / `axi4_master_wr_mon` instances on the data-read R bus
  and data-write W bus. CSRs `RDMON_PERF_*` @ `0x300`, `WRMON_PERF_*` @ `0x330`
  (PROD/BP/STARV/IDLE + WINDOW_CYCLES + BEAT/BYTE/BURST).
- **Per-channel buckets** (Section 3.2): in-core `axi_bus_meter` per bus, keyed
  by `rid` (read) / the write-engine active-channel sideband (write). Indexed
  readout: write `PERF_CH_SEL.CH_SEL` (@ `0x35C`), read the packed
  `RD/WRMON_PERF_CH_PROD_BP` / `_STARV_IDLE` (@ `0x360`-`0x36C`) and the
  all-channel overflow masks (`0x370`/`0x374`).
- **Latency histograms** (Section 4, "optional, valuable"): `axi_perf_latency_hist`
  per bus — read AR->first-R + AR->RLAST, write AW->B — binned into 16 log2
  bins. Indexed readout: `HIST_SEL{BUS,METRIC,BIN}` (@ `0x378`), `HIST_DATA`
  (@ `0x37C`), `HIST_TOTAL` (@ `0x380`, = per-metric transaction count).

**Window control** (Section 4.1): the perf window is driven by the
`RD/WRMON_PERF_CTRL.RUN` bits in **trigger mode** (`start/end_event_sel=000`):
write `RUN=1` to clear+open the window, run the workload, write `RUN=0` to
close/freeze, then read the counters. The rising edge of `RUN` clears the
aggregate buckets, per-channel meter, and histograms in lockstep. The host
(`read_rw_perf.py`; `read_bus_meters.py` is now a compatibility shim) opens the
window before the kick and closes it the instant the workload completes;
`datapath_utilization` additionally uses the harness timer's exact first/last
beat span as a methodology denominator. `WINDOW_CYCLES` is a live-only counter
the monitor zeroes at close, so the authoritative closed-window length is the
sum of the four buckets (which hold after close).

---

## 5. Recommended primary + complementary pair

For external reporting (datasheets, architect-facing characterization):

- **Primary:** End-to-end utilization (definition 2.3, end event = final B response or completion signal). This is the honest system-level number.
- **Complementary:** Datapath utilization (definition 2.1, burst-only window). This shows what the engine is capable of when not paying setup/teardown cost.

Report as a pair with the delta explicitly called out:

```
Datapath utilization (steady-state):     96.3%
End-to-end utilization (incl. overhead): 87.1%
Overhead breakdown:
  Descriptor fetch (first descriptor): 4.8%
  Address phase + first-beat latency:  1.2%
  Write-response drain (final B):      2.2%
  Inter-descriptor gaps:               4.0%
```

The delta is itself a quality signal — it quantifies how much benefit aggressive descriptor prefetch and completion pipelining would yield.

For internal microarchitecture debugging:

- **Primary:** Datapath utilization, broken down per channel
- **Diagnostic:** Backpressure / starvation / idle cycle breakdown per channel
- **Diagnostic:** Latency histograms for descriptor fetch and first-beat

---

## 6. Test workload considerations

Measurements are sensitive to workload shape. Document these axes alongside any reported number:

| Axis | Why it matters |
|------|----------------|
| Descriptor count | Single descriptor exposes setup cost; long chain amortizes it |
| Descriptor size (bytes) | Large descriptors flatter datapath utilization; small expose overhead |
| Channel count active | Single-channel hides arbitration cost; many-channel exposes it |
| Source/destination alignment | Misaligned transfers split into smaller bursts, lose efficiency |
| Backpressure profile | Always-ready destination hides flow-control overhead |
| Descriptor location (SRAM vs DRAM) | DRAM-resident descriptors expose fetch latency |
| Descriptor prefetch depth | Affects whether non-first descriptors hide their fetch cost |

A characterization report should fix all of these and state them explicitly. A single utilization number without these axes specified is not reproducible.

---

## 7. Known measurement pitfalls

- **Counting cycles where the engine is committed but not productive.** A DMA waiting on a `BREADY` from a slow downstream may show low productive-beat count but high "engine-busy" cycles. Don't conflate "engine busy" with "engine productive."
- **Including reset / configuration cycles.** Start the window after the engine is in its operational state, not at power-on.
- **Bus-width mismatch.** If the destination is narrower than the source (or vice versa), utilization-by-beats and utilization-by-bytes diverge. Report bytes, and state the reference bus width.
- **TKEEP / TSTRB in partial beats.** A beat with only some valid bytes counts as one productive cycle but transfers less than the full bus width. Bytes-based utilization handles this correctly; beats-based does not.
- **Last-beat ambiguity.** Some designs assert `TLAST` on a beat with no productive data (e.g., end-of-frame marker). Decide whether that beat counts.
- **Clock-domain crossings inside the engine.** If counters live in a different domain than the interface they measure, sample-accurate measurement requires careful synchronizer design or per-domain counters with later merge.

---

## 8. Open questions for the design-side agent

The choices below depend on engine-specific microarchitecture. The system-side methodology above is independent of these but the *numbers* will depend on them.

1. **Descriptor prefetch depth.** How many descriptors can the engine hold in-flight? This determines how quickly the first-descriptor fetch cost amortizes. If prefetch depth is ≥2, only the very first descriptor in a chain exposes fetch latency.
2. **Completion pipelining.** Can the engine begin descriptor N+1's data phase while descriptor N's write-response is still draining? If yes, the inter-descriptor gap collapses and end-to-end approaches datapath utilization.
3. **Per-channel arbitration policy.** Round-robin, weighted-RR, strict-priority, or credit-based? Affects starvation_cycles distribution across channels.
4. **Outstanding-transaction limits.** How many AW/AR can be in flight? If less than `(round-trip latency × bandwidth / burst-size)`, the destination interface will have bubbles regardless of engine quality.
5. **Source/destination FIFO sizing.** Determines tolerance to transient backpressure without stalling the source-side handshake.
6. **Status writeback semantics.** Does the engine write status to memory before, after, or in parallel with the final data write? Affects which end event is appropriate.

These should be answered before settling on the measurement window definition, because the right definition follows the engine's actual completion semantics.

---

## 9. Proposed next steps

1. **Design-side agent** to confirm prefetch depth, completion pipelining behavior, and which end-event (data-last vs B-last vs writeback vs IRQ) the engine treats as "transfer complete" from a software perspective.
2. **Add instrumentation block** per Section 4 — DONE (in-core, RFC Stage E
   option 2; see Section 4.2). Configurable start/end events per Section 4.1 are
   implemented as the `RD/WRMON_PERF_CTRL.RUN` trigger-mode window.
3. **Run characterization sweep** across the workload axes in Section 6. Report primary + complementary pair per Section 5 at each operating point.
4. **Decision point** on whether to publish (a) only end-to-end, (b) only datapath, or (c) both with overhead breakdown. Recommended: (c), for the reasons in Section 5.

---

*This document is methodology-only. Specific cycle counts, latency targets, and design parameters belong in the engine's characterization report, which depends on the answers to Section 8.*
