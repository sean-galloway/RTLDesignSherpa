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

# Design Note: Kick/Flow Separation, Injection-FIFO Sizing, Deadlock Obligations, and Model Measurability

**Status:** explored 2026-10-13 (owner: "let's explore this" × 2 + "what is this")
**Companion:** [HIVE Reference Library](../references.md) §2 (network-processor
queueing), §1 (interconnect theory), §5 (ESL modeling)

---

## 1. Kick scheduling vs flow pacing (the NP-queueing idea, pinned down)

**What HIVE-C schedules is the kick.** A descriptor *chain* (next-ptr linked,
scatter-gather) is admitted to a priority queue; the scheduler decides when
each chain is kicked and to which RAPIDS channel. After the kick, **RAPIDS'
producer/consumer flow control paces execution** — producer and consumer
endpoints (cells, memory) synchronize through hardware handshakes on flags
in memory. So the queueing discipline applies to *kick admission*, not to
per-beat pacing:

- HIVE-C = admission control + kick ordering (deficit round-robin within a
  level, aging promotion, channel-aware S2MM arming).
- RAPIDS HW = rate control per kicked chain (producer/consumer flag pacing).

This maps onto the network-processor literature (Franklin et al., *Network
Processor Design*): the NP schedules packet *launches*; the line hardware
paces transmission. Steal from that book: deficit round-robin with quantum
per level for kick fairness, and per-channel arming state as the analog of
flow state.

**Design consequence:** the scheduler firmware needs a *kick queue* per
priority level whose entries are chains, not individual descriptors —
MAX_INFLIGHT bounds armed chains, not beats.

## 2. Injection-FIFO depth analysis (credit/queueing, not rule-of-thumb)

MAS §1.2 sets command depth 2 and uplink depth 4 per SERV. Framework to
justify or revise, per Dally & Towles ch. on flow control:

**Sizing rule (Little's law + sync latency):** a FIFO must hold enough
entries to (a) cover the round-trip until consumer backpressure propagates
through the CDC sync, and (b) absorb the burstiness of the arrival process
at the target overflow probability.

- **(a) Sync cover:** the write side keeps accepting while the read-side
  pointer crosses (2-flop sync, same-frequency PoC clocks ≈ 2–3 cycles).
  Depth 2 = sync cover + 1 in flight. Depth 4 (uplink) adds margin for the
  arbiter's non-preemptive grant latency.
- **(b) Burst math:** steady-state uplink load ρ is tiny (16 SERVs × 1
  report/1000 cycles + alerts ≈ 0.02 of line rate) — M/M/1 waiting ≈ ρ/(1−ρ)
  ≈ 0.02 frames. Overflow risk is *correlated bursts*, not steady load: a
  congestion event makes one SERV alert repeatedly while its periodic report
  also lands. Model as M/M/1/b with burst intensity β (alerts per event);
  P(overflow) ≈ ρ_b^b with ρ_b the burst-window occupancy. For b = 4 and a
  10-alert burst window, P(overflow) < 10⁻³ — depth 4 is comfortable; b = 2
  on the command path is the tight one and deserves the measurement below.

**Obligation to close the loop:** the observation bus already exports
fifo full/empty flags (MAS ch5). Add to the ctrl_network testplan a
*traffic-characterization* pass: run the testplan scenarios, record arrival
and service processes from the waveforms, and either confirm the depths or
revise them with measured ρ and β. Until then the depths stand as
"analytically plausible, empirically unconfirmed" — said honestly in the MAS.

## 3. Deadlock-freedom proof obligations

**Today (delta as crossbar):** a crossbar has no routing loops — deadlock-free
by construction. The obligation is only to keep it that way: assert no
credit loops are ever added without a return-path proof.

**Cell's 3-D QoS-routed fabric (write these before the fabric):** per Duato's
theory, a routing function is deadlock-free when its channel-dependency
graph is acyclic, or when an escape resource exists under a restricted
acyclic routing function. **Requirement context (owner 2026-10-13):** a
single cell has only N connections, and N-cell paths can form loops — and
the fabric must support **dynamic re-routing** when a cell hangs or latency
grows too high. Adaptive routing is precisely where naive loop-avoidance
breaks: an adaptive function that detours around a hung cell can reintroduce
cycles unless the escape-resource conditions hold for the adaptive paths
too (fully-adaptive-with-escape-channel is Duato's canonical safe pattern).
Detection needs a per-cell heartbeat/watchdog, and a re-route must ride the
quiesce/reconfigure discipline HIVE already owns (HAS §5.4) — fault handling
reuses the context-switch machinery rather than inventing a new one. The
obligations, concretely:

1. **Routing restriction:** dimension-ordered (X→Y→Z), no backtracking.
   *Property:* at every router, a packet's coordinates are monotonic per
   hop; the next-hop dimension is the current or the next in order. (SVA,
   each router ingress.)
2. **Escape resource:** at least one VC per port routed by the restricted
   function; QoS classes and **adaptive detours** may not bypass the escape
   VC while blocked. *Property:* a packet holding non-escape resources can
   always eventually acquire the escape VC — under the base routing
   function **and** under every detour the adaptive policy can select.
3. **Credit progress:** credits return on wires independent of data;
   *Property:* credit occupancy is bounded and strictly decreasing when the
   downstream drains (no credit cycles).
4. **Memory-flag channels:** the producer/consumer flag handshake must make
   forward progress — *Property:* a flag set is eventually observed
   (bounded flag latency), else the flag channel itself deadlocks.

**Where they live:** the property inventory joins the HAS ch7-style formal
table; the SVA goes into the delta/cell `formal/` areas when the fabric
lands; and a directed sim sweep (uniform + tornado + hotspot traffic under
assertions) becomes part of the fabric's testplan. Rationale: writing the
restrictions first is what turns "deadlock-free by design" from a hope into
a checked obligation — and it is exactly the class of property the repo's
formal area exists to teach.

## 4. TLM discipline — what it is and why ±10% needs it

**What it is:** transaction-level modeling (Bailey & Martin's ESL book is
the methodology source) models *transactions*, not cycles. A descriptor
kick is a transaction with an arrival time, a service time at each resource
(HIVE-C queue, injection FIFO, fabric traversal, RAPIDS engine,
producer/consumer pacing), and a completion time. The model is a network of
timed queues.

**Why the HAS's ±10% target is unfalsifiable without it:** ER-1.1 says the
SimPy models must predict hardware within ±10%. You can only check that if
model and RTL measure *the same thing at the same points*. The discipline:

1. **Same workload:** one workload definition (a descriptor-chain trace)
   drives both the model and the RTL testbench.
2. **Same observation points:** the model timestamps transactions at the
   observation-bus boundaries (MAS ch5); the RTL testbench measures at the
   same signals. HIVE already defines those points — the model just has to
   use them.
3. **Measured service times:** service-time distributions come *from* RTL
   runs (the Phase-1 tests already log handshake latencies), not from
   imagination.
4. **Comparison on distributions:** compare latency percentiles
   (median, P99) model vs RTL under workload W; within 10% = requirement met.

Without these four rules you get an honest-but-vague model and a
cycle-accurate RTL run measuring different quantities — the ±10% claim
becomes untestable. With them, ER-1.1 is an executable check in CI.
