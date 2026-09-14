# DDR2 Bandwidth Measurement — Methodology Reference

**Scope:** an AXI4-attached DDR2 memory controller and its PHY, driving a real
device. Written against pumice on the Nexys A7 (MT47H64M16, x16, DDR2-300, BL4,
75 MHz controller clock, 64-bit AXI) but the definitions are design-independent;
only the worked numbers are specific.

**Purpose:** settle what "bandwidth" and "efficiency" mean for a memory
controller before any number is published, enumerate the candidate denominators,
and name the primary plus complementary pair to report. The companion document
[DMA_UTILIZATION_MEASUREMENT](../../../../Genesys2/stream/docs/DMA_UTILIZATION_MEASUREMENT.md)
does the same job for the STREAM DMA, and this one deliberately mirrors its
shape so the two areas argue about efficiency in the same vocabulary.

---

## 1. Why this matters more for DRAM than for a datapath

A DMA moving SRAM to SRAM has one real denominator: the bus could have carried a
beat every cycle, and did not. A DRAM controller has at least four, because the
DRAM protocol itself burns cycles that no controller can recover:

- **Activate and precharge.** Opening a row costs tRCD before a column access,
  closing it costs tRP. On a page miss the data pins are idle through both.
- **Refresh.** tRFC every tREFI is stolen from every requester, forever. It is
  not overhead the controller introduced and not overhead it can remove.
- **Bus turnaround.** A read following a write costs tWTR; the reverse costs
  tRTW. A 50/50 mix pays this constantly and a read-only stream never does.
- **Burst granularity.** BL4 on a x16 device is 8 bytes per burst. A requester
  asking for less still pays for the whole burst.

So a controller can be flawless and still deliver well under half the pin rate,
and a controller can look excellent on one access pattern and terrible on
another without a line of RTL changing. Quoting a single number without saying
which denominator it used, and on which pattern, is not a measurement.

The two failure modes are the same as anywhere:

- **Overstatement.** Report data-bus occupancy during a page-hit streaming
  workload and you get a number near the pin rate that no real workload sees.
- **Understatement.** Report end-to-end payload on a single short burst and
  every fixed cost — activate, first-word latency, refresh — is charged to a
  handful of bytes.

---

## 2. Candidate definitions

Listed from highest-reported to most-honest. None is universally correct; the
choice depends on the question.

### 2.1 Pin rate (peak, theoretical)

- **Definition:** data-bus width times transfer rate. At the AXI boundary here,
  8 bytes at 75 MHz = **600 MB/s**. At the DRAM pins, 2 bytes at 300 MT/s = the
  same 600 MB/s, which is the point of the gearing.
- **Excludes:** everything. No activate, no refresh, no turnaround, no protocol.
- **Answers:** "what is the ceiling?"
- **Reports:** by construction, 100%.

This is the number on the box. It belongs in a report exactly once, as the
reference line every other number is drawn against. Never as a result.

### 2.2 Data-bus occupancy

- **Start event:** first data beat of the run on the measured channel.
- **End event:** last data beat of the run.
- **Excludes:** command-bus activity, and any dead time before the first beat or
  after the last.
- **Includes:** activate, precharge and refresh stalls that happen *between*
  beats, since they fall inside the window.
- **Answers:** "once the controller is streaming, how full are the data pins?"

The cleanest measure of the controller's scheduling. It is also the number that
flatters a page-hit workload most, because a row-major walk inside one page
never pays an activate after the first.

### 2.3 AXI datapath utilization (the four buckets)

- **Definition:** of the cycles in the window, the fraction in which the
  measured AXI data channel completed a beat.
- **Instrumented directly** by `axi_bus_meter`, which classifies every cycle
  into exactly one of four buckets:

| Bucket | Meaning | What a rise tells you |
|--------|---------|-----------------------|
| productive | a beat completed | — |
| backpressure | source had data, sink was not ready | the controller could not accept: DRAM-bound |
| starvation | sink was ready, source had no data | the requester did not ask: generator-bound |
| idle | neither side active | the run is not the limiter; the window is too wide |

: The four-bucket cycle classification

- **Answers:** "where did the cycles go, and whose fault was it?"

This is the diagnostic definition. Its value is not the percentage, it is that
backpressure and starvation point in opposite directions, so a bandwidth
shortfall becomes a named cause rather than a disappointment.

### 2.4 Useful payload, end to end

- **Start event:** the requester's first command is accepted.
- **End event:** the last response retires — the final `RLAST` for reads, the
  final `B` for writes. Not the last data beat.
- **Excludes:** nothing inside the run. Includes every activate, every refresh,
  every turnaround, and the latency of the first and last transactions.
- **Answers:** "what did the requester actually get?"

This is the honest system-level number and the one an architect budgeting
bandwidth should be handed. On this board, with the read return ring at 64,
reads reach **571.3 MB/s** and writes **570.2 MB/s**, which is 95% of the
600 MB/s pin rate under a page-friendly pattern at a burst length long enough to
amortize the activate.

---

## 3. What this harness instruments

| Quantity | Source | Notes |
|----------|--------|-------|
| Per-direction window | harness timer `w_first`/`w_last`, `r_first`/`r_last` | latched at that engine's own first and last beat |
| Cycle classification | `axi_bus_meter` productive / backpressure / starvation / idle | one bucket per cycle, per direction |
| Latency distribution | `axi_perf_latency_hist`, log2 bins | AR to first R, and AR to RLAST |
| Transactions returned | read histogram total | compared against what was programmed |
| Data integrity | per-generator CRC, plus mismatched-beat count | writer and reader compute independently |

: Instrumentation available at the AXI boundary

Everything is measured on the AXI wires between the generators and the
controller, so a number describes the controller plus PHY plus device as one
unit. Nothing here sees inside the DRAM.

---

## 4. Choosing the window, and the trap in it

**Use the per-engine hardware stamps, not a host clock, and not a shared timer.**

Two specific errors, both of which have produced wrong numbers in this area:

- **Host wall clock.** Programming an engine is dozens of UART register writes.
  A window that starts when the host says "go" and ends when it observes "done"
  measures the UART. Every figure in a report must come from on-chip counters.
- **A timer that stops on both directions.** This harness's global timer stops
  only when write done AND read done are both asserted. In a single-direction
  phase it therefore free-runs, or stops on a stale done left by the other
  direction. The per-engine `first`/`last` stamps are latched by that engine
  alone and are the only correct window for a one-direction measurement. For a
  concurrent run the bus window is `max(last) - min(first)` across both.

Guard the result: if the counter window and the hardware span disagree by more
than about 2x, the measurement is dominated by something outside the run and the
number should be flagged rather than published.

---

## 5. Recommended primary plus complementary pair

For external reporting:

- **Primary:** useful payload end to end (2.4), as MB/s and as a percentage of
  the pin rate (2.1).
- **Complementary:** AXI datapath utilization (2.3), with the four-bucket
  breakdown beside it.

Report the pair, and show the gap between them:

```
Pin rate (reference):                600.0 MB/s     100%
End-to-end payload (primary):        571.3 MB/s    95.2%
Datapath productive (complementary):                  --
```

The first two lines are measured. The third is available from the bus meters
per run and belongs here beside them.

**The attribution below it is NOT yet measurable, and should not be published
until it is.** A breakdown of the missing percent into refresh, activate,
turnaround and first-transaction latency is the natural next line of that block
and is what a reader will want, but nothing in the present instrumentation can
separate those causes: the four buckets say the controller did not accept a
beat, not why. Writing a plausible split would be inventing data. Either add a
stall-cause counter in the controller or leave the line out.

What the pair does support today is a direction. A large gap with low
backpressure means the controller sat idle waiting for the requester; a large
gap with high backpressure means the DRAM is the wall. Those call for opposite
fixes, and distinguishing them needs no new hardware.

For internal debugging, invert the emphasis: lead with the four buckets per
bank and the latency histogram, and treat bandwidth as the summary.

---

## 6. Workload axes

Bandwidth is a function of the workload, not a property of the controller. Fix
these and state them, or the number cannot be reproduced.

| Axis | Why it matters |
|------|----------------|
| Burst length (AxLEN) | Short bursts cannot amortize activate or hide latency; long bursts flatter every number |
| Outstanding transactions | Bandwidth is bounded by outstanding x AxLEN / (latency + AxLEN); see §8 |
| Inter-burst gap | Injected idle separates "the controller is the limit" from "the requester is" |
| Access order | Page-hit (row-major) versus page-miss (column-major) can differ by 2x or more |
| Bank parallelism | Generators on distinct banks let activates overlap; on one bank they serialize |
| Read/write mix | A mixed stream pays turnaround that neither pure direction does |
| Page policy | Open-page rewards locality, closed-page rewards scatter; the winner depends entirely on the pattern |
| Refresh mode | Fixed cost, but when it lands relative to a burst changes the variance |
| Controller clock | Every MB/s figure scales with it. Read it from the board; never assert it |

: Workload axes that must be stated alongside any bandwidth number

A single bandwidth number without these axes specified is not reproducible.

---

## 7. Known measurement pitfalls

Each of these has produced a wrong or misleading number in this area.

- **Confusing efficiency with speed.** A controller can be at 100% data-bus
  occupancy and still be slow, because the requester is not asking for enough.
  Efficiency and bandwidth are different questions; report both.
- **Latency masquerading as a scheduler problem.** Read bandwidth here was once
  attributed to the arbiter when it was Little's law: with 8 outstanding reads
  at 49 cycles of latency, short bursts simply cannot fill the pipe. Compute the
  bound before blaming the design (§8).
- **An address hash that wraps differently than the DRAM.** If the expected data
  is a function of the pre-wrap address and the device wraps physically, every
  access past the top of the device "mismatches" without anything being wrong.
  Wrap the generated address at the device boundary.
- **A seed that changes between the write and the read.** Expected data is a
  function of address AND seed. A per-scenario seed invalidates any fill that
  preceded it, and the failure looks exactly like corruption.
- **Counter saturation.** A 16-bit cycle counter wraps at 65536. A long run
  silently reports a small number. Check for saturation and say so rather than
  publishing the wrapped value.
- **Field widths that silently truncate the sweep.** The inter-burst gap here is
  four bits. Asking for 16 programs 0 and re-measures the back-to-back case
  under a different label.
- **Assuming both directions did the same work.** In a concurrent run it is
  natural to compute one bandwidth and print it twice. Measure each direction on
  its own window; if they differ, one was starved and that is the finding.
- **Trusting programmed byte counts.** Bandwidth is bytes over time, and the
  bytes are assumed. Compare the transactions the bus actually returned against
  what was programmed; if they disagree the MB/s is fiction.
- **Assuming the points of a sweep are independent.** They are not, if any point
  can leave memory in a wrong state. A point that corrupts cells is inherited by
  every later point that reads the same region, and the inherited damage is
  reported as the later point's own result. This is not hypothetical: it made
  the first `bank_gap_sweep` run unreadable (PUMICE-037). Re-fill before every
  point unless you are deliberately studying accumulation.
- **A constant repeated across runs is stale state, not a race.** A race varies.
  When `row_major g1` reported an identical 3694 mismatched beats at eight
  consecutive gaps, that count was the previous family's damage being re-read
  eight times — the points themselves were clean. Confirmed by a later point
  reporting exactly the mismatch count audited into that bank beforehand. The
  same reasoning inverts usefully: a figure that varies run to run is a race,
  and one that does not is state you carried in.
- **Reading only generator 0.** The mismatch counter is per reader. A sweep that
  calls `beats_mismatched()` with no argument verifies one of four readers and
  silently reports the other three as clean. Sum across the active engines.
- **Checking correctness only where you happened to read.** Writers and readers
  on disjoint banks means nobody ever verifies the writers' banks. A defect can
  sit there for a whole run and only appear when some later configuration
  happens to place a reader on a bank that earlier points wrote — which is
  exactly how PUMICE-037 surfaced, at the very last block of a 192-point sweep.
  Audit the whole device, not just the read side.

---

## 8. The bounds worth checking a number against

A measurement is only interesting relative to a model. Three are cheap to
compute and between them explain most shortfalls.

**Little's law, for reads.** The pipe holds `outstanding x AxLEN` beats and each
takes `latency + AxLEN` cycles to traverse:

```
beats/cycle  =  min( outstanding x AxLEN / (latency + AxLEN),  peak_fraction )
```

The knee is at roughly `latency / AxLEN` outstanding transactions — about 49 at
AxLEN 1 and 13 at AxLEN 4 for this board's ~49-cycle read latency. Measuring
above the knee tells you about the DRAM; measuring below it tells you about your
own request rate. A sweep that never reaches the knee has measured the harness.

**Bank parallelism.** With `n` generators on distinct banks, activates on
different banks overlap, so the activate cost is divided by `n` until tFAW or the
command bus binds. On one bank they serialize completely. The gap between the
one-bank and n-bank curves is the parallelism the controller actually extracts,
as opposed to the parallelism the device offers.

**Refresh.** `tRFC / tREFI` is lost unconditionally. It sets a ceiling below the
pin rate that no scheduling can recover, and it should be drawn on the chart as
a second reference line under the pin rate so nobody spends a week chasing it.

---

## 9. Reporting checklist

Before a bandwidth number leaves this area:

1. The denominator is named (§2) and the pin rate is quoted beside it.
2. The window came from on-chip stamps, and the counter and hardware spans agree.
3. Every workload axis in §6 is stated.
4. Data integrity passed — a fast wrong answer is not a result.
5. The transactions returned match the transactions programmed.
6. The number is placed against at least one bound from §8.
7. The clock was read from the board, not assumed.
