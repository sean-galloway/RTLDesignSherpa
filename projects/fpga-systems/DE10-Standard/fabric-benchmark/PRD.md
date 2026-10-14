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

**[← Back to fabric-benchmark](README.md)**

# DE10-Standard Fabric Benchmark — PRD

**Version:** 0.3 (draft) · **Date:** 2026-10-11 · **Status:** collateral-blocked
(Quartus/Platform Designer IP intake pending; bring-up unblocked when available)

## 1. Purpose

Measure, on one piece of silicon and one mirrored pair of traffic patterns,
what two AXI fabrics cost and what they deliver:

- **Leg A — bridge:** the RTL Design Sherpa bridge generator's crossbar
  (AXI3 ports, delivered under sean-galloway/RTLDesignSherpa#97).
- **Leg B — Intel fabric:** the Platform Designer (Qsys) AXI interconnect.

**The workload — two mirror-image flavors (both legs, bit-identical):**

- **Flavor 1 — fill, then drain:** the write injector fills main memory
  with pseudo-random data (through the fabric and the hard MC). `stream`
  then moves it all from main memory across the fabric into the
  CRC-checker SRAM.
- **Flavor 2 — mirror image:** `stream` reads data from a pseudo-random
  data slave and writes it all to main memory across the fabric.

The flavors are mirror images and should tell the same story. Running both
checks that they do: fabric and memory-controller behavior should be
direction-symmetric, and any asymmetry the two flavors surface (arbitration,
MC read/write turnaround, data-path differences) is itself a result. The
scenario library in §4.1 extends the same mirror-discipline to contention,
addressing, transients, and integrity.

Two comparison axes: **size of design** and **performance**. Everything
else — device, HPS, memory controller, stream datapath, CRC checker, SRAMs,
obs blocks, injector, PRBS slave, driver, clocks — is held constant.

## 2. Background

The site teaches fabric design with generated crossbars (see the bridge
HAS/MAS and the interconnect literature in
`projects/components/fabric-gen-ip/bridge/references/`). A fair question a
reader should be able to see answered with data: against the vendor's own
interconnect on the same device, with the same masters and slaves, what does
a generated crossbar cost in logic and fmax, and what bandwidth/latency does
it actually deliver? The DE10-Standard (Cyclone V SoC, hard DDR3 controller
in the HPS) is the vehicle: the Intel memory controller is the constant
anchor both fabrics must reach through. The Cyclone V HPS FPGA-facing ports
are AXI3, which is why the AXI3 converters and the bridge's AXI3 port
support (#96/#97) exist.

## 3. Definitions and constants

| Held constant (both legs) | Value / source |
| --- | --- |
| Board / device | Terasic DE10-Standard, Cyclone V 5CSXFC6D6F31C8 |
| Toolchain | Quartus Prime 24.1 Standard (`/home/seang/intelFPGA_lite/24.1std`) |
| HPS + hard memory controller | Intel DDR3 MC via HPS; identical HPS config both legs |
| Clock plan | One fabric clock domain (single clock, same frequency both legs) |
| Write injector | PRBS payload fill master (repo `axi4_master_wr_injector` family), same config both legs; AXI3 adaptation per leg identical |
| Pseudo-random data slave | PRBS responder slave (stream test-slave family; exact block chosen at M2) |
| Movers | `stream` (the measured mover in both flavors); JTAG-AXI master as driver/diagnostics; any second master identical across legs |
| Slaves | CRC-checker block with its SRAM (stream's), PRBS slave, obs register file |
| obs blocks | Identical observer/monitor RTL on the datapath, same probe points both legs |
| Traffic | Identical driver scripts, transaction counts, burst sequences, PRBS seeds |

| The one variable | Leg A | Leg B |
| --- | --- | --- |
| The fabric between masters and slaves | Bridge-generated crossbar (`protocol = "axi3"` both sides) | Platform Designer AXI3 interconnect |

Matching rule: Leg A's bridge config (TOML) mirrors the PD system's topology
— same master/slave count, same data widths, same ID widths, same address
map. No wider or fancier bridge than the PD fabric it replaces. Any PD
feature with no bridge equivalent (e.g. default slave, topology display) is
matched functionally or documented as a difference.

## 4. Benchmark definition

### 4.1 Workloads (performance axis)

**v1 execution scope** — the headline sweep runs on W1-F1 and W1-F2: burst
length {4, 8, 16, 32, 64 beats} × outstanding transactions {1, 2, 4, 8},
fixed measurement window, N = 5 runs.

- **W1-F1 — fill then drain (headline):** the write injector fills a fixed
  DDR3 region with PRBS data through the fabric+MC (setup phase; timed and
  reported separately — it is the write-direction datapoint), then `stream`
  copies the whole region from DRAM across the fabric into the CRC-checker
  SRAM (the headline read-direction measurement).
- **W1-F2 — mirror image:** `stream` reads the full working set from the
  PRBS data slave across the fabric and writes it to a fixed DDR3 region
  through the MC. Read direction from the slave, write direction into DRAM:
  the mirror of W1-F1's drain.
- **W2 — SRAM ↔ SRAM across the fabric:** loopback between two stream SRAM
  regions; removes DRAM/MC variance to expose fabric-only behavior. This is
  the control that attributes any W1 asymmetry (fabric vs MC).
- **W3 — Contention pair (F3 / F3-mirror):** stream drains DRAM→CRC while
  the injector concurrently fills a *different* DRAM region (concurrent
  R+W through the arbiters and MC); the mirror run swaps the roles.
  Sweep: mix {50/50, 90/10} × outstanding {2, 4}. **Story:** per-master
  bandwidth shares should be symmetric under role-swap; asymmetry isolates
  arbitration bias in the fabric vs read-priority scheduling in the MC.

**Scenario library** — adopted with this PRD; all reuse the fixed cast and
all carry a mirror check. Scheduling follows milestone appetite; data lands
in `data/` under the same conventions as v1.

| Scenario | Mirror partner | The story it should tell |
| --- | --- | --- |
| **B1 — Burst-knee curve** | both flavors | Efficiency vs burst length at fixed total bytes; the saturation knee per leg, and the same knee in both flavors |
| **B2 — Address-stride sweep** | both flavors | Row-interleaved vs blocked vs strided access (stream's existing address generators); the fabric adds no order-sensitivity, and legs track across strides |
| **B3 — Hot-region saturation** | — (single, but percentile tails are the check) | Latency percentiles under full saturation of one bank/region; arbitration jitter exposed by the tail |
| **B4 — Cold vs warm transients** | idle durations {1 µs, 1 ms, 10 ms} | First-transaction latency after idle vs steady-state; pipeline/skid depth visible as the size-vs-latency trade |
| **C1 — F2 readback verify** | F1's drain CRC | After W1-F2 writes DRAM, stream reads it back into the CRC checker — closes the integrity loop so **both** flavors end in a CRC verdict |
| **C2 — Seed-swap sanity pair** | F1 ↔ F2 seeds | Same entropy, different data; results are data-independent |

**v1.x stretch** (reuse the cast; schedule after the library): D1 — hours-long
alternating F1/F2 soak with obs tracking BW/latency drift over time; E1 —
unmapped-address probe (DECERR latency, PD default slave vs bridge
subtractive slave); E2 — unaligned burst starts (both legs carry aligners;
measure the penalty).

**Deferred:** A2 — backpressure pair (slow sink, then slow source). Tells
the sustained-backpressure story, but needs one small RTL knob (a pace
throttle on the PRBS slave / CRC sink); revisit after v1.

### 4.2 Metrics — performance

Measured by the **obs blocks** (identical RTL and probe points both legs),
read out through the same register path:

- Sustained bandwidth (MB/s) per sweep point, per flavor; efficiency vs the
  DDR3/theoretical ceiling.
- Latency distribution (p50 / p95 / p99) for the measured transaction
  windows, idle and under load.
- Mirror agreement: W1-F1 vs W1-F2 (and F3 vs F3-mirror) bandwidth and
  latency at matched sweep points; divergence investigated and explained
  (with W2 as the fabric/MC attributor).
- Under W3: per-master bandwidth share (arbitration fairness) and latency
  inflation; role-swap symmetry.
- Integrity: CRC verdicts at the end of every flavor run (C1 closes the
  loop for F2).

### 4.3 Metrics — size of design

From Quartus, same seeds/effort/SDC both legs:

- ALMs (and the logic vs register split), FFs, M10K blocks and bits, DSPs
  (expected zero).
- fmax from TimeQuest on the fabric-clocking scheme (same target strategy
  both legs; report achieved and the failing-path story if a leg misses).
- Compile wall-clock; per-hierarchy resource extraction for the fabric
  instance where the flow allows.

Delivered as raw Fitter/TimeQuest report parses (CSV in `data/`) and a
normalized delta table (% difference, Leg A vs Leg B).

### 4.4 Methodology rules

- Same Quartus version, device, pin/clock constraints, and SDC.
- Same driver scripts and transaction streams both legs (scripted via
  System Console + JTAG-AXI; identical TCL, identical counts, identical
  PRBS seeds both flavors and both legs).
- Warm-up excluded: measurements taken over a fixed steady-state window;
  the W1-F1 fill phase is timed separately from the drain measurement.
- N = 5 runs per point; report median and spread.
- No hand-tuning a leg's constraints to win; constraint files are shared.

## 5. Architecture sketch

![DE10-Standard fabric benchmark (planned)](docs/assets/graphviz/de10_fabric_benchmark_planned.png)

- **Flavor 1:** injector -> DRAM, then stream -> CRC SRAM.
- **Flavor 2:** PRBS slave -> stream -> DRAM, then C1 readback -> CRC SRAM.
- **F3 pair:** stream drain + injector fill (the roles swap in the mirror).

Leg A assembles from: bridge generator config TOML → generated crossbar SV →
thin wrapper top; obs probes instantiated at the same net names as Leg B.
Leg B assembles from Platform Designer; the same `stream`/obs/CRC/injector/
PRBS-slave RTL is wired in as PD components or exported-conduit hookups. The
obs register file is reachable from the JTAG-AXI master on both legs at the
same addresses.

## 6. Deliverables

1. `quartus/` — two compilable Quartus projects (Leg A, Leg B).
2. `rtl/` — bridge TOML(s), wrapper tops, obs hookup notes.
3. `scripts/` — System Console/JTAG-AXI driver TCL, report-to-CSV parsers.
4. `data/` — measurement CSVs per leg per scenario/flavor per run date.
5. `docs/` — analysis document (standard doc flow → PDF): headline size
   table + performance tables (both flavors) + mirror-agreement verdicts +
   honest caveats (driver ceilings, topology differences, single-device
   scope).

## 7. Milestones

| M | Content | Blocked by |
| --- | --- | --- |
| M0 | Collateral intake: PD IP inventory, JTAG-AXI master availability in 24.1 std, HPS DDR3 config for this board, f2h/h2f/ACP widths | external download |
| M1 | Leg B (Intel PD) bring-up: compiles, JTAG-AXI loopback, sanity counters | M0 |
| M2 | Block selection: exact PRBS slave block from stream's inventory; injector/obs plumbing; W1-F1/W1-F2/W2/W3 scripted on one leg | M1 |
| M3 | Leg A (bridge) bring-up: matched-topology TOML, compiles, same driver passes all v1 scenarios | M2 |
| M4 | Measurements: v1 sweep (both flavors + W3) ×5 runs; scenario-library runs as appetite allows; Fitter/TimeQuest parses | M3 |
| M5 | Analysis doc + site write-up (incl. mirror-agreement verdicts) | M4 |

Note the order: Intel leg first. The PD flow is the unknown; the bridge leg
is deterministic given a matched topology.

## 8. Success criteria

- Both legs fit and run on the DE10-Standard with the identical driver.
- Headline tables delivered: size delta and performance delta, Leg A vs Leg
  B, at matched topology, for both flavors.
- **Mirror agreement:** W1-F1 and W1-F2 (and F3 vs F3-mirror) tell the same
  story within measurement spread at matched sweep points, or every
  divergence is explained in the analysis.
- Every flavor run ends in a CRC verdict (C1 makes this true for F2).
- A third party can re-run the campaign from `scripts/` + this PRD alone.

## 9. Non-goals (v1)

Other topologies/NoC; ACP comparisons; multi-clock/CDC comparisons; power;
Linux userspace benchmarking (System Console + bare JTAG-AXI only); AXI5;
write-only or read-only DRAM microbenches beyond the two flavors (extend in
v2 if the mirror check surprises); backpressure pacing (A2 deferred).

## 10. Risks

| Risk | Mitigation |
| --- | --- |
| JTAG-AXI bandwidth ceiling caps the performance axis | Also drive W1 from an HPS-side master; if the driver saturates first, report "at-driver-saturation" figures and say so plainly |
| HPS boot complexity (MC needs HPS configuration) | Use the vendor reference boot flow from the collateral; bare-metal preloader if Linux is overkill |
| PD leg emits features the bridge can't match | Match functionally or document as a difference in the analysis; never let Leg A exceed Leg B's configured capability |
| Leg A fmax below Leg B on Cyclone V (different RAM inference styles) | Report achieved fmax at the shared clock target plus a best-effort column; the comparison is primarily at-equal-clock |
| Mirror flavors disagree (real asymmetry) | That is a finding, not a failure: localize with W2 (fabric-only) vs W1 (with MC) to attribute the asymmetry |
| Scenario-library scope creeps past milestone appetite | Library is explicitly appetite-scheduled; v1 exit criteria only cover F1/F2/W2/W3 |
| Quartus 24.1 std device/IP gaps for 5CSX | M0 verifies before any build work |

## 11. Open questions (resolve at M0/M2)

- Exact HPS DDR3 part/timing config shipped with the board collateral.
- f2h_axi_slave / h2f_axi_master / ACP data widths on the DE10-Standard
  (64-bit everywhere?) — fixes the bridge TOML widths.
- JTAG-AXI master component availability and its practical bandwidth.
- Whether System Console scripting in 24.1 std needs any license feature.
- PD interconnect default configuration knobs worth matching (pipeline
  stages, arbitration) so Leg A's bridge config is a fair mirror.
- M2: exact PRBS responder block from stream's `rtl/fub` inventory for the
  Flavor-2 source slave (and the matching CRC-verification hook, per C1).

## 12. References

- Dally & Towles, *Principles and Practices of Interconnection Networks*
  (Morgan Kaufmann, 2004) — router/interconnect cost model framing; already
  in `projects/components/fabric-gen-ip/bridge/references/README.md`.
- Terasic DE10-Standard user manual and Intel Cyclone V HPS documentation —
  bibliographic entries to be added at M0 from the downloaded collateral.
- Bridge HAS/MAS (`projects/components/fabric-gen-ip/bridge/docs/`) — Leg A
  capabilities and configuration surface.
- `projects/fpga-systems/Genesys2/dma-ip/stream/` — the stream blocks, obs
  infrastructure, and perf-build conventions this campaign reuses.
