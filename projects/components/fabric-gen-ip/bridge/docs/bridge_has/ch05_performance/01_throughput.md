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

# Throughput Characteristics

## Overview

What the fabric can move when everything goes right, and what eats into that number when it doesn't. The short version: bursts and matched widths win; conversions and contention cost you.

## Functional Description

### Peak Throughput

One master driving one slave — no contention, no conversion:

| Data Width | Frequency | Peak Throughput |
|------------|-----------|-----------------|
| 32-bit | 100 MHz | 400 MB/s |
| 64-bit | 100 MHz | 800 MB/s |
| 128-bit | 100 MHz | 1.6 GB/s |
| 256-bit | 100 MHz | 3.2 GB/s |
| 512-bit | 100 MHz | 6.4 GB/s |

: Peak Throughput by Data Width

### Formula

```
Peak Throughput = DATA_WIDTH (bits) × Frequency (Hz) / 8 bytes/bit
```

### Measured (2026-09-11)

`bridge_2x2_rw` (two 32-bit AXI4 masters, two 32-bit AXI4 slaves, no width
or protocol conversion), 16-beat INCR bursts, every BFM channel back-to-back,
each figure computed over its own window from the first to the last beat at
the port named. `test_bridge_2x2_rw_perf` asserts a floor under every row,
so a change that costs bandwidth fails there instead of ageing this table.

| Traffic | Where measured | Beats / cycle | Notes |
|---|---|---|---|
| One master streaming reads | R at the master port | **1.00** | 128 bursts, 2048 beats in 2048 cycles |
| One master streaming writes | W at the slave port | **0.89-0.90** | 0 cycles of WREADY low at the master port: the ~2-cycle gap per burst is the requester re-arming W between bursts, not the fabric |
| Two masters streaming writes to one slave | W at the shared slave port | **1.00** | the port stays full; the other master's beats fill the gaps above |
| -- per-master share of the contended window | W at each master port | **0.499 / 0.501** | 128 bursts each (0.475 / 0.525 at 8 bursts: round-robin, window-length effects only) |
| Two masters to two different slaves | W at both slave ports | **1.78-1.80** | two independent paths; neither slows the other |

: Measured throughput, direct 32-bit AXI4 paths

So the formula above holds for this fabric: a saturated port moves one beat
per cycle, two masters on one port split it evenly, and paths to different
slaves do not share anything. The write-stream row is the requester's figure,
not the bridge's -- the contention row is the bridge's.

The current performance tests measure throughput floors under uniform-style
patterns; a full saturation study (accepted traffic vs. applied load, latency
vs. offered load) is tracked as bridge vault TASK-014.

### On Silicon: the Genesys 2 Fabric Benchmark (2026-10-16)

The fabric benchmark (`projects/fpga-systems/Genesys2/fabric-benchmark`,
PRD §8) compares a generated bridge, `bridge_fb_data`, with the Xilinx AXI
Crossbar and SmartConnect. All three use the same port set and the same
harness on the same board, at 128 bits and 100 MHz, with only the fabric
instance changed. Every figure is the mean of 5 runs. Peak is 1525.9 MiB/s,
one direction.

| Measure | Bridge | AXI Crossbar | SmartConnect |
|---|---:|---:|---:|
| One DMA, 8 ch x 4 x 1 MB, MiB/s | 1525.8 | 1525.8 | 1525.8 |
| One DMA, 1 ch x 4 x 4 KB, MiB/s | 1416.6 | 1420.7 | 1358.5 |
| Two writers into one slave, both full rate, writer B limited to 4 outstanding: B's share | 50.0% | 50.0% | 20.0% |
| The same, writer B limited to 2 outstanding: B's share | 50.0% | 50.0% | 11.1% |

: The bridge against the vendor fabrics on the Genesys 2

In steady state the bridge costs no bandwidth, and its per-transfer
overhead matches the Xilinx crossbar. Under contention it splits a slave as
evenly as the crossbar, and more evenly than SmartConnect.

The 2-outstanding case was not at parity when the benchmark first ran
(2026-10-16): the bridge gave that writer 40% of the slave. The arbiter
then picked from the raw requests into a 2-deep AW stage in front of the
slave. The board's DDR controller (LiteDRAM) accepts an AW only once that
burst's write data is in its buffer, so the stage stayed full of AWs that
had already been granted. Each slot that freed went to whichever master
had an AW waiting at that moment, which was almost always the 8-channel
DMA and seldom the writer between bursts. Arbitrating at the slave pins
from per-master request slots, with nothing queued past the pick (bridge
commit 73467609f, 2026-10-17), removed it. A board bisect over the leg's
history confirms the step at that commit (40.0% before, 50.0% from it on),
and the current bridge gives 50.0% in five identical runs.

The fabric is also larger than the crossbar, and now about as fast. Placed
and routed alone, out of context on the Genesys 2's part (2026-10-22), the
bridge is 8,449 LUTs and 6,722 flops with an estimated Fmax of ~250 MHz
(-0.001 ns at 4 ns); the AXI Crossbar is 2,688 LUTs and 2,190 flops at ~256
MHz; SmartConnect is 8,333 LUTs, 3,959 LUTRAM and 11,616 flops at ~268 MHz.
The bridge was ~179 MHz on 2026-10-16, with the slave-side CAMs that W12
later removed; re-measured without them it was ~239 MHz, and two timing
edits to `bridge_id_remap` (write the lowest free entry unconditionally;
`req_ok` as one flat reduction) gave the rest. Its worst path is 7 levels,
from a master's AW skid through the remap ID compare into a slave's AW
stage. Most of the size difference is the default of a registered stage
on every channel at both ends of every port, which the crossbar there does
not have. All three close at the board's 100 MHz.

### Factors Affecting Throughput

| Factor | Impact | Mitigation |
|--------|--------|------------|
| Arbitration contention | Reduces per-master throughput | Increase slave ports |
| Width conversion | the narrow side's full rate; +4 to +12 cycles of read latency (measured below) | Match widths where latency matters |
| Protocol conversion | 2+ cycles for APB | Use AXI4 for high-bandwidth |
| Response routing | Minimal (pipelined) | N/A |

: Factors Affecting Throughput

### Width-Converted Paths (measured)

`test_bridge_4x4_rw_width_perf` (GitHub #119 L4): one master to one slave of
`bridge_4x4_rw` at a time, 16-beat bursts at the master's natural size,
16 bursts per direction, every word checked. Rates are beats per `aclk`
cycle at each port. Read latency is the idle first beat, AR handshake to the
first R handshake at the master port.

| Path | Master → slave | Master W | Slave W | Master R | Slave R | Ideal (master) | Read latency (cycles) |
|---|---|---:|---:|---:|---:|---:|---:|
| matched | 64b → 64b | 0.895 | 0.895 | 1.000 | 1.000 | 1.000 | 5 |
| upsize 4:1 | 32b → 128b | 0.895 | 0.226 | 0.945 | 0.259 | 1.000 | 9 |
| upsize 4:1 | 64b → 256b | 0.895 | 0.226 | 0.945 | 0.259 | 1.000 | 9 |
| downsize 2:1 | 64b → 32b | 0.498 | 0.972 | 0.501 | 1.000 | 0.500 | 11 |
| downsize 8:1 | 256b → 32b | 0.128 | 0.993 | 0.125 | 1.000 | 0.125 | 17 |

: Width-converted paths, bridge_4x4_rw (FULL level)

Every path runs at its narrower side's full rate: an upsize moves a master
beat per cycle, a downsize keeps the narrow slave busy every cycle. The
0.895 write figure is the requester BFM's own gap between bursts; the same
figure appears on the matched path. Conversion costs read latency: +4 cycles
upsizing, +6 at 2:1 and +12 at 8:1 downsizing. A downsize has to gather a
whole wide beat before the first one goes back.

### Latency Against Offered Load (measured)

`test_bridge_2x2_rw_load` (GitHub #119 L4): open loop, a master starts one
4-beat read to ddr every `gap` cycles regardless of completions. Latency is
from the call to the last beat at the requester, so it includes queueing in
the requester. Peak at the ddr port is 1 beat per cycle.

| Traffic | Gap | Offered (beats/cycle) | Accepted | Mean latency | p95 latency |
|---|---:|---:|---:|---:|---:|
| cpu alone | 16 | 0.250 | 0.258 | 10.0 | 10 |
| cpu alone | 8 | 0.500 | 0.511 | 10.0 | 10 |
| cpu alone | 5 | 0.800 | 0.807 | 10.0 | 10 |
| cpu alone | 4 | 1.000 | 1.000 | 10.0 | 10 |
| cpu alone | 3 | 1.333 | 1.000 | 21.5 | 31 |
| cpu alone | 2 | 2.000 | 1.000 | 41.8 | 52 |
| cpu + dma | 16 | 0.500 | 0.511 | 12.0 | 14 |
| cpu + dma | 8 | 1.000 | 1.000 | 12.0 | 14 |
| cpu + dma | 6 | 1.333 | 1.000 | 35.0 | 56 |
| cpu + dma | 4 | 2.000 | 1.000 | 58.0 | 98 |
| cpu + dma | 2 | 4.000 | 1.000 | 108.4 | 174 |

: Accepted throughput and latency against offered load, bridge_2x2_rw (GATE level, 24 reads per master per point)

Accepted equals offered up to the slave's one beat per cycle and holds there
past it. Latency is flat until saturation (10 cycles alone, 12 with two
masters contending for the same slave), then grows with the queue. The
fabric adds no queueing of its own below saturation. (Accepted reads a
little above offered at light load because the window runs first beat to
last.)

### Traffic Patterns Against Offered Load (measured)

`test_bridge_perf_patterns` (bridge TASK-014) drives three traffic patterns
open loop -- every `gap` cycles each master starts one 4-beat read at the
slave the pattern names -- and records accepted throughput against offered
load, in slave beats per cycle summed over the targeted ports, with each
master's mean and p95 latency (call to last beat at the requester, so the
requester's own queue counts once the port's outstanding limit binds).
`capacity` is what the targeted ports can absorb: the sum over slaves of
min(offered at that slave, 1.0). Uniform random traffic is the benign
pattern (Dally & Towles ch. 3); permutation (every master at a different
slave) and hot-spot (every master at one slave) are the ones that expose
allocation and buffering. GATE runs three load points, FUNC and FULL the
curve.

| Pattern | Gap | Offered | Capacity | Accepted | cpu mean / p95 | dma mean / p95 |
|---|---:|---:|---:|---:|---:|---:|
| uniform | 32 | 0.250 | 0.250 | 0.259 | 10.0 / 10 | 14.0 / 14 |
| uniform | 8 | 1.000 | 1.000 | 1.021 | 10.0 / 10 | 14.0 / 14 |
| uniform | 5 | 1.600 | 1.600 | 1.613 | 10.0 / 10 | 14.0 / 14 |
| uniform | 4 | 2.000 | 2.000 | 2.000 | 10.0 / 10 | 14.0 / 14 |
| uniform | 3 | 2.667 | 2.000 | 1.610 | 57.0 / 99 | 62.0 / 104 |
| uniform | 2 | 4.000 | 2.000 | 1.345 | 159.0 / 188 | 157.8 / 194 |
| permutation | 32 | 0.250 | 0.250 | 0.255 | 10.0 / 10 | 10.0 / 10 |
| permutation | 8 | 1.000 | 1.000 | 1.011 | 10.0 / 10 | 10.0 / 10 |
| permutation | 4 | 2.000 | 2.000 | 2.000 | 10.0 / 10 | 10.0 / 10 |
| permutation | 3 | 2.667 | 2.000 | 2.000 | 33.5 / 54 | 33.5 / 54 |
| permutation | 2 | 4.000 | 2.000 | 2.000 | 95.1 / 123 | 90.2 / 115 |
| hot-spot | 32 | 0.250 | 0.250 | 0.254 | 10.0 / 10 | 14.0 / 14 |
| hot-spot | 8 | 1.000 | 1.000 | 1.000 | 10.0 / 10 | 14.0 / 14 |
| hot-spot | 6 | 1.333 | 1.000 | 1.000 | 57.0 / 98 | 61.0 / 102 |
| hot-spot | 4 | 2.000 | 1.000 | 1.000 | 119.8 / 196 | 114.4 / 190 |
| hot-spot | 2 | 4.000 | 1.000 | 1.000 | 258.2 / 289 | 250.6 / 281 |

: Traffic patterns against offered load, `bridge_2x2_rw` (FUNC level, 48 reads per master per point, 2026-10-24). `bridge_2x2_rw_pipe` is the same curve one cycle later (11 / 15 cycles at light load).

Reading: below capacity every pattern carries exactly what is offered and
latency is flat (10 cycles alone at a slave, 14 when the other master's
reads interleave at it); the fabric adds no queueing of its own. At
capacity the permutation keeps both slaves at 1.000 however far it is
overloaded -- two flows cross the crossbar in parallel with nothing shared
-- and the hot-spot keeps its one port at 1.000 while latency grows with
the queue. Uniform traffic past saturation is the finding: 1.61 of 2.0 at
1.33x offered and 1.35 at 2x. The master adapter returns R in AR issue
order across slaves (its response mux follows the AR tracking FIFO's head),
so a read the idle slave has answered waits behind an earlier read still
queued at the busy one -- head-of-line blocking on the response path that
only uniform traffic past saturation can show. The request slots were the
first suspect and are not it: 4- and 8-deep slots measured the identical
curve. Filed as bridge TASK-021 (fix direction: select the R source by the
returned ID, which the remap slot or the per-ID table can carry); the test
holds those points at 0.55 of capacity under that ID until it lands.

On the mixed-width `bridge_4x4_rw` (cpu 64b, dma0 32b, dma1 128b, gpu
256b; periph 32b, ddr0 64b, sram 128b, gpu_mem 256b) the same sweep in
slave beats -- a 256-bit master's 4-beat read is 32 beats at the 32-bit
slave, which is why capacity is summed per slave:

| Pattern | Gap | Offered | Capacity | Accepted | cpu mean / p95 | dma0 | dma1 | gpu |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| uniform | 32 | 0.878 | 0.878 | 0.912 | 18.0 / 52 | 13.8 / 18 | 15.6 / 20 | 27.2 / 44 |
| uniform | 16 | 1.755 | 1.755 | 1.795 | 20.1 / 52 | 13.8 / 18 | 16.2 / 21 | 28.1 / 45 |
| uniform | 8 | 3.510 | 2.6 | 2.365 | 72.0 / 275 | 87.8 / 245 | 30.8 / 82 | 108.5 / 279 |
| uniform | 4 | 7.021 | 3.1 | 2.437 | 134.6 / 390 | 182.2 / 376 | 82.1 / 185 | 213.1 / 410 |
| uniform | 2 | 14.042 | 4.0 | 2.430 | 335.0 / 491 | 376.0 / 411 | 226.0 / 261 | 409.1 / 475 |
| permutation | 8 | 2.250 | 2.250 | 2.264 | 18.0 / 18 | 15.0 / 15 | 10.0 / 10 | 10.0 / 10 |
| permutation | 5 | 3.600 | 3.0 | 3.012 | 88.5 / 150 | 15.0 / 15 | 10.0 / 10 | 10.0 / 10 |
| permutation | 4 | 4.500 | 3.5 | 3.505 | 112.0 / 194 | 15.0 / 15 | 10.0 / 10 | 10.0 / 10 |
| permutation | 2 | 9.000 | 4.0 | 3.568 | 233.4 / 282 | 100.1 / 128 | 95.1 / 123 | 95.1 / 123 |
| hot-spot (ddr0) | 32 | 0.938 | 0.938 | 0.939 | 10.0 / 10 | 18.0 / 18 | 22.0 / 22 | 38.0 / 38 |
| hot-spot (ddr0) | 8 | 3.750 | 1.0 | 1.000 | 782.0 / 1070 | 706.1 / 1008 | 727.1 / 1021 | 743.1 / 1037 |
| hot-spot (ddr0) | 2 | 15.000 | 1.0 | 1.000 | 1157.7 / 1242 | 1113.6 / 1250 | 1120.7 / 1254 | 1136.7 / 1270 |

: Traffic patterns against offered load, `bridge_4x4_rw` (FUNC level, 2026-10-24; latency in cycles, mean / p95 per master)

The permutation (cpu -> periph, dma0 -> ddr0, dma1 -> sram, gpu -> gpu_mem)
carries 0.89-1.00 of its per-slave capacity however hard it is driven: four
flows of four widths cross at once, and only cpu's latency grows because
its 64-bit reads are eight beats each at the 32-bit periph, the one port it
oversubscribes. The hot spot keeps ddr0 at 1.000 from every master; all
four queue behind it equally. Uniform traffic is the same head-of-line
story as the 2x2 (bridge TASK-021): 0.91 of capacity at gap 8, 0.61 from
gap 4 on, each master's responses returning in issue order while a slave it
is waiting on is busy.

### Bandwidth Characterization (measured)

`test_bridge_perf_char` drives each fixture with pipelined requesters
(VALID held high across transactions, so a gap at a port belongs to the
fabric), a fixed number of transactions in flight and rotating IDs, and
checks every word. It measures inside each phase's own window and holds
every figure to a floor: one beat per cycle where the shape can saturate,
otherwise Little's law for the transactions in flight against the
fixture's measured round trip. It runs in the FUNC regression. A port on
its own clock is measured in that clock's cycles. Peak is one beat per
cycle of the port's clock, or of the slower clock across a crossing. Since
bridge TASK-016 the Little's-law floor takes the port's `max_outstanding`
from the fixture's `<bridge>_sizing.json`: a stream asked to keep more in
flight than the port holds is bound by the port (`bridge_2x2_rw_lat`
derives 8, so its 16- and 32-in-flight rows at 64 cycles of latency are
Little's law at 8).

| Fixture | What it adds | Streams, 2+ beats | Shared slave, both masters active | Single-beat round trip (one in flight) |
|---|---|---:|---:|---|
| `bridge_2x2_rw` | the reference | 1.000 | 0.997 writes, 1.000 reads | write 8 / read 7 cycles |
| `bridge_2x2_rw_pipe` | registered crossbar | 1.000 | 0.996 writes, 1.000 reads | write 10 / read 8 |
| `bridge_4x4_rw` | mixed widths, rate buffers | 1.000 | 0.995 writes, 1.000 reads | 12 on the upsized paths |
| `bridge_2x2_axi5` | AXI5 masters, AXI5 and AXI4 slaves | 1.000 | 0.997 writes, 1.000 reads | write 7 / read 6 |
| `bridge_2x2_rw_cdc`, slave 7 ns | slave faster than the 10 ns fabric | 0.700 at the slave (the fabric's rate), 1.000 at the masters | 0.696 writes, 0.700 reads | ~13 fabric cycles |
| `bridge_2x2_rw_cdc`, slave 13 ns | slave slower than the fabric | 1.000 at the slave, 0.770 at the masters | 0.993 writes, 0.999 reads | ~12 slave cycles |
| `bridge_2x2_axi3_masters` | AXI3 masters, 32b and 64b | 1.000 | 0.995 writes, 1.000 reads | write 7 / read 6 |
| `bridge_mix_e` | AXI3 and AXI4 masters, AXI3, AXI4 and APB slaves | 1.000; single-beat writes AXI3 to AXI3 0.890 at 8 in flight | 0.997 writes, 1.000 reads | write 8 / read 6 |

: Bandwidth characterization, `test_bridge_perf_char` (FUNC level, 2026-10-18)

Single-beat traffic is bounded by the round trip at a few in flight: eight
in flight carry 8 / (round trip) beats per cycle, and 16 in flight saturate
every same-clock path. That is latency, not lost bandwidth. A CDC port pays
two synchronizer crossings each way. Eight single-beat transactions in
flight reach 0.58 of the port's peak with the slave at 7 ns and 0.62 at
13 ns. Bursts of two beats or more saturate the slower side.

#### Limits fixed on 2026-10-18

- **W7, AXI3 master writes one at a time.** `axi3_to_axi4_wr` held AW from
  acceptance to B. Writes ran at beats / (beats + ~8): 0.111 single-beat,
  0.674 at 16 beats. It now passes every channel through, so writes
  overlap; W bursts must still follow AW order (AXI3 write-interleave depth
  1), and a simulation-only check flags any that do not.
- **W8, the AXI3 slave converter.** `axi4_to_axi3_rd/wr` issued at most one
  AR or AW every other cycle (single-beat reads 0.50), took one
  transaction per ID (same-ID single-beat reads 0.334), lost a W cycle per
  AXI3 burst, and queued four granted requests behind the arbiter
  (round-robin share 0.26). Now:
  - one request per cycle;
  - an unchopped request passes straight to the pins, so nothing is queued
    behind the arbiter (round-robin share 0.498 / 0.500);
  - up to 32 in flight across IDs; a chopped (17+ beat) request waits for
    its ID to drain;
  - W and B pass through when nothing is queued ahead.
- **W10, the AXI3 slave converter did not synthesize.** It kept its queues
  in SystemVerilog queues (`[$:N]`), which Vivado 2025.1 rejects ("[Synth
  8-27] dollar-sign operator not supported"). They are `gaxi_fifo_sync`
  instances now.
- **W11, no register on the AXI3 slave's R and B.** The converter faced the
  crossbar directly, so `<slave>_rvalid` reached `<slave>_rready` through
  the crossbar's R arbiter (-0.741 ns at 10 ns). An AXI3 slave adapter is
  now built like an AXI4 one: the timing wrapper, by-ID response routing
  when several masters share it, and the per-master request slots. The converter
  is the last stage before the pins. Responses are routed by ID through the
  tracker, as for AXI4, instead of by FIFO position.

- **W12, the per-ID CAM in every shared slave was the critical path.** A
  slave adapter shared by several masters looked each returning BID / RID
  up in `bridge_cam` to find the master, in series with the crossbar's
  response arbitration and the master adapter's per-ID counters (14-18 LUT
  levels). The fabric ID is `{master index, master id}`, so the master is
  the ID's top bits: the adapter now reads it off the ID and keeps one
  outstanding counter per direction (MAS 4.1). AXI4 slaves are covered as
  well as AXI3 ones. Halving the CAM to 8 entries had recovered only
  0.8-0.9 ns.

- **W13, the AXI3 slave converter's per-ID state on the request and BID
  paths.** The crossbar's AR grant ran into the read converter's per-ID
  check and chunk-address adder (17 levels), and the BID and RID pins ran
  into the merge counts through RID/BID-indexed muxes. A chopped (17+ beat)
  request is best effort now. It is taken into a staging register with no
  per-ID check and starts a cycle later, once its ID has drained. B lands raw
  in the converter's existing output register and is merged from there, and
  each ID's read-merge entry updates itself. Unchopped traffic gains no
  cycle. (A skid in front of B cost single-beat AXI3 writes 0.801 against
  0.862 beat/cycle, so it went into the existing register instead.)
- **W14, shim slaves picked from live requests.** An APB / AXI4-Lite / WB4
  slave that several masters share was picked straight from their requests,
  so one master's request gate ran through the grant into another master's
  accept and its width converter (`bridge_mix_e`, -0.106 ns). It takes
  per-master request slots like an AXI slave. The cost is one cycle of
  address latency on those slow slaves. Its W owner takes no early-W bypass,
  since a shim does not accept W before its AW.
- **W9, round-robin share at a CDC slave.** The pick was made on `aclk`, and
  granted requests queued in the one crossing to the slave, so a master with
  2 in flight got 0.18-0.20 against one with 8. A CDC slave that several
  masters share is now crossed per master and arbitrated on its own clock
  (`bridge_cdc_slave_arb`: per-lane async FIFOs, `arbiter_matrix` with a
  registered grant, W owner on the slave side; HAS 4.5a). At 32 cycles of
  slave latency the 2-deep master gets 0.496-0.500. With a slave that
  answers at once it gets 0.40-0.41, because its two transactions spend
  their turnaround crossing twice. With 8 in flight each, both get 0.498.

Built on the Artix-7 at 10 ns, every row with the I/O at 30% of the period
(HAS 6.4):

| Bridge | Before (per-ID CAM, 2026-10-18 morning) | Now | LUTs before -> now |
|---|---:|---:|---:|
| `bridge_2x2_axi3_masters` | +0.060 ns | +1.217 ns | 6,884 -> 5,218 |
| `bridge_2x2_axi3_slaves` | -1.006 ns | +0.231 ns | 10,636 -> 9,120 |
| `bridge_mix_e` | -2.686 ns | +0.174 ns | 17,158 -> 15,365 |
| `bridge_2x2_rw_cdc` | +0.066 ns | +0.637 ns | 5,184 -> 3,389 |

: Fixtures re-measured after W9 and W12-W14, Artix-7 -1 at 10 ns

All four meet timing. `rtl/common/arbiter_matrix` and
`arbiter_matrix_weighted` had never been through Vivado, and their update
loops were bounded by the winner itself. Vivado would not unroll them
(handbook `design/static-loop-bounds`); they are rewritten with static
bounds, and their own suites pass.

#### Open

None in the bridge's bandwidth or timing. The W9 residue above, a 2-deep
master at a zero-latency CDC slave, is a property of its own round trip and
is floored at its measured 0.40 in the perf suite.

#### Buffer Sizing Rule (`max_outstanding`, `latency_cycles`, `rate_buffer`)

Each port's `max_outstanding` bounds the transactions it keeps in flight.
A stream of `beats`-beat bursts saturates its port while

```
max_outstanding * beats >= beats + slave_latency + round_trip
```

That is the credit-loop rule (Dally & Towles ch. 12 / 15: a buffer holds the
loop's round trip, in units of what each entry carries), and since bridge
TASK-016 it is also how the generator sizes every depth a TOML leaves unset
(`bin/bridge_pkg/sizing.py`):

- `round_trip` is the fabric's own, summed per master -> slave path from the
  registered stages the generator builds there: the master wrapper's request
  and response stages, the request slot at a shared slave, the registered
  crossbar's two stages, the slave wrapper's two, the width and protocol
  converters (two each way), a CDC port's crossings (three each way), the rate
  buffer, the slave's turnaround and the response routing. It reproduces the
  single-beat round trips measured at one in flight -- 8 on `bridge_2x2_rw`,
  10 registered, 12-13 through a converter, 13 across a crossing -- as a
  bound within two cycles (`bin/tests/test_generator_pkg.py` holds it there).
- `slave_latency` is the slave's business: the TOML hint `latency_cycles`
  (default 0, a slave that answers the cycle after it accepts).
- The derived `max_outstanding` is the smallest power of two covering the
  single-beat case, `1 + latency_cycles + round_trip`, over the port's
  connected paths; so 16 on every standard fixture (9-14 before rounding),
  32 on `bridge_2x2_rw_slow` (`latency_cycles = 16`), 4-8 on a fabric cut
  to wires (`preset = "xbar"`). A master that keeps its own ID is floored at
  `2**id_width` so the derivation never turns ID remapping on by itself.
- `rate_buffer` (bridge W2) is derived to hold one `max_burst_beats` burst
  whole on the master's widest upsized path into a shared slave:
  `pow2(max_burst_beats / ratio)`, 0 where there is no such path.
- Every skid stage defaults to 2, the smallest that sustains a beat per
  cycle; W was 4.

The generator prints every depth with the rule's minimum beside it and
writes `<bridge>_sizing.json` next to the RTL (depths, their basis, the
per-path round trips). A pinned value under the rule's minimum is a
warning, not an error: the TOML wins, and the report says what it costs.
The board fabrics (`bridge-stress`, `fabric-benchmark`) pin the depths they
were measured with.

On `bridge_2x2_rw` (round trip 6-7 cycles), 8-beat bursts reach 1.000 with
4 in flight at 16 cycles of slave latency and with 16 at 64 cycles:

| Slave latency (cycles) | 1 in flight | 2 | 4 | 8 | 16 | 32 |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 0.577 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 |
| 16 | 0.271 | 0.544 | 1.000 | 1.000 | 1.000 | 1.000 |
| 64 | 0.105 | 0.212 | 0.431 | 0.846 | 1.000 | 1.000 |

: 8-beat read rate against transactions in flight, bridge_2x2_rw (FUNC level)

A depth of 16 covers 8-beat bursts up to about 110 cycles of slave
latency. Where it binds is single-beat traffic behind a slow slave: 16 in
flight carry 16 / (1 + latency + round trip), so 0.22 behind a 64-cycle
slave. Declare the slave's `latency_cycles` and the rule raises the depth
(to the 64 the trackers can hold), or pin `max_outstanding` (2..64) on those
ports only. It sizes every tracker on the path: the master adapters' per-ID
tables grow with it, while a shared slave's by-ID tracker is just a counter
(W12). The rule measured at its boundary is the next table.

| Fixture | `max_outstanding` (derived) | Stream | Slave latency | Rule holds | Little's law | Measured |
|---|---:|---|---:|---|---:|---:|
| `bridge_2x2_rw` (`latency_cycles` 0) | 16 | 1-beat reads | 16 | no (16 < 1 + 16 + 7) | 0.667 | 0.733 |
| | 16 | 1-beat writes | 16 | no | 0.640 | 0.706 |
| | 16 | 8-beat reads / writes | 16 | yes | 1.000 | 1.000 |
| | 16 | 1-beat reads / writes | 64 | no | 0.222 | 0.259 / 0.255 |
| | 16 | 8-beat reads / writes | 64 | yes | 1.000 | 1.000 |
| `bridge_2x2_rw_slow` (`latency_cycles` 16) | 32 | 1-beat reads / writes | 16 | yes (32 >= 1 + 16 + 8) | 1.000 | 1.000 |
| | 32 | 8-beat reads / writes | 16 | yes | 1.000 | 1.000 |
| | 32 | 1-beat reads / writes | 64 | no | 0.444 | 0.552 / 0.545 |
| | 32 | 8-beat reads / writes | 64 | yes | 1.000 | 1.000 |

: The sizing rule at its boundary: cpu -> ddr, as many in flight as the port allows, one ID per transaction, slave BFM answering after exactly the latency shown (`test_bridge_perf_sizing`, FUNC level, 2026-10-24)

Where the rule holds the port saturates; where it does not, the port runs at
Little's law or a little above it (the round trip under load is a cycle or
two shorter than the one-in-flight figure the rule uses, so the rule is a
safe bound). The two fixtures differ only in the hint: declaring the slave's
16 cycles moved the derived depth from 16 to 32 and the single-beat stream
from 0.73 to 1.00 of the port's peak. One ID per transaction in flight
matters for the measurement: the slave BFM answers same-ID reads in order,
one delayed response at a time per ID, so rotating 16 IDs caps the reads in
flight at 16 whatever the port allows.

### Multi-Master Scaling

Arbitration is a fair round-robin (measured above: 0.499 / 0.501 at the
shared port; the sum stays at one beat per cycle). The pick is made at the
slave's pins from per-master request slots, so the round-robin holds when
the slave throttles too: against a slave taking two transactions at a time,
a master with 2 in flight gets 0.50 of it against another master's 8 (it
got 0.34 while granted requests queued behind the arbiter). A CDC slave is
picked on its own clock from per-master lanes, so it holds too (W9, HAS
4.5a). A slave that
accepts many at once keeps its own queue, and the share inside it follows
each master's outstanding count. Per master, then:

```
Per-Master Throughput = Peak Throughput / Active Masters (to same slave)
```

#### Example: 4 Masters, 2 Slaves

```
All 4 masters accessing Slave 0:
  Per-master = Peak / 4

2 masters to Slave 0, 2 masters to Slave 1:
  Per-master = Peak / 2 (full parallelism)
```

### Burst Efficiency

| Transaction Type | Overhead | Efficiency |
|------------------|----------|------------|
| Single beat | 1 cycle address + 1 cycle data | 50% |
| 4-beat burst | 1 cycle address + 4 cycle data | 80% |
| 16-beat burst | 1 cycle address + 16 cycle data | 94% |
| 256-beat burst | 1 cycle address + 256 cycle data | 99.6% |

: Burst Efficiency Comparison

### Width Conversion Impact

#### Upsize (Narrow to Wide)

```
64-bit to 512-bit (8:1 ratio):
  Input: 8 beats × 64 bits = 512 bits
  Output: 1 beat × 512 bits = 512 bits

Throughput: Preserved (same data, fewer beats)
Latency: +1 cycle (packing delay)
```

#### Downsize (Wide to Narrow)

```
512-bit to 64-bit (8:1 ratio):
  Input: 1 beat × 512 bits = 512 bits
  Output: 8 beats × 64 bits = 512 bits

Throughput: Preserved (same data, more beats)
Latency: +7 cycles (sequential output)
```

### Protocol Conversion Impact

| Metric | AXI4 Direct | AXI4 to APB |
|--------|-------------|-------------|
| Min cycles/transfer | 1 | 2 |
| Burst support | Yes | No (split) |
| Pipeline depth | 1+ | 1 |
| Peak throughput | DATA_WIDTH/cycle | DATA_WIDTH/2 cycles |

: AXI4 vs APB Protocol Impact

## Design Notes

Bursts buy you efficiency:

- Use bursts whenever possible
- AXI4 supports up to 256 beats per burst
- APB does not support bursts (split internally)

And protocol choice matters more than most people expect:

- Keep high-bandwidth traffic on AXI4 paths
- Use APB only for low-bandwidth peripherals
- Group APB slaves to avoid impacting AXI4 traffic

## References

* Duato/Yalamanchili/Lionel, *Interconnection Networks*, Morgan Kaufmann 2003 — the standard network-evaluation methodology plots accepted traffic vs. applied load and latency vs. applied load, normalized to network capacity (ch9). ([Reference archive](../../../references/README.md))
* Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann 2004 — uniform-random traffic is benign; permutation, hot-spot, and adversarial patterns are the stresses that reveal allocation limits (ch3 §3.2-3.3). ([Reference archive](../../../references/README.md))
