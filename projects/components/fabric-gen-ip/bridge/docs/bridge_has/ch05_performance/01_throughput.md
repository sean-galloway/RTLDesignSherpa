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
| The same, writer B limited to 2 outstanding: B's share | 40.0% | 50.0% | 11.1% |

: The bridge against the vendor fabrics on the Genesys 2

In steady state the bridge costs no bandwidth, and its per-transfer
overhead matches the Xilinx crossbar. Under contention it is fairer than
SmartConnect. One case is not at parity with the crossbar: a writer limited
to 2 outstanding transactions gets 40% of a contended slave rather than 50%.
The cause measured so far is a longer write round trip. STREAM's AW-to-B
time is 256-511 cycles through the bridge against 64-127 through the
crossbar at the same throughput, which bounds a 2-outstanding writer. It is
not the slave tracker's depth: capping it at 4 changed nothing. Where the
extra time goes is open (GitHub #119).

The fabric is also larger and slower than the crossbar. Placed and routed
alone, out of context on the Genesys 2's part, the bridge is 10,450 LUTs and
7,479 flops with an estimated Fmax of ~179 MHz; the AXI Crossbar is 2,688
LUTs and 2,190 flops at ~256 MHz; SmartConnect is 8,333 LUTs, 3,959 LUTRAM
and 11,616 flops at ~268 MHz. The bridge's estimate was ~148 MHz before the
slave adapters' CAM insert and free were registered (MAS 4.1); its worst
path now runs from a master's R skid through the response routing into the
read CAM. All three close at the board's 100 MHz.

### Factors Affecting Throughput

| Factor | Impact | Mitigation |
|--------|--------|------------|
| Arbitration contention | Reduces per-master throughput | Increase slave ports |
| Width conversion | UNVERIFIED -- see note | Match widths where possible |
| Protocol conversion | 2+ cycles for APB | Use AXI4 for high-bandwidth |
| Response routing | Minimal (pipelined) | N/A |

: Factors Affecting Throughput

> **The width-conversion figure is not measured.** "1-cycle penalty per
> direction" has no source: the converters (`axi_data_upsize`,
> `axi_data_dnsize`, `axi4_dwidth_converter_{rd,wr}`) decompose or combine
> beats, so the cost depends on the width RATIO and the burst length, and a
> single constant cannot be right for 256b->32b and 64b->32b alike.
>
> It is left marked rather than replaced with a guess. Measuring it needs a
> propagation measurement on a converted path in `bridge_4x4_rw`
> (gpu 256b -> periph 32b) against a matched one (cpu 64b -> ddr0 64b), in the
> style of `test_bridge_2x2_rw_latency`. An attempt at that test could not
> reliably observe the master-side reference and was withdrawn rather than
> committed half-working.

### Multi-Master Scaling

With fair round-robin arbitration (measured above: 0.499 / 0.501 at the
shared port; the sum stays at one beat per cycle):

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
