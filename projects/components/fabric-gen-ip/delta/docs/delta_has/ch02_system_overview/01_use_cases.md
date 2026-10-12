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

# Use Cases

## Primary: RISC Cores + DSP Array

**Scenario:** Four small RISC-V cores route compute tasks to sixteen DSP accelerators.

**Configuration:**

- 4 masters (RISC cores)
- 16 slaves (DSP arrays)
- 64-bit data width
- Flat topology

**Benefits:**

- Each RISC core can target any DSP (full flexibility).
- Per-slave round-robin arbitration prevents starvation.
- Two-cycle latency keeps task dispatch responsive.
- All sixteen DSPs can operate concurrently when traffic targets different slaves.

## Secondary: Sensor/Peripheral Fabric

**Scenario:** Multiple sensor streams feed a smaller set of processing blocks.

**Configuration:**

- 2-8 masters (sensor front-ends)
- 2-4 slaves (aggregation or filter blocks)
- 32-bit data width with optional `TSTRB` byte qualifiers

**Benefits:**

- Direct TDEST routing removes the need for an address decoder.
- Packet atomicity preserves frame boundaries from each sensor.
- Optional `TSTRB` supports sparse byte-valid data from byte-packed sensors.

## Tertiary: AMBA 5-Aware Streaming Interconnect

**Scenario:** A low-power subsystem needs wakeup hints and AXI5-Stream interface parity protection.

**Configuration:**

- Masters and slaves that implement AMBA 5 AXI-Stream
- `--amba5` enabled

**Benefits:**

- `TWAKEUP` lets a master wake a target slave before presenting data.
- The IHI 0051B chapter 5 check signals (`TDATACHK` and the rest, odd parity) are carried across the fabric and checked at each crossbar port. A sticky per-port flag reports a fault.
- Generated ports port-match the `rtl/amba/axis5/*` interface conventions.

## Educational Demonstration

**Scenario:** Teach interconnect design trade-offs and code generation.

**Configuration:**

- Generate flat crossbars of varying sizes into `rtl_test/`.
- Compare latency, throughput, and resource estimates from `delta_performance_model.py`.

**Benefits:**

- Hands-on learning with working RTL.
- Clear performance comparisons.
- Demonstrates specification-driven design and Python-based RTL generation.
