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

# Resources

## Overview

What a generated bridge costs on an FPGA, measured. The numbers below come
from the out-of-context synthesis and implementation flow in
`projects/components/fabric-gen-ip/bridge/fpga/` (HAS 6.4: how it constrains the bridge,
how to repeat a run, how to read a line of `reports/summary.csv`), on the two
parts this repository's boards carry. Earlier revisions of this page carried
hand estimates per component and per configuration; they did not reconcile
with each other and had never been checked against a synthesis report, so
they are gone. Anything not in the tables below is a configuration nobody
has synthesized yet, and the flow takes minutes to answer for it.

## Measured Utilization and Timing

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 5,120 | 4,013 | 0 | -0.11 | 98.9 | 10 |
| `bridge_2x2_axi5_native` | 8,252 | 6,773 | 0 | -1.20 | 89.3 | 11 |
| `bridge_2x2_rw` | 5,832 | 4,605 | 0 | -0.04 | 99.6 | 11 |
| `bridge_2x2_rw_cdc` | 5,184 | 4,021 | 0 | +0.07 | 100.7 | 11 |
| `bridge_2x2_rw_pipe` | 5,569 | 4,869 | 0 | +0.57 | 106.1 | 8 |
| `bridge_2x2_rw_qos` | 5,344 | 3,925 | 0 | -0.28 | 97.3 | 11 |
| `bridge_2x2_rw_qos_pipe` | 5,932 | 4,933 | 0 | -0.02 | 99.8 | 12 |
| `bridge_4x4_rw` | 40,239 | 38,241 | 0 | -3.01 | 76.9 | 15 |
| `bridge_5x3_channels` | 30,835 | 28,051 | 0 | -3.21 | 75.7 | 15 |
| `bridge_mix_a` | 7,994 | 6,623 | 0 | -2.10 | 82.6 | 13 |

: Measured utilization and timing, Artix-7 100T -1 at 10 ns (HAS 6.4 flow)

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 4,949 | 4,013 | 0 | +0.59 | 164.6 | 11 |
| `bridge_2x2_axi5_native` | 8,119 | 6,773 | 0 | +0.47 | 161.3 | 12 |
| `bridge_2x2_rw` | 5,682 | 4,605 | 0 | +0.56 | 163.8 | 10 |
| `bridge_2x2_rw_cdc` | 5,030 | 4,021 | 0 | +0.26 | 156.0 | 10 |
| `bridge_2x2_rw_pipe` | 5,564 | 4,869 | 0 | +1.14 | 180.8 | 9 |
| `bridge_2x2_rw_qos` | 5,176 | 3,925 | 0 | +0.48 | 161.6 | 11 |
| `bridge_2x2_rw_qos_pipe` | 5,886 | 4,933 | 0 | +0.53 | 163.0 | 11 |
| `bridge_4x4_rw` | 40,042 | 38,241 | 0 | -0.14 | 146.8 | 13 |
| `bridge_5x3_channels` | 30,712 | 28,051 | 0 | -0.68 | 136.1 | 15 |
| `bridge_mix_a` | 7,844 | 6,623 | 0 | +0.30 | 157.1 | 13 |

: Measured utilization and timing, Kintex-7 325T -2 at 6.667 ns

Fmax is an estimate from the register-to-register slack at the constrained
period; the I/O budget and the reading of each row are in HAS 6.4.
Re-measured 2026-10-16 (rev 1.3). The 2x2s, QoS included, are at 100 MHz on
the Artix-7 and meet 150 MHz on the Kintex-7. The fixtures with width
converters, unmeasurable until the read converters lost their reassembly
pool, now miss by 2-3 ns on the Artix-7 and up to 0.7 ns on the Kintex-7, on
wide response paths that `xbar_pipeline` registers.

### Arbitration Policy on an ASIC Library (ASAP7)

Bridge TASK-015 asked where the matrix arbiter lands against the round-robin
for the bridge's usual two to eight masters. Measured on the generated
crossbar module alone (`<bridge>_xbar`, the arbiters' home), flattened,
Yosys + ABC against the ASAP7 7 nm RVT library at the TT corner, OpenSTA
register to register on the mapped netlist; the driver is
`projects/asic-trials/timing_characterization/work/synth_module.py`. The two
netlists of each pair differ only in the arbiter: adding the `matrix` policy
left every `rr` and `qos` fixture byte-identical on regeneration.

| Crossbar (`<bridge>_xbar`, flattened) | Policy | Cells | Flops | Area (um^2) | ABC delay (ps) / levels | STA worst reg-to-reg (ps) |
|---|---|---:|---:|---:|---:|---:|
| `bridge_2x2_rw` | rr | 19,295 | 1,883 | 2,063 | 369 / 17 | 454 |
| `bridge_2x2_rw_matrix` | matrix | 19,228 | 1,883 | 2,081 | 401 / 18 | 479 |
| `bridge_2x2_rw_qos` | qos | 20,334 | 1,979 | 2,280 | 748 / 28 | 821 |
| `bridge_4x4_rw` | rr | 60,685 | 5,311 | 6,389 | 543 / 22 | 610 |
| `bridge_4x4_rw_matrix` | matrix | 62,103 | 5,321 | 6,532 | 471 / 20 | 542 |

: ASAP7 RVT TT, Yosys 0.62 + ABC at a 1000 ps target, OpenSTA on the mapped netlist (2026-10-24)

| Crossbar | Policy | Cells | Area (um^2) | ABC delay (ps) / levels | STA worst reg-to-reg (ps) |
|---|---|---:|---:|---:|---:|
| `bridge_2x2_rw` | rr | 19,279 | 2,061 | 385 / 16 | 461 |
| `bridge_2x2_rw_matrix` | matrix | 19,336 | 2,088 | 364 / 18 | 445 |
| `bridge_2x2_rw_qos` | qos | 20,849 | 2,318 | 609 / 24 | 690 |
| `bridge_4x4_rw` | rr | 62,362 | 6,479 | 458 / 19 | 540 |
| `bridge_4x4_rw_matrix` | matrix | 60,828 | 6,443 | 437 / 19 | 513 |

: The same, mapped at a 400 ps target (the mapper under pressure)

Reading: at four masters the matrix arbiter takes 5-11 percent off the
crossbar's worst path for about 2 percent in cells (the rotation chain of the
round-robin's pick was the critical path); at two masters the two policies
are one priority bit either way and land within mapper noise. QoS-with-aging
costs 28 logic levels and 5 percent of the area on the same 2x2. Fairness is
the same bound (`n-1` foreign grants between two of a master's own), measured
1 at 2x2 and 2 at 4x4 three-way (MAS 2.4). The ASIC figures are a proxy, not
a sign-off: no placement, ideal clock, one corner.

The same pair out of context on the Kintex-7 325T -2 at 10 ns (HAS 6.4 flow,
2026-10-24):

| Bridge (whole top) | LUTs | FFs | WNS (ns) | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_4x4_rw` | 48,775 | 47,187 | +1.315 | +1.315 | 115.1 | 9 |
| `bridge_4x4_rw_matrix` | 48,817 | 47,209 | +1.207 | +1.338 | 115.4 | 10 |

: Kintex-7, 4x4, round-robin against matrix

On the FPGA the two are the same design to within 0.1 percent of LUTs and 23
ps of register-to-register slack: a LUT6 absorbs either pick in one level,
so the ASIC's gate-depth advantage does not show. The FPGA number does not
argue for a default change either.

Default policy (PRD FR-6): `rr` stays the default. The matrix arbiter wins
only where four or more masters contend on an ASIC library, it is neutral on
the FPGA, and every board build is tuned to its measured round-robin timing;
choose `arbitration = "matrix"` for a wide fabric on an ASIC target.

### Scaling

| Component | Scales with |
|-----------|-------------|
| Crossbar core | O(M x N) muxing, plus one arbiter per slave channel |
| Master adapters | O(M), each holding a full beat per channel in its skid buffers |
| Slave adapters | O(N), plus a converter and its monitor sandwich for every non-AXI4 or width-stepped port |
| bridge_id FIFOs | O(N x depth), small LUT arrays, no BRAM |
| Registered crossbar (`xbar_pipeline`) | one 2-deep skid per slave-side channel |
| CDC slave port (`cdc`) | one async FIFO per channel; shared by M masters, M lanes of AW / W / AR FIFOs plus B and R, two `arbiter_matrix` and a W owner FIFO |

: Resource Scaling

Block RAM and DSP usage are zero in every configuration measured: the
per-slave bridge_id FIFOs are LUT arrays, the by-ID trackers are counters, and there is no
arithmetic.

The current resource figures come from a small set of configurations driven
with uniform-style traffic; a systematic resource-vs-load characterization
across adversarial patterns is tracked as bridge vault TASK-014.

## Design Notes

### Resource Reduction

1. **Use channel-specific masters** - a read-only or write-only master
   builds half the adapter and half the crossbar columns
2. **Match data widths** - a width step costs a converter each way
3. **Use APB and AXI-Lite slaves sparingly** - each carries a shim and a
   second monitor
4. **Limit outstanding transactions** - shallower per-slave bridge_id FIFOs

### Performance/Resource Trade-off

| Feature | Resource Impact | Performance Impact |
|---------|-----------------|-------------------|
| Deeper skid buffers | +registers | +timing margin |
| Deeper bridge_id FIFOs | +LUTs | +outstanding depth (no OOO support) |
| Pipeline stages | +registers | +frequency |
| Wider data paths | +routing | +throughput |

: Performance/Resource Trade-offs

## References

* Duato/Yalamanchili/Lionel, *Interconnection Networks*, Morgan Kaufmann 2003 — accepted traffic vs. applied load and latency vs. applied load are the standard network-evaluation plots; resource counts must be paired with those load sweeps to be meaningful (ch9). ([Reference archive](../../../references/README.md))
* Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann 2004 — uniform-random traffic is benign; permutation and hot-spot patterns are the standard stresses that reveal allocation and buffer-sizing limits which in turn drive resource growth (ch3 §3.2-3.3). ([Reference archive](../../../references/README.md))
