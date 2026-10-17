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

### Scaling

| Component | Scales with |
|-----------|-------------|
| Crossbar core | O(M x N) muxing, plus one arbiter per slave channel |
| Master adapters | O(M), each holding a full beat per channel in its skid buffers |
| Slave adapters | O(N), plus a converter and its monitor sandwich for every non-AXI4 or width-stepped port |
| bridge_id FIFOs | O(N x depth), small LUT arrays, no BRAM |
| Registered crossbar (`xbar_pipeline`) | one 2-deep skid per slave-side channel |
| CDC slave port (`cdc`) | one async FIFO per channel of that port |

: Resource Scaling

Block RAM and DSP usage are zero in every configuration measured: the
per-slave bridge_id FIFOs and the CAM are LUT arrays, and there is no
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
