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
| `bridge_2x2_axi5` | 5,060 | 3,945 | 0 | -0.06 | 99.4 | 10 |
| `bridge_2x2_axi5_native` | 8,054 | 6,705 | 0 | -0.53 | 95.0 | 12 |
| `bridge_2x2_rw` | 5,719 | 4,537 | 0 | +0.05 | 100.5 | 9 |
| `bridge_2x2_rw_cdc` | 5,334 | 3,953 | 0 | +0.05 | 100.5 | 10 |
| `bridge_2x2_rw_pipe` | 5,492 | 4,801 | 0 | +0.69 | 107.5 | 8 |
| `bridge_2x2_rw_qos` | 5,195 | 3,857 | 0 | -0.63 | 94.1 | 12 |
| `bridge_2x2_rw_qos_pipe` | 5,938 | 4,865 | 0 | -0.62 | 94.2 | 12 |
| `bridge_4x4_rw` | 39,642 | 37,968 | 0 | -7.48 | 57.2 | 20 |
| `bridge_5x3_channels` | 30,138 | 27,875 | 0 | -3.96 | 71.6 | 15 |
| `bridge_mix_a` | 7,632 | 6,551 | 0 | -4.51 | 68.9 | 16 |

: Measured utilization and timing, Artix-7 100T -1 at 10 ns (HAS 6.4 flow)

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 4,911 | 3,945 | 0 | +0.40 | 159.6 | 11 |
| `bridge_2x2_axi5_native` | 7,889 | 6,705 | 0 | +0.41 | 159.9 | 12 |
| `bridge_2x2_rw` | 5,617 | 4,537 | 0 | +0.21 | 155.0 | 11 |
| `bridge_2x2_rw_cdc` | 5,202 | 3,953 | 0 | +0.38 | 159.2 | 10 |
| `bridge_2x2_rw_pipe` | 5,494 | 4,801 | 0 | +1.14 | 180.8 | 7 |
| `bridge_2x2_rw_qos` | 4,986 | 3,857 | 0 | +0.46 | 161.1 | 12 |
| `bridge_2x2_rw_qos_pipe` | 5,852 | 4,865 | 0 | +0.24 | 155.7 | 12 |
| `bridge_4x4_rw` | 39,671 | 37,968 | 0 | -2.73 | 106.4 | 20 |
| `bridge_5x3_channels` | 30,001 | 27,875 | 0 | -0.62 | 137.3 | 16 |
| `bridge_mix_a` | 7,524 | 6,551 | 0 | -1.11 | 128.6 | 16 |

: Measured utilization and timing, Kintex-7 325T -2 at 6.667 ns

Fmax is an estimate from the register-to-register slack at the constrained
period; the I/O budget and the reading of each row are in HAS 6.4.
Re-measured 2026-10-16. The 2x2s stay near 100 MHz on the Artix-7 and meet
150 MHz on the Kintex-7. The fixtures with width converters miss on one
structure, the write converter's B-response fold in series with a slave
CAM, and its fix is open (GitHub #119). The September path through the
slave CAM allocate is gone, taken out by the registered CAM insert.

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
