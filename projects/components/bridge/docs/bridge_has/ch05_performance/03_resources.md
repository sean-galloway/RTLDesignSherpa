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
`projects/components/bridge/fpga/` (HAS 6.4: how it constrains the bridge,
how to repeat a run, how to read a line of `reports/summary.csv`), on the two
parts this repository's boards carry. Earlier revisions of this page carried
hand estimates per component and per configuration; they did not reconcile
with each other and had never been checked against a synthesis report, so
they are gone. Anything not in the tables below is a configuration nobody
has synthesized yet, and the flow takes minutes to answer for it.

## Measured Utilization and Timing

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 4,441 | 3,325 | 0 | +0.40 | 104.2 | 8 |
| `bridge_2x2_rw` | 4,615 | 3,253 | 0 | +0.12 | 101.2 | 9 |
| `bridge_2x2_rw_cdc` | 4,851 | 3,413 | 0 | +0.27 | 102.7 | 9 |
| `bridge_2x2_rw_pipe` | 5,646 | 4,227 | 0 | +1.27 | 114.6 | 6 |
| `bridge_2x2_rw_qos` | 5,136 | 3,317 | 0 | -2.91 | 77.4 | 14 |
| `bridge_2x2_rw_qos_pipe` | 5,494 | 4,291 | 0 | +0.17 | 101.7 | 9 |
| `bridge_4x4_rw` | 30,278 | 29,508 | 0 | -1.57 | 86.4 | 14 |
| `bridge_5x3_channels` | 19,243 | 16,932 | 0 | -2.66 | 79.0 | 16 |
| `bridge_mix_a` | 6,456 | 5,697 | 0 | -0.29 | 97.1 | 16 |

: Table 5.11: Measured utilization and timing, Artix-7 100T -1 at 10 ns (HAS 6.4 flow)

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 4,430 | 3,325 | 0 | +0.69 | 167.4 | 9 |
| `bridge_2x2_rw` | 4,612 | 3,253 | 0 | +0.97 | 175.6 | 9 |
| `bridge_2x2_rw_cdc` | 4,842 | 3,413 | 0 | +0.55 | 163.4 | 9 |
| `bridge_2x2_rw_pipe` | 5,647 | 4,227 | 0 | +1.73 | 202.6 | 6 |
| `bridge_2x2_rw_qos` | 4,963 | 3,317 | 0 | -0.18 | 146.0 | 13 |
| `bridge_2x2_rw_qos_pipe` | 5,475 | 4,291 | 0 | +0.70 | 167.6 | 9 |
| `bridge_4x4_rw` | 29,719 | 29,508 | 0 | +0.28 | 156.5 | 13 |
| `bridge_5x3_channels` | 19,035 | 16,932 | 0 | -0.13 | 147.1 | 17 |
| `bridge_mix_a` | 6,375 | 5,697 | 0 | +0.53 | 162.9 | 8 |

: Table 5.12: Measured utilization and timing, Kintex-7 325T -2 at 6.667 ns

Fmax is an estimate from the register-to-register slack at the constrained
period; the I/O budget and the reading of each row are in HAS 6.4. The
rows that miss on the Artix-7 all fail on one path -- master adapter,
crossbar arbitration and mux, slave CAM allocate -- and `xbar_pipeline`
is the register that splits it: `bridge_2x2_rw_qos` at -2.91 ns becomes
`bridge_2x2_rw_qos_pipe` at +0.17 ns.

### Scaling

| Component | Scales with |
|-----------|-------------|
| Crossbar core | O(M x N) muxing, plus one arbiter per slave channel |
| Master adapters | O(M), each holding a full beat per channel in its skid buffers |
| Slave adapters | O(N), plus a converter and its monitor sandwich for every non-AXI4 or width-stepped port |
| bridge_id FIFOs | O(N x depth), small LUT arrays, no BRAM |
| Registered crossbar (`xbar_pipeline`) | one 2-deep skid per slave-side channel |
| CDC slave port (`cdc`) | one async FIFO per channel of that port |

: Table 5.13: Resource Scaling

Block RAM and DSP usage are zero in every configuration measured: the
per-slave bridge_id FIFOs and the CAM are LUT arrays, and there is no
arithmetic.

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

: Table 5.14: Performance/Resource Trade-offs
