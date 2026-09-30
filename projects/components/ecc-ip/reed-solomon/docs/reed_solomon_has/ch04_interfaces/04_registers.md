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

# Register Block

The standalone tops carry a PeakRDL-generated register block, `rs_regs`,
attached through the converters' APB-to-cpuif path exactly as STREAM's
configuration block attaches its own. The bare cores have no registers:
their configuration is parameters, and their status is the per-block status
port. The map below is the outline; the RDL is the authority once written.

| Register | Access | Contents |
|---|---|---|
| `ID` | RO | component ID, version, `KES_ALGO`, `ENABLE_*` build flags |
| `PROFILE` | RO | m, t, n, k, first root b, primitive polynomial index of the build |
| `CTRL` | RW | enable, soft reset, scrambler enable (if built), erasure enable (if built) |
| `JOB_SRC`, `JOB_DST`, `JOB_LEN` | RW | job fields (AXI4 ends only) |
| `JOB_KICK` | WO | start the job |
| `JOB_STATUS` | RO | busy, done, last job's status summary, AXI response errors |
| `STAT_BLOCKS` | RO | blocks processed |
| `STAT_CORRECTED_BLOCKS` | RO | blocks with at least one correction |
| `STAT_CORRECTED_SYMBOLS` | RO | total symbols corrected |
| `STAT_UNCORRECTABLE` | RO | blocks flagged uncorrectable |
| `STAT_FRAME_ERR` | RO | blocks with a length mismatch |
| `IRQ_EN`, `IRQ_STATUS` | RW / W1C | interrupt on uncorrectable, on job done, on frame error |

: Table 4.8: Register block outline

Registers are accessed by name through the generated regmap in DV and host
code, never by offset (`vault/handbook/dv/registers-by-name.md`). Counters
are 32-bit, saturating, cleared by `CTRL.soft_reset`.
