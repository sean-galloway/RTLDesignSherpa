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

The BCH component has no standalone tops and therefore no register block at
revision 0.1. The bare cores are parameterised; their status is the
per-block `out_status` port. When the AXI4 job adapter is built a register
block will be added to the standalone top, attached through the converters'
APB-to-cpuif path exactly as the reed-solomon standalone tops do.

The target register map is the reed-solomon map adapted to bit-level status:

| Register | Access | Contents |
|---|---|---|
| `ID` | RO | component ID, version, `KES_ALGO`, `ENABLE_*` build flags |
| `PROFILE` | RO | m, t, n, k, first root b, primitive polynomial index of the build |
| `CTRL` | RW | enable, soft reset, erasure enable (if built) |
| `JOB_SRC`, `JOB_DST`, `JOB_LEN` | RW | job fields (AXI4 ends only) |
| `JOB_KICK` | WO | start the job |
| `JOB_STATUS` | RO | busy, done, last job's status summary, AXI response errors |
| `STAT_BLOCKS` | RO | blocks processed |
| `STAT_CORRECTED_BLOCKS` | RO | blocks with at least one correction |
| `STAT_CORRECTED_BITS` | RO | total bits corrected |
| `STAT_UNCORRECTABLE` | RO | blocks flagged uncorrectable |
| `STAT_FRAME_ERR` | RO | blocks with a length mismatch |
| `IRQ_EN`, `IRQ_STATUS` | RW / W1C | interrupt on uncorrectable, on job done, on frame error |

: Table 4.8: Register block outline (target)

Registers will be accessed by name through the generated regmap in DV and
host code, never by offset (`vault/handbook/dv/registers-by-name.md`).
Counters will be 32-bit, saturating, cleared by `CTRL.soft_reset`.
