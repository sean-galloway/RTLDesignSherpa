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

# Document Conventions

## Naming Conventions

| Convention | Meaning | Example |
|------------|---------|---------|
| `s_axis_*` | Signals on the master side of the crossbar (inputs) | `s_axis_tdata[m]` |
| `m_axis_*` | Signals on the slave side of the crossbar (outputs) | `m_axis_tready[s]` |
| `[NUM_MASTERS]` | Unpacked array dimension, one entry per master | `s_axis_tvalid [NUM_MASTERS]` |
| `[NUM_SLAVES]` | Unpacked array dimension, one entry per slave | `m_axis_tvalid [NUM_SLAVES]` |
| `m` | Master index | `for (int m = 0; m < NUM_MASTERS; m++)` |
| `s` | Slave index | `for (int s = 0; s < NUM_SLAVES; s++)` |

: Naming Conventions

## Signal Direction Conventions

All directions are stated from the crossbar's point of view:

- `s_axis_*` signals are driven by upstream masters and received by Delta.
- `m_axis_*` signals are driven by Delta and received by downstream slaves.
- `aclk` and `aresetn` are driven by the system.

## Numbering Conventions

- Masters are numbered `0` to `NUM_MASTERS-1`.
- Slaves are numbered `0` to `NUM_SLAVES-1`.
- `TDEST` is interpreted as a slave index; legal values are `0` to `NUM_SLAVES-1`.

## Typographic Conventions

- `code font` is used for signal names, parameters, and file paths.
- **Bold** is used for emphasis and defined terms.
- Tables use the RTL Design Sherpa corporate document style.

## Versioning Conventions

This document uses semantic-style major.minor revision numbers. The initial release is 1.0.
