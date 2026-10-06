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

# Elaboration Configurations

## Default Config

The default elaboration geometry is the PRD D1 center point:

| Parameter | Value |
|-----------|-------|
| `SETS` | 128 |
| `WAYS` | 4 |
| `LINE_BYTES` | 64 |
| `BUS_WIDTH` | 64 |
| `REPL_POLICY` | `"LRU"` |
| `WRITE_POLICY` | `"wb_wa"` |
| `VICTIM_DEPTH` | 1 |

This is the configuration used for FPGA characterization, cache_sim parity, and the FULL cocotb grid.

## Tiny Formal Config

The SymbiYosys control-layer proofs use a tiny geometry for tractability:

| Parameter | Value |
|-----------|-------|
| `SETS` | 16 |
| `WAYS` | 2 |
| `LINE_BYTES` | 64 |
| `BUS_WIDTH` | 64 |
| `REPL_POLICY` | `"LRU"` |
| `WRITE_POLICY` | `"wb_wa"` |
| `VICTIM_DEPTH` | 1 |

The tiny config reduces tag-array depth and way count so that the formal tool can fully explore the control FSM and pending-fill bypass interactions.

## Bring-Up Config

A minimal bring-up config may use:

| Parameter | Value |
|-----------|-------|
| `SETS` | 4 |
| `WAYS` | 2 |
| `LINE_BYTES` | 32 |
| `BUS_WIDTH` | 32 |
| `REPL_POLICY` | `"FIFO"` |
| `WRITE_POLICY` | `"wt_na"` |
| `VICTIM_DEPTH` | 1 |

This is for initial module-level smoke tests only, not for characterization or formal proofs.

---

**Last Updated:** 2026-10-06
