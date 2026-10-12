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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Assertions

## Overview

All generated Delta modules include an `ifdef FORMAL` block with SystemVerilog assertions for debug and formal verification.

## One-Hot Grant Check

Each slave must grant at most one master at a time:

```systemverilog
assert property (@(posedge aclk) disable iff (!aresetn)
    $onehot0(grant_matrix[s])
) else $error("Grant matrix not one-hot for slave %0d", s);
```

`$onehot0` allows the grant vector to be all-zero (idle) but not multi-hot.

## TDEST Range Check

Each master must drive a valid slave index when it asserts `TVALID`:

```systemverilog
assert property (@(posedge aclk) disable iff (!aresetn)
    s_axis_tvalid[m] |-> s_axis_tdest[m] < NUM_SLAVES
) else $error("TDEST out of range for master %0d", m);
```

## Enabling Assertions

Define `FORMAL` during simulation or formal analysis:

```bash
verilator --lint-only -DFORMAL rtl/delta_axis_flat_4x16.sv
```

## Notes

- Assertions are disabled by default to avoid simulation overhead.
- The TDEST range assertion duplicates the combinational safety check in the request decode block.
- Additional protocol assertions (TVALID stability, TLAST packet integrity) are candidates for the planned cocotb testbench.
