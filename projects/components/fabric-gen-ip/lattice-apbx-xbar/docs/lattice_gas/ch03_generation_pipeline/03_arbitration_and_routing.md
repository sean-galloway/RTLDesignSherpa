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

# Arbitration and Routing

For each slave, the generator emits an independent round-robin arbiter that selects among the masters requesting that slave.

## Per-slave request vector

```systemverilog
s0_arb_request[0] = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd0);
s0_arb_request[1] = m1_cmd_valid && m1_addr_in_range && (m1_slave_sel == 2'd0);
```

When `num_slaves == 1`, the slave-select check is omitted.

## Round-robin arbitration

The generator instantiates `arbiter_round_robin` with `WAIT_GNT_ACK=1` so the grant is locked until the transaction completes:

```systemverilog
arbiter_round_robin #(
    .CLIENTS(2),
    .WAIT_GNT_ACK(1)
) u_s0_arbiter (...);
```

The grant-ack vector is driven by `rsp_valid && rsp_ready` on the selected slave port, ensuring the grant persists across the entire APB access.

## Command routing

A combinational `case (1'b1)` mux routes the granted master's cmd fields to the slave-side cmd nets. APB5 sideband is carried only when both the master and the slave are APB5.

## Response routing

The generator registers each master's slave selection (`r_m<N>_slave_sel`) when a command is accepted. On the response path, the registered slave index selects which slave's `rsp_*` signals are returned to the master. The registered selection keeps the response aligned with the command even if a new command arrives before the first response completes.

## Ready routing

- Master `cmd_ready` is asserted only by the slave selected by the current command.
- Slave `rsp_ready` is asserted only by the master currently holding the grant for that slave.
- The decode-miss path bypasses the slave arbiters and completes locally.
