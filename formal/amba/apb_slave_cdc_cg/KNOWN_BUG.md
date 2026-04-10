# Suspected Bugs: apb_slave_cdc_cg

## Bug 1: PREADY Forced To Zero During Gating

Line 115 of `apb_slave_cdc_cg.sv`:
```systemverilog
assign s_apb_PREADY = pclk_cg_gating ? 1'b0 : int_apb_PREADY;
```

This unconditionally forces `s_apb_PREADY` to 0 whenever `pclk_cg_gating`
is asserted. This is a **protocol glitch hazard**: if an APB transaction
is in flight (PSEL asserted) when the clock gate engages, PREADY is
yanked to 0, potentially violating the master's view of the APB protocol.

In practice, `pclk_user_valid = s_apb_PSEL || w_rsp_valid` keeps the clock
ungated while PSEL is asserted, so the hazard only triggers if the gating
engages between PSEL assertion cycles (which the design intends to
prevent). However, combined with Bug 2 below, this creates a window
where PREADY can flicker during the wakeup latency.

## Bug 2: CDC Wakeup Through Pclk Signal In Aclk Domain

Line 123 of `apb_slave_cdc_cg.sv`:
```systemverilog
assign aclk_axi_valid = cmd_valid || cmd_ready || s_apb_PSEL;
```

This feeds `s_apb_PSEL` (a pclk-domain signal) directly into the
`aclk_gate_ctrl.axi_valid` input. That input eventually flops the
signal inside `amba_clock_gate_ctrl` (`r_wakeup <= user_valid || axi_valid`),
clocked by aclk. **This is a CDC violation** -- a pclk-domain signal
crosses into the aclk domain without a synchronizer.

The single-clock formal model (pclk=aclk=clk) cannot detect this bug
because synchronization is trivially satisfied when both domains run on
the same clock. Under true CDC, this path would require a 2-FF
synchronizer on `s_apb_PSEL` before it can feed the aclk gate controller.

## Recommended Fixes

### Fix 1 (PREADY):
Remove the override, or gate it with a PENABLE qualifier so it only
masks PREADY during truly-idle gating:
```systemverilog
assign s_apb_PREADY = int_apb_PREADY;  // Trust the gated flop value
```

### Fix 2 (CDC PSEL):
Synchronize `s_apb_PSEL` into the aclk domain before using it for
wakeup:
```systemverilog
logic s_apb_PSEL_aclk;
cdc_synchronizer #(.WIDTH(1)) u_psel_sync (
    .clk_dst(aclk), .rst_dst_n(aresetn),
    .async_in(s_apb_PSEL), .sync_out(s_apb_PSEL_aclk)
);
assign aclk_axi_valid = cmd_valid || cmd_ready || s_apb_PSEL_aclk;
```

## Formal Proof Handling

The formal wrapper uses a single-clock model (pclk=aclk=clk) so CDC Bug 2
is not observable. The proof verifies:
- Reset clears PREADY and both gating outputs
- `cfg_cg_enable=0` implies no gating
- Cover points demonstrate the valid/ready paths
