# Suspected Bug: apb5_slave_cdc_cg CDC Wakeup Violation

## Summary

Line 132 of `apb5_slave_cdc_cg.sv`:
```systemverilog
r_wakeup <= s_apb_PSEL || s_apb_PENABLE || cmd_valid || rsp_valid || wakeup_request;
```

The signals `cmd_valid`, `rsp_valid`, and `wakeup_request` are in the
`aclk` domain but are sampled directly in `pclk` domain (via `r_wakeup`
which is clocked by `pclk`). This is a **CDC violation** -- these signals
cross from aclk to pclk without synchronization.

This cannot be detected by the single-clock formal model (pclk=aclk=clk).

## Impact

Under true multi-clock operation, the aclk-domain signals could be
metastable when sampled by pclk. The consequence would be an unreliable
wakeup signal leading to sporadic clock gating failures -- either:
- Wakeup fails and the clock stays gated, blocking transactions
- Wakeup fires spuriously causing unnecessary power consumption

## Recommended Fix

Add 2-FF synchronizers for the aclk-domain signals:
```systemverilog
logic cmd_valid_sync, rsp_valid_sync, wakeup_request_sync;

cdc_synchronizer #(.WIDTH(1)) u_sync_cmd (
    .clk_dst(pclk), .rst_dst_n(presetn),
    .async_in(cmd_valid), .sync_out(cmd_valid_sync)
);
cdc_synchronizer #(.WIDTH(1)) u_sync_rsp (
    .clk_dst(pclk), .rst_dst_n(presetn),
    .async_in(rsp_valid), .sync_out(rsp_valid_sync)
);
cdc_synchronizer #(.WIDTH(1)) u_sync_wakeup (
    .clk_dst(pclk), .rst_dst_n(presetn),
    .async_in(wakeup_request), .sync_out(wakeup_request_sync)
);

r_wakeup <= s_apb_PSEL || s_apb_PENABLE || cmd_valid_sync || rsp_valid_sync || wakeup_request_sync;
```

## Also Applies To

- `apb_slave_cdc_cg.sv` (line 123: `s_apb_PSEL` used in aclk domain)
- All CDC CG wrappers that mix domain signals in the wakeup logic
