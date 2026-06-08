# mon_temp/ — Staging area for the CAM-backed monitor rewrite

This directory holds in-progress versions of the AXI monitor RTL that
move the per-transaction keying + payload storage out of inline
`always_ff` blocks and into the shared `monitor_trans_cam` module
(see `../monitor_trans_cam.sv`).

**Not on the synth path.** Nothing here is referenced from any
`rtl/amba/filelists/*.f`. Verilator's `-y rtl/amba/shared` is
non-recursive so it will not pick these files up by accident. The
production modules in `rtl/amba/shared/` are still authoritative.

When a staged module reaches functional + timing parity with its
production sibling, the swap is a single filelist edit:

```
- $REPO_ROOT/rtl/amba/shared/axi_monitor_trans_mgr.sv
+ $REPO_ROOT/rtl/amba/shared/mon_temp/axi_monitor_trans_mgr.sv
+ $REPO_ROOT/rtl/amba/shared/monitor_trans_cam.sv
```

Module names mirror the production names so the swap doesn't require
hierarchy edits in the parents (e.g. `axi_monitor_base.sv`).

## Status

| Module                   | Source        | Status      |
|--------------------------|---------------|-------------|
| `axi_monitor_trans_mgr.sv` | this dir    | WIP, not validated |
