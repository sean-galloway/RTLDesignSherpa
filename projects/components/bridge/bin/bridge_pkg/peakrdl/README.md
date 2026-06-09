# Bridge cfg subsystem — PeakRDL flow

Status: **prototype** (task 90.1)

This directory will eventually hold the auto-generated `.rdl` for the
bridge's monitor cfg space, plus the regblock SV that PeakRDL emits.
For now it contains a hand-coded prototype for one adapter port so we
can lock the schema style before extending it across all 9 adapters
(see task 90.2).

## Prototype

`bridge_cfg_proto.rdl` describes host_0's 36 cfg signals (18 wr + 18 rd)
packed into 14 32-bit registers per direction (CTRL + LATENCY + 5 MASKS).

To regenerate the SV (one-shot during 90.1 development):

```bash
peakrdl regblock bridge_cfg_proto.rdl --cpuif axi4-lite-flat -o /tmp/bridge_cfg_out/
```

The emitted regblock exposes an AXIL slave (`s_axil_*`) and a typed
`hwif_out` struct whose fields back the bridge's existing internal
cfg nets.

## Integration pattern (sketch)

The bridge generator will, in 90.3, instantiate this regblock inside
the bridge top and route its outputs to existing cfg nets:

```sv
bridge_cfg_proto u_bridge_cfg (
    .clk            (aclk),
    .rst            (~aresetn),
    .s_axil_awvalid (s_cfg_axil_awvalid),
    // ... other AXIL slave channels ...
    .hwif_out       (cfg_hwif)
);

assign cfg_host_0_wr_monitor_enable = cfg_hwif.HOST_0_WR_CTRL.monitor_enable.value;
assign cfg_host_0_wr_error_enable   = cfg_hwif.HOST_0_WR_CTRL.error_enable.value;
// ... rest of the 351 cfg nets ...
```

After 90.3 the bridge's external port list drops the 351 `cfg_*`
inputs and replaces them with a single AXIL slave port.

## Address map

Each adapter direction (e.g. host_0_wr) occupies 28 bytes = 7 × 32-bit
registers, packed as:

| Offset | Register   | Fields                                                  |
|-------:|------------|---------------------------------------------------------|
|  0x00  | CTRL       | enables[6:0] + timeout_cycles[31:16]                    |
|  0x04  | LATENCY    | latency_threshold[31:0]                                 |
|  0x08  | MASKS_A    | axi_pkt_mask + axi_err_select                           |
|  0x0C  | MASKS_B    | axi_error_mask + axi_timeout_mask                       |
|  0x10  | MASKS_C    | axi_compl_mask + axi_thresh_mask                        |
|  0x14  | MASKS_D    | axi_perf_mask + axi_addr_mask                           |
|  0x18  | MASKS_E    | axi_debug_mask (upper 16b reserved)                     |

Two directions × 9 adapters = 504 bytes for per-monitor cfg. The
mon_group_* cfg (cfg_base_addr, cfg_limit_addr, cfg_axi_*_mask, etc.)
adds another ~128 bytes for ~632 bytes total — well within a single
AXIL register block.
