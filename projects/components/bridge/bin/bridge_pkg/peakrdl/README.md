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

# Bridge cfg subsystem — PeakRDL flow

Status: **historical prototype** (task 90.1)

This directory holds the hand-written `.rdl` prototype from task 90.1,
kept as the reference for the schema style. It is not part of the
generation flow: RDL generation now lives in
`bridge_pkg/generators/cfg_rdl_generator.py` +
`bridge_pkg/jinja_templates/bridge_cfg.rdl.j2`, which emit the per-bridge
`.rdl` into the bridge output directory alongside the generated SV.

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
