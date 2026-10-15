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

**[← Back to README](../README.md)**

# Genesys 2 Fabric Benchmark — Address Map

The design uses one 32-bit address space. The **data fabric under test** decodes
the lower regions; the **configuration bridge** decodes the top region
(`0xF000_0000` and above). They are two separate interconnects, but no address
means two things, so every reachable block is listed in one table.

Sources:

- Data-fabric decode: [`rtl/bridges/configs/bridge_fb_data.toml`](../rtl/bridges/configs/bridge_fb_data.toml) and the generated [`bridge_fb_data.sv`](../rtl/bridges/generated/bridge_fb_data/bridge_fb_data.sv).
- Configuration region: PRD.md section 5, mirroring the DE10-Standard fabric
  benchmark address map with the Genesys 2 STREAM harness offsets under a
  `0xF000_0000` base.

Status: **planned for K0** — the map is extracted from the PRD and the
generated bridge, but the harness top and host scripts that implement it have
not yet landed.

### Figure 1: System address map

![System address map](assets/graphviz/k7_address_map.png)

**Source:** [assets/graphviz/k7_address_map.dot](assets/graphviz/k7_address_map.dot)

## Data-fabric regions

| Base | Size | Block | Reached by | Behind the port |
| --- | ---: | --- | --- | --- |
| `0x0000_0000` | 1 GB | DDR3 | data fabric (`stream` rd/wr, injector) | MIG 7-series AXI4 slave (memory model in sim) |
| `0x8000_0000` | 64 KB | `desc_ram` read port | data fabric (`stream` m_axi_desc) | `sdpram_slave_axi4_axi4`; host preloads the same RAM at `0xF002_0000` |
| `0x9000_0000` | 256 MB | LFSR source | data fabric (`stream` m_axi_rd) | `axi4_cdc_rd` → `axi4_slave_rd_injector` (read-only) |
| `0xA000_0000` | 256 MB | CRC sink | data fabric (`stream` m_axi_wr) | `axi4_cdc_wr` → `axi4_slave_wr_crc_check` (write-only) |

: Table 1: Data-fabric address map

Unmapped accesses in the data-fabric window are caught by the bridge's
subtractive slave (`axi4_subtractive_slave`), which returns DECERR and latches
the first offending address.

## Configuration region

The configuration bridge is `bridge_stream_mon_axil`, the same generated bridge
used by the Genesys 2 STREAM harness. The offsets below are relative to the
base `0xF000_0000`.

| Base (absolute) | Size | Window | Block behind it |
| --- | ---: | --- | --- |
| `0xF000_0000` | 8 KB | `stream_apb` | STREAM registers: channel enables, scheduler/engine config, `KICK`, in-core perf CSRs |
| `0xF001_0000` | 4 KB | `harness_csr` | Harness control/status: `CTRL`, `STATUS`, timer, per-channel CRCs, `CRC_RD_EXPECTED` / `CRC_WR_EXPECTED` / `CRC_WR_COMPUTED` |
| `0xF002_0000` | 64 KB | `desc_ram` write port | Descriptor preload, 32 bytes per descriptor |
| `0xF003_0000` – `0xF017_FFFF` | — | *(reserved)* | Tallies, error drains — monitor build only, **not in v1** |
| `0xF018_0000` | 4 KB | `obs_slave` | Observer at the fabric's slave ports (DDR3, LFSR source, CRC sink) |
| `0xF019_0000` | 4 KB | `obs_master` | Observer at the fabric's master ports (`stream` rd/wr, injector wr) |
| `0xF01A_0000` | — | *(reserved)* | Capture SRAM — monitor build only, **not in v1** |
| `0xF01C_0000` | 4 KB | `obs_desc` | Observer on `stream`'s descriptor master |
| `0xF01D_0000` | 4 KB | `chargen` | W3 injector registers (`char_engine_block`) |

: Table 2: Configuration bridge address map

## As-built vs planned

- **As-built:** `bridge_fb_data` data-fabric decode from the generated RTL
  matches the data-fabric table above.
- **Planned:** the configuration bridge, CSR windows, host register-map layer,
  and the harness top that instantiates them are not yet present in this area.
  They are expected to be reused from
  `projects/fpga-systems/Genesys2/dma-ip/stream/` with only the base address
  changed.
