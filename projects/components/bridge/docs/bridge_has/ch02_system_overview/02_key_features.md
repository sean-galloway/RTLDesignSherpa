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

# Key Features

## Configuration-Driven Generation

### CSV/TOML Configuration

Bridge uses human-readable configuration files:

- **ports configuration** - Define each master and slave port
- **connectivity matrix** - Specify which masters connect to which slaves
- **Version-control friendly** - Text-based, easy to diff and review

### Example Configuration

**Port Definition (TOML):**
```toml
masters = [
  {name = "cpu", prefix = "cpu_m_axi", data_width = 64, channels = "rw"},
  {name = "dma", prefix = "dma_m_axi", data_width = 256, channels = "rw"}
]
slaves = [
  {name = "ddr", prefix = "ddr_s_axi", data_width = 512, protocol = "axi4"},
  {name = "uart", prefix = "uart_apb", data_width = 32, protocol = "apb"}
]
```

**Connectivity Matrix (CSV):**
```csv
master\slave,ddr,uart
cpu,1,1
dma,1,0
```

## Multi-Protocol Support

| Master Protocol | Slave Protocol | Conversion Type |
|-----------------|----------------|-----------------|
| AXI4 | AXI4 | Direct or width convert |
| AXI4 | AXI4-Lite | Protocol downgrade |
| AXI4 | APB | Full protocol conversion |

: Table 2.1: Supported Protocols

### Protocol Features

- **AXI4 Full** - Complete 5-channel implementation with bursts
- **AXI4-Lite** - Simplified single-beat transactions
- **APB** - Low-power peripheral access

## Channel-Specific Masters

### Write-Only Masters (wr)

Generate only write channels:
- AW (Write Address)
- W (Write Data)
- B (Write Response)

**Use case:** DMA write engines, descriptor writers

### Read-Only Masters (rd)

Generate only read channels:
- AR (Read Address)
- R (Read Data)

**Use case:** DMA read engines, source data fetchers

### Full Masters (rw)

Generate all five channels for complete read/write capability.

**Use case:** CPU interfaces, configuration masters

### Resource Savings

| Master Type | Channels | Signal Reduction |
|-------------|----------|------------------|
| Write-only (wr) | 3 of 5 | ~39% fewer signals |
| Read-only (rd) | 2 of 5 | ~61% fewer signals |
| Full (rw) | 5 of 5 | Baseline |

: Table 2.2: Channel-Specific Resource Savings

## Automatic Converters

### Width Conversion

Bridge automatically inserts width converters:

- **Upsize** - Narrow master to wide slave (e.g., 64b to 512b)
- **Downsize** - Wide master to narrow slave (e.g., 512b to 32b)
- **Per-path** - Only where needed, not global conversion

### Protocol Conversion

Bridge inserts protocol converters for mixed systems:

- **AXI4 to APB** - Full conversion with burst handling
- **AXI4 to AXI4-Lite** - Simplified conversion

## Flexible Topology

### Scalability

- **Masters:** 1-32 master ports
- **Slaves:** 1-256 slave ports
- **Partial connectivity** - Not all masters need access to all slaves

### Mixed Configurations

- **Mixed protocols** - AXI4, AXI4-Lite, and APB slaves in same crossbar
- **Mixed data widths** - 32b, 64b, 128b, 256b, 512b
- **Mixed channels** - Write-only, read-only, and full masters
