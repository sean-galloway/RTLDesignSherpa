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

# Parameter Configuration

## Core Parameters

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| NUM_MASTERS | int | 1-32 | 2 | Number of master ports |
| NUM_SLAVES | int | 1-256 | 2 | Number of slave ports |
| ADDR_WIDTH | int | 12-64 | 32 | Address bus width |
| DATA_WIDTH | int | 32-512 | 64 | Data bus width |
| ID_WIDTH | int | 1-16 | 4 | Master ID width |
| USER_WIDTH | int | 1-16 | 1 | User signal width |

: Table 6.8: Bridge Core Parameters

## Derived Parameters

### Calculated by Generator

| Parameter | Formula | Example |
|-----------|---------|---------|
| BID_WIDTH | clog2(NUM_MASTERS) | 4 masters = 2 bits |
| TOTAL_ID_WIDTH | ID_WIDTH + BID_WIDTH | 4 + 2 = 6 bits |
| STRB_WIDTH | DATA_WIDTH / 8 | 64b = 8 strobes |

: Table 6.9: Derived Parameters

## Per-Port Configuration

### Master Port Configuration

| Field | Type | Description |
|-------|------|-------------|
| name | string | Unique identifier |
| prefix | string | Signal prefix |
| channels | enum | "rw", "wr", or "rd" |
| data_width | int | Port data width |
| id_width | int | Port ID width |

: Table 6.10: Master Port Configuration

### Slave Port Configuration

| Field | Type | Description |
|-------|------|-------------|
| name | string | Unique identifier |
| prefix | string | Signal prefix |
| protocol | enum | "axi4", "axi4lite", "apb" |
| data_width | int | Port data width |
| base_addr | hex | Base address |
| addr_range | hex | Address range size |

: Table 6.11: Slave Port Configuration

## Configuration File Format

### TOML Configuration

```toml
[bridge]
  name = "my_bridge"
  description = "Example bridge configuration"

  defaults.skid_depths = {ar = 2, r = 4, aw = 2, w = 4, b = 2}

  masters = [
    {name = "cpu", prefix = "cpu_m_axi", channels = "rw",
     id_width = 4, addr_width = 32, data_width = 64, user_width = 1},
    {name = "dma", prefix = "dma_m_axi", channels = "rw",
     id_width = 4, addr_width = 32, data_width = 256, user_width = 1}
  ]

  slaves = [
    {name = "ddr", prefix = "ddr_s_axi", protocol = "axi4",
     id_width = 6, addr_width = 32, data_width = 512, user_width = 1,
     base_addr = 0x80000000, addr_range = 0x40000000},
    {name = "uart", prefix = "uart_apb", protocol = "apb",
     addr_width = 12, data_width = 32,
     base_addr = 0x00000000, addr_range = 0x00001000}
  ]
```

### CSV Connectivity

```csv
master\slave,ddr,uart
cpu,1,1
dma,1,0
```

## Parameter Validation

### Generator Checks

| Check | Error Condition |
|-------|-----------------|
| NUM_MASTERS | < 1 or > 32 |
| NUM_SLAVES | < 1 or > 256 |
| DATA_WIDTH | Not power of 2 |
| Address overlap | Slave ranges intersect |
| Connectivity | Master with no slaves |
| ID width | Insufficient for masters |

: Table 6.12: Generator Validation Checks

### Runtime Validation

Bridge includes optional assertions for:

- Address alignment
- Burst boundary crossing
- Protocol violations
- ID mismatch

## Example Configurations

### Simple 2x2

```toml
[bridge]
  name = "bridge_simple"
  masters = [
    {name = "m0", prefix = "m0_axi", data_width = 64},
    {name = "m1", prefix = "m1_axi", data_width = 64}
  ]
  slaves = [
    {name = "s0", prefix = "s0_axi", base_addr = 0x0, addr_range = 0x10000000},
    {name = "s1", prefix = "s1_axi", base_addr = 0x10000000, addr_range = 0x10000000}
  ]
```

### Mixed Protocol

```toml
[bridge]
  name = "bridge_mixed"
  masters = [
    {name = "cpu", prefix = "cpu_axi", data_width = 64, channels = "rw"}
  ]
  slaves = [
    {name = "mem", prefix = "mem_axi", protocol = "axi4", data_width = 512},
    {name = "gpio", prefix = "gpio_apb", protocol = "apb", data_width = 32},
    {name = "uart", prefix = "uart_apb", protocol = "apb", data_width = 32}
  ]
```
