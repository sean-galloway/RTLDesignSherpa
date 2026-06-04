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
| use_monitor | bool | **Mandatory.** Enable per-port monitor wrappers (true/false) |

: Table 6.10: Master Port Configuration

### Slave Port Configuration

| Field | Type | Description |
|-------|------|-------------|
| name | string | Unique identifier |
| prefix | string | Signal prefix |
| protocol | enum | "axi4", "axi4lite", "apb" |
| data_width | int | Port data width |
| base_addr | hex | Base address (must be 4K-aligned) |
| addr_range | hex | Address range size (must be multiple of 4K) |
| use_monitor | bool | **Mandatory.** Enable per-port monitor wrappers (true/false) |

: Table 6.11: Slave Port Configuration

#### Slave Address Window Rules (MANDATORY)

Every slave must occupy a 4K-aligned address window that is a multiple of 4 KB:

```
Rule 1: Base Address Alignment
  base_addr & 0xFFF == 0x000
  
  Valid:   0x00000000, 0x00001000, 0x80000000, 0xFFFF0000
  Invalid: 0x00000001, 0x80000800, 0xC0000100

Rule 2: Range Alignment
  addr_range % 0x1000 == 0
  
  Valid:   0x1000 (4 KB), 0x2000 (8 KB), 0x10000 (64 KB)
  Invalid: 0x800 (2 KB), 0x1001, 0x7FFF

Rule 3: Non-Overlapping Windows
  All slaves must have non-overlapping address ranges
  
  Valid:   Slave0: 0x00000000-0x0FFFFFFF, Slave1: 0x10000000-0x1FFFFFFF
  Invalid: Slave0: 0x00000000-0x10000000, Slave1: 0x0FFFFFFF-0x1FFFFFFF
```

## Top-Level Monitor Configuration

When monitor collection is desired, the bridge TOML configuration includes:

| Field | Type | Description |
|-------|------|-------------|
| variants | list | List of bridge variants to generate. Supported: `["no"]` (no monitor), `["mon"]` (monitor only), `["no", "mon"]` (both). Default: `["no"]` |

### Monitor Identifiers

Each monitored port gets a unique `(UNIT_ID, AGENT_ID)` pair for identification in monitor packets:

```
UNIT_ID Assignment:
  - UNIT_ID = 1: Master-side monitor wrappers (axi4_master_{rd,wr}_mon)
  - UNIT_ID = 2: Slave-side monitor wrappers (axi4_slave_{rd,wr}_mon)

AGENT_ID Assignment (per port):
  - AGENT_ID = (port_index << 4) | channel_bit
  - channel_bit: 0 = read channel (AR/R), 1 = write channel (AW/W/B)
  - Example: Master port 2, write direction → AGENT_ID = (2 << 4) | 1 = 0x21
```

### AXIL→Wider-Slave Master-Side Alignment

When an AXI4-Lite master connects to a wider AXI4 slave through the bridge (e.g., 32-bit AXIL master to 64-bit AXI4 slave), the generator automatically emits a master-side alignment converter (`axil_to_axi4_wide_align_{rd,wr}` modules) between the master adapter and the crossbar core. This converter handles partial-word alignment on the narrow side while preserving AXIL's single-beat semantics, without changing the protocol from AXIL to AXI4 (protocol shims are applied separately at the slave boundary).

**Why This Rule Exists**:
- Real memory systems use 4K page boundaries (virtual memory, MMU)
- Linker scripts and memory maps assume 4K granularity
- Address decoders simplify to bit masks with 4K alignment
- Prevents ambiguity in address decode logic

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
