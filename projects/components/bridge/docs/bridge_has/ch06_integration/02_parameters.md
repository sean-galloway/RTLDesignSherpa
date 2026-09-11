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

## Overview

Every bridge the generator emits starts here: port counts, bus widths, per-port configuration, and the address map. This chapter collects the full parameter set — the core knobs, the widths the generator derives from them, the per-port fields, the monitor options, and the checks the generator runs before it accepts your configuration.

## Parameters

### Core Parameters

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| NUM_MASTERS | int | 1-32 | 2 | Number of master ports |
| NUM_SLAVES | int | 1-256 | 2 | Number of slave ports |
| ADDR_WIDTH | int | 12-64 | 32 | Address bus width |
| DATA_WIDTH | int | 32-512 | 64 | Data bus width |
| ID_WIDTH | int | 1-16 | 4 | Master ID width |
| USER_WIDTH | int | 1-16 | 1 | User signal width |

: Table 6.8: Bridge Core Parameters

### Registered Crossbar (`xbar_pipeline`)

| TOML key (`[bridge]`) | Type | Default | Effect |
|---|---|---|---|
| `xbar_pipeline` | bool | `false` | `true` puts a 2-deep skid stage on every slave-side channel (AW, W, AR, B, R) inside the crossbar. Propagation 3/3 cycles instead of 2/2 (Table 5.7), throughput unchanged. For high-fanout or wide fabrics that miss timing on the arbiter-plus-mux or the response OR-merge cone. Measured (HAS 6.4): the register that splits the arbitration-mux-CAM path; on the Artix-7 at 100 MHz any configuration beyond a plain 2x2 -- QoS, wide ports, more masters -- needs it. |
| `arbitration` | `"rr"` / `"qos"` | `"rr"` | Per-slave arbitration policy. `"qos"` grants the highest `AxQOS` plus aging (MAS 2.3, Per-Slave Request Arbitration); it decides among requests pending at the arbiter, so it shows at a slave that backpressures AW, not at one that accepts every AW on arrival; equals share round-robin. |
| `qos_aging_shift` | int 0..7 | 4 | With `"qos"`: a waiting request gains one priority level every `2**shift` cycles, so the worst wait for a QoS-0 request is `15 * 2**shift` cycles. |

: Table 6.8a: Crossbar options (BRIDGE-017)

| TOML key (`[[bridge.slaves]]`) | Type | Default | Effect |
|---|---|---|---|
| `cdc` | bool | `false` | `true` gives this AXI4 slave port its own clock: `<name>_aclk` / `<name>_aresetn` on the top, `axi4_cdc_{wr,rd}` between the adapter's timing wrapper and the port (HAS 4.5a). Slave ports, `protocol = "axi4"` only. |

: Table 6.8b: CDC slave port option (BRIDGE-017)

### Derived Parameters

The generator works these out from the core set — you never write them yourself:

| Parameter | Formula | Example |
|-----------|---------|---------|
| BRIDGE_ID_WIDTH | clog2(NUM_MASTERS) | 4 masters = 2 bits |
| STRB_WIDTH | DATA_WIDTH / 8 | 64b = 8 strobes |

: Table 6.9: Derived Parameters

> `TOTAL_ID_WIDTH` was listed here as a derived parameter. It does not exist:
> IDs are not extended, so there is nothing to widen. `BRIDGE_ID_WIDTH` sizes
> the SIDEBAND master id carried beside the transaction, and is the only
> derived width the generated package defines.

### Per-Port Configuration

Each master and slave port carries its own field set in the configuration file.

#### Master Port Configuration

| Field | Type | Description |
|-------|------|-------------|
| name | string | Unique identifier |
| prefix | string | Signal prefix |
| channels | enum | "rw", "wr", or "rd" |
| data_width | int | Port data width |
| id_width | int | Port ID width |
| use_monitor | bool | Optional, defaults to `true`. Per-port monitor wrappers. Only meaningful on a `mon` variant; on a `no` variant there is nothing to disable. |

: Table 6.10: Master Port Configuration

#### Slave Port Configuration

| Field | Type | Description |
|-------|------|-------------|
| name | string | Unique identifier |
| prefix | string | Signal prefix |
| protocol | enum | `axi4`, `axi5`, `axil`, `axil5`, `apb`, `apb5` -- the exact values `config_validator.valid_protocols` accepts. Note `axil`, not `axi4lite`. |
| data_width | int | Port data width |
| base_addr | hex | Base address (must be 4K-aligned) |
| addr_range | hex | Address range size (must be multiple of 4K) |
| use_monitor | bool | Optional, defaults to `true`. Per-port monitor wrappers. Only meaningful on a `mon` variant; on a `no` variant there is nothing to disable. |

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

**Why This Rule Exists:**

- Real memory systems use 4K page boundaries (virtual memory, MMU)
- Linker scripts and memory maps assume 4K granularity
- Address decoders simplify to bit masks with 4K alignment
- Prevents ambiguity in address decode logic

There's nothing arbitrary about the 4K requirement — it's the granularity the rest of the system already assumes.

### Top-Level Monitor Configuration

When monitor collection is desired, the bridge TOML configuration includes:

| Field | Type | Description |
|-------|------|-------------|
| variants | list | List of bridge variants to generate. Supported: `["no"]` (no monitor), `["mon"]` (monitor only), `["no", "mon"]` (both). Default: `["no"]` |

#### Monitor Identifiers

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

#### AXIL→Wider-Slave Master-Side Alignment

When an AXI4-Lite master connects to a wider AXI4 slave through the bridge (e.g., 32-bit AXIL master to 64-bit AXI4 slave), the generator emits a master-side alignment converter (the `axil_to_axi4_wide_align_{rd,wr}` modules) between the master adapter and the crossbar core. The converter handles partial-word alignment on the narrow side while preserving AXIL's single-beat semantics; the protocol stays AXIL — protocol shims are a slave-boundary concern, applied separately.

### Parameter Validation

#### Generator Checks

The generator checks every configuration against these rules:

| Check | Error Condition |
|-------|-----------------|
| NUM_MASTERS | < 1 or > 32 |
| NUM_SLAVES | < 1 or > 256 |
| DATA_WIDTH | Not power of 2 |
| Address overlap | Slave ranges intersect |
| Connectivity | Master with no slaves |
| ID width | Insufficient for masters |

: Table 6.12: Generator Validation Checks

#### Runtime Validation

Bridge includes optional assertions for:

- Address alignment
- Burst boundary crossing
- Protocol violations
- ID mismatch

## Usage Example

A complete configuration is two parts: the TOML file that describes the bridge, and the CSV that describes the connectivity.

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

Two configurations to use as starting points:

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
    {name = "mem",  prefix = "mem_axi",  protocol = "axi4", data_width = 512,
     base_addr = 0x00000000, addr_range = 0x80000000},
    {name = "gpio", prefix = "gpio_apb", protocol = "apb",  data_width = 32,
     base_addr = 0x80000000, addr_range = 0x00010000},
    {name = "uart", prefix = "uart_apb", protocol = "apb",  data_width = 32,
     base_addr = 0x80010000, addr_range = 0x00010000}
  ]
```
