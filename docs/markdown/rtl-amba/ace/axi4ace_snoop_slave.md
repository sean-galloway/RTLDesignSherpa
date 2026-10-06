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

# axi4ace_snoop_slave

ACE snoop-channel responder transport on the cache side: AC in from the coherency manager, CR/CD out back to the manager.

## Overview

The `axi4ace_snoop_slave` module sits between the coherency manager (onyx) and a cache's snoop FSM (amber/jet). It receives a snoop command on the AC channel, buffers it, and presents it to the cache FSM on the FUB side. The cache FSM returns its response on CR and any data on CD; those are buffered back to the manager. It is a transport module and does not generate snoop responses or data.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AC | int | 2 | Snoop address channel skid buffer depth in entries (2..8 inclusive) |
| SKID_DEPTH_CR | int | 4 | Snoop response channel skid buffer depth in entries (2..8 inclusive) |
| SKID_DEPTH_CD | int | 4 | Snoop data channel skid buffer depth in entries (2..8 inclusive) |
| ADDR_WIDTH | int | 32 | Snoop address width |
| DATA_WIDTH | int | 32 | Snoop data width |
| AW | int | ADDR_WIDTH | Short alias for address width |
| DW | int | DATA_WIDTH | Short alias for data width |
| ACSize | int | AW + 4 + 3 | Packed AC skid payload width |
| CRSize | int | 5 | Packed CR skid payload width |
| CDSize | int | DW + 1 | Packed CD skid payload width |

## Ports

### Module Declaration

```systemverilog
module axi4ace_snoop_slave #(
    parameter int SKID_DEPTH_AC = 2,
    parameter int SKID_DEPTH_CR = 4,
    parameter int SKID_DEPTH_CD = 4,
    parameter int ADDR_WIDTH    = 32,
    parameter int DATA_WIDTH    = 32,
    parameter int AW            = ADDR_WIDTH,
    parameter int DW            = DATA_WIDTH,
    parameter int ACSize        = AW + 4 + 3,
    parameter int CRSize        = 5,
    parameter int CDSize        = DW + 1
) (
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI Interface (Input Side) -- manager/coherency controller -> cache
    // Snoop address channel (AC)
    input  logic [AW-1:0]              m_axi_acaddr,
    input  logic [3:0]                 m_axi_acsnoop,
    input  logic [2:0]                 m_axi_acprot,
    input  logic                       m_axi_acvalid,
    output logic                       m_axi_acready,

    // Snoop response channel (CR)
    output logic [4:0]                 m_axi_crresp,
    output logic                       m_axi_crvalid,
    input  logic                       m_axi_crready,

    // Snoop data channel (CD)
    output logic [DW-1:0]              m_axi_cddata,
    output logic                       m_axi_cdlast,
    output logic                       m_axi_cdvalid,
    input  logic                       m_axi_cdready,

    // Fabric/Upstream Buffer Interface (Output Side) -- cache snoop FSM
    // Snoop address channel (AC)
    output logic [AW-1:0]              fub_acaddr,
    output logic [3:0]                 fub_acsnoop,
    output logic [2:0]                 fub_acprot,
    output logic                       fub_acvalid,
    input  logic                       fub_acready,

    // Snoop response channel (CR)
    input  logic [4:0]                 fub_crresp,
    input  logic                       fub_crvalid,
    output logic                       fub_crready,

    // Snoop data channel (CD)
    input  logic [DW-1:0]              fub_cddata,
    input  logic                       fub_cdlast,
    input  logic                       fub_cdvalid,
    output logic                       fub_cdready,

    // Status outputs for clock gating
    output logic                       busy
);
```

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXI clock |
| aresetn | 1 | Input | AXI active-low reset |

### Manager Interface (Input Side - AXI)

#### Snoop Address Channel (AC)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axi_acaddr | ADDR_WIDTH | Input | Snoop address |
| m_axi_acsnoop | 4 | Input | Snoop transaction type |
| m_axi_acprot | 3 | Input | Protection attributes |
| m_axi_acvalid | 1 | Input | Snoop address valid |
| m_axi_acready | 1 | Output | Snoop address ready |

#### Snoop Response Channel (CR)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axi_crresp | 5 | Output | Snoop response |
| m_axi_crvalid | 1 | Output | Snoop response valid |
| m_axi_crready | 1 | Input | Snoop response ready |

#### Snoop Data Channel (CD)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axi_cddata | DATA_WIDTH | Output | Snoop data |
| m_axi_cdlast | 1 | Output | Last snoop data beat |
| m_axi_cdvalid | 1 | Output | Snoop data valid |
| m_axi_cdready | 1 | Input | Snoop data ready |

### Cache FSM Interface (Output Side - FUB)

#### Snoop Address Channel (AC)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_acaddr | ADDR_WIDTH | Output | Snoop address |
| fub_acsnoop | 4 | Output | Snoop transaction type |
| fub_acprot | 3 | Output | Protection attributes |
| fub_acvalid | 1 | Output | Snoop address valid |
| fub_acready | 1 | Input | Snoop address ready |

#### Snoop Response Channel (CR)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_crresp | 5 | Input | Snoop response |
| fub_crvalid | 1 | Input | Snoop response valid |
| fub_crready | 1 | Output | Snoop response ready |

#### Snoop Data Channel (CD)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_cddata | DATA_WIDTH | Input | Snoop data |
| fub_cdlast | 1 | Input | Last snoop data beat |
| fub_cdvalid | 1 | Input | Snoop data valid |
| fub_cdready | 1 | Output | Snoop data ready |

### Status Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| busy | 1 | Output | Module activity indicator for clock gating |

## Functional Description

### Triple Buffer Design

The module buffers all three snoop channels independently:

1. **AC Channel Buffer**: Manager → cache FSM
2. **CR Channel Buffer**: Cache FSM → manager
3. **CD Channel Buffer**: Cache FSM → manager

### Busy Signal Generation

```systemverilog
assign busy = (int_ac_count > 0) || (int_cr_count > 0) || (int_cd_count > 0) ||
                m_axi_acvalid || fub_crvalid || fub_cdvalid;
```

## ACE Notes

- Snoop channels have no transaction ID; ordering is by channel only
- ACE requires CR and CD responses after the AC handshake, and both CR and CD must be returned in the same order as the AC addresses
- The module does not enforce the stricter `cache-ip` convention (complete CD before CR); that ordering is produced by the cache FSM driving the FUB side
- `CRRESP` bit semantics follow ACE: DataTransfer[0], Error[1], PassDirty[2], IsShared[3], WasUnique[4]

## Related Modules

- **axi4ace_snoop_slave_monlite**: Lite-monitor wrapper for this core
- **axi4ace_snoop_master**: Complementary CCU-side snoop initiator
- **axi4ace_snoop_monitor_lite**: ACE-aware monitor core for the snoop channels
- **gaxi_skid_buffer**: Underlying buffer infrastructure

---

## Navigation

- **[← Back to ACE Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
