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

# AXI4 Interface Overview

## Interface Organization

### Master-Side Interfaces

Bridge presents **slave interfaces** to upstream masters. Each master port includes:

| Channel | Signals | Direction (to Bridge) |
|---------|---------|----------------------|
| AW | AWVALID, AWREADY, AWADDR, AWID, AWLEN, AWSIZE, AWBURST, ... | Input |
| W | WVALID, WREADY, WDATA, WSTRB, WLAST | Input |
| B | BVALID, BREADY, BID, BRESP | Output |
| AR | ARVALID, ARREADY, ARADDR, ARID, ARLEN, ARSIZE, ARBURST, ... | Input |
| R | RVALID, RREADY, RDATA, RID, RRESP, RLAST | Output |

: Master-Side Interface Channels

### Slave-Side Interfaces

Bridge presents **master interfaces** to downstream slaves. Each slave port includes:

| Channel | Signals | Direction (from Bridge) |
|---------|---------|------------------------|
| AW | AWVALID, AWREADY, AWADDR, AWID, AWLEN, AWSIZE, AWBURST, ... | Output |
| W | WVALID, WREADY, WDATA, WSTRB, WLAST | Output |
| B | BVALID, BREADY, BID, BRESP | Input |
| AR | ARVALID, ARREADY, ARADDR, ARID, ARLEN, ARSIZE, ARBURST, ... | Output |
| R | RVALID, RREADY, RDATA, RID, RRESP, RLAST | Input |

: Slave-Side Interface Channels

## Signal Naming Convention

### Custom Prefixes

Each port uses a custom prefix for signal naming:

```systemverilog
// Example: Master 0 with prefix "cpu_m_axi_"
input  logic [31:0] cpu_m_axi_awaddr,
input  logic [3:0]  cpu_m_axi_awid,
input  logic        cpu_m_axi_awvalid,
output logic        cpu_m_axi_awready,
// ... remaining AW signals

// Example: Slave 0 with prefix "ddr_s_axi_"
output logic [31:0] ddr_s_axi_awaddr,
output logic [4:0]  ddr_s_axi_awid,  // {BRIDGE_ID, id}: master width + clog2(NUM_MASTERS)
output logic        ddr_s_axi_awvalid,
input  logic        ddr_s_axi_awready,
```

### ID Width Extension

Slave-side IDs are `{master index, master-local id}`, sized by outstanding
requests rather than by the masters' ID widths:

```
Local ID Width:  per master, clog2(max_outstanding) if its id_width is wider
                 (a remap slot), else its id_width   (widest = MASTER_ID_WIDTH)
Bridge ID Width: clog2(NUM_MASTERS)            (ID_PREFIX_WIDTH; 0 for one master)
Slave ID Width:  MASTER_ID_WIDTH + ID_PREFIX_WIDTH  (XBAR_ID_WIDTH)

bridge_2x2_rw:       cpu_m_axi_awid [7:0]  ->  ddr_s_axi_awid [4:0]   (slot)
bridge_2x2_ooo:      cpu_axi_awid   [3:0]  ->  ddr_axi_awid   [4:0]   (ID kept)
bridge_5x3_channels: cpu_axi_awid   [7:0]  ->  sram_buffer_axi_awid [6:0]
```

Each master adapter sends `{BRIDGE_ID, slot}` (or `{BRIDGE_ID, id}`) into
the fabric. On B and R its remap table restores the master's ID from the
returned slot (bridge TASK-018); a kept ID has the prefix stripped. A master
sees exactly the IDs it issued, and two of its requests with one ID keep one
fabric ID, so they stay ordered. A slave port's declared `id_width` must be at least
`XBAR_ID_WIDTH`; the validator rejects a narrower AXI3/AXI4/AXI5 slave.
Responses are routed by the master index the slave adapter returns with
them: the BID/RID prefix bits for a multi-master AXI3/AXI4/AXI5 slave (any
completion order), or an in-order FIFO for single-master bridges and shim
slaves (request order required, bridge BUG-008). See HAS 3.2.

Either way a slave may interleave R beats of different IDs, as AXI4
allows; beats of one ID stay in order. The per-master-path R arbiters
re-arbitrate every beat, so bursts from two slaves interleave toward a
master rather than one holding the path through RLAST, and the read width
converters convert each beat against its own ID's state as it arrives
(`R_INTERLEAVE = 1`). Until 2026-10-18 slaves had to return each R burst
contiguously.

## Channel-Specific Interfaces

### Write-Only Master (wr)

Only AW, W, B channels generated:

```systemverilog
// Write Address Channel
input  logic [ADDR_WIDTH-1:0] descr_m_axi_awaddr,
input  logic [ID_WIDTH-1:0]   descr_m_axi_awid,
// ... full AW channel

// Write Data Channel
input  logic [DATA_WIDTH-1:0] descr_m_axi_wdata,
input  logic [STRB_WIDTH-1:0] descr_m_axi_wstrb,
// ... full W channel

// Write Response Channel
output logic [ID_WIDTH-1:0]   descr_m_axi_bid,
output logic [1:0]            descr_m_axi_bresp,
// ... full B channel

// NO AR or R channels
```

### Read-Only Master (rd)

Only AR, R channels generated:

```systemverilog
// Read Address Channel
input  logic [ADDR_WIDTH-1:0] src_m_axi_araddr,
input  logic [ID_WIDTH-1:0]   src_m_axi_arid,
// ... full AR channel

// Read Data Channel
output logic [DATA_WIDTH-1:0] src_m_axi_rdata,
output logic [ID_WIDTH-1:0]   src_m_axi_rid,
// ... full R channel

// NO AW, W, or B channels
```

## Monitor Bus Output (when `variants` includes `mon`)

When monitor collection is enabled (via the bridge TOML `variants` list including `"mon"`), each bridge instance exposes a unified monitor interface at the bridge top level:

| Signal | Type | Width | Direction | Description |
|--------|------|-------|-----------|-------------|
| `s_mon_axil_*` | AXIL Slave | 32-bit addr, 64-bit data | Input | Monitor packet read interface for CPU consumption |
| `m_axil_mon_*` | AXIL Master | 32-bit addr, 64-bit data | Output | Monitor packet write interface for bulk trace capture |
| `stream_irq` | logic | 1-bit | Output | Interrupt signal (asserted when error FIFO has records) |

: Monitor Bus Output

Per-port collection comes from the `axi4_master_{rd,wr}_monlite` and `axi4_slave_{rd,wr}_monlite` wrappers (`axi_monitor_lite`; the full `_mon` wrappers are no longer used in generated bridges, 2026-09-26).

**Packet Format:** the canonical 128-bit packet layout and field definitions live in `docs/markdown/rtl-amba/includes/ocelus_package_spec.md` — see that reference for bit-field descriptions, protocol-type enumerations, and packet-type codes.

## Handshake Protocol

### Valid/Ready Handshake

All channels use AXI4 valid/ready handshake:

```
Transfer occurs when: VALID && READY
```

### Backpressure

- Bridge asserts READY when able to accept
- Masters must hold VALID until READY
- Bridge does not drop transactions

## Burst Support

### Supported Burst Types

| AWBURST/ARBURST | Type | Description |
|-----------------|------|-------------|
| 2'b00 | FIXED | Same address each beat |
| 2'b01 | INCR | Incrementing address |
| 2'b10 | WRAP | Wrapping at boundary |
| 2'b11 | Reserved | Not used |

: Supported Burst Types

### Burst Length

- AWLEN/ARLEN: 8-bit field
- Length = AXLEN + 1 (1 to 256 beats)
- Burst does not cross 4KB boundary (AXI4 rule)
