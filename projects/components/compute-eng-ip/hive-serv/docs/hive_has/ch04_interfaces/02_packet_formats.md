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

# Packet Formats and Routing Rules

All HIVE control traffic is AXIS packets classified by `tuser[1:0]`. These
encodings are shared with the Delta Network contract — Delta owns the routing,
HIVE owns the packet classes and payloads.

## AXIS Packet Classification

```verilog
// AXIS TUSER[1:0] encoding
typedef enum logic [1:0] {
    PKT_DATA   = 2'b00,  // Compute data (activations, weights, results)
    PKT_CDA    = 2'b01,  // DMA descriptor ("CDA", Compute Direct Access)
    PKT_CONFIG = 2'b10,  // Configuration command
    PKT_STATUS = 2'b11   // Status/monitoring data
} packet_type_t;
```

> **Naming note:** early drafts called 2'b01 `PKT_DESC`; current docs and the
> Delta contract call it CDA. `PKT_CDA` is the spelling to use in RTL.

**Routing rules:**

- `PKT_DATA` — routed through the Delta mesh to compute tiles
- `PKT_CDA` — routed to the RAPIDS DMA descriptor queue (virtual tile 16)
- `PKT_CONFIG` — routed to tile configuration registers / router config
- `PKT_STATUS` — routed to the HIVE-C monitoring aggregator (virtual tile 17)

---

## CDA Descriptor Format (256-bit)

RAPIDS descriptors injected by HIVE-C (one per packet, single beat):

```
Bits [255:192]: Source Address (64-bit)
Bits [191:128]: Destination Address (64-bit)
Bits [127:96]:  Transfer Length (32-bit, in bytes)
Bits [95:64]:   2D Stride Configuration (32-bit)
Bits [63:32]:   Control Flags (32-bit)
Bits [31:0]:    Next Descriptor Pointer (32-bit)

Control Flags [31:0]:
  [31:28] - Burst Size (AXI beats)
  [27:24] - Burst Type (FIXED/INCR/WRAP)
  [23:20] - Priority Level (0-15)
  [19:16] - Destination Tile ID
  [15:12] - Source Tile ID (S2MM channel select; see below)
  [11:8]  - Completion Interrupt Vector
  [7]     - Enable 2D Transfer
  [6]     - Enable Scatter-Gather (follow next ptr)
  [5]     - Generate Completion Interrupt
  [4]     - Cache Coherent Access (reserved in PoC; no coherence fabric)
  [3:0]   - Descriptor Type (future expansion)
```

: CDA descriptor field map

**Channel-aware programming:** for S2MM (stream-to-memory) descriptors, the
source tile ID field selects which RAPIDS S2MM channel the descriptor arms;
RAPIDS matches that channel against the `tid` of incoming result packets from
the tiles. HIVE-C must program S2MM descriptors with the exact tile IDs it
expects results from — the identity mapping `channel = tile_id` is the PoC
convention.

---

## PKT_CONFIG Format (128-bit)

```
Bits [127:96]:  Target Tile Mask (32-bit, one bit per tile)
Bits [95:64]:   Configuration Command (32-bit)
Bits [63:0]:    Payload Data (64-bit)

Command Types:
  0x0000_0001: Set Routing Mode (payload = context ID)
  0x0000_0002: Update Router Table Entry
  0x0000_0004: Set Traffic Priority Weights
  0x0000_0008: Enable/Disable Tile
  0x0000_0010: Flush Local Buffers
  0x0000_0020: Reset Statistics Counters
  0x0000_0040: Update Clock Divider
  0x0000_0080: Set Debug Trace Mode
```

: PKT_CONFIG field map

The target tile mask allows a single broadcast packet to configure multiple
tiles simultaneously — the mechanism that makes atomic context switching
possible (all routers update mode in the same cycle).

---

## PKT_STATUS Format (128-bit)

```
Bits [127:120]: Source Tile ID (8-bit)
Bits [119:112]: Status Type (8-bit)
Bits [111:64]:  Timestamp (48-bit cycle counter)
Bits [63:0]:    Payload (type-dependent)

Status Types:
  0x01: Traffic Statistics (packet counts)
  0x02: Buffer Occupancy Report
  0x04: Congestion Alert
  0x08: Error/Exception Report
  0x10: Performance Counter Snapshot
  0x20: Debug Trace Data
```

: PKT_STATUS field map

The 48-bit timestamp is in the producer's clock domain; HIVE-C interprets
status freshness by interval, not by absolute timestamp comparison across
domains.

---

## TID Enforcement Rule

When compute elements send PKT_DATA back toward RAPIDS, the tile Network
Interface **overrides `tid` with the local tile ID**:

```systemverilog
// Network Interface (NI) TX path for compute-element traffic
always_comb begin
    if (source == COMPUTE_ELEMENT && axis_tuser == PKT_DATA) begin
        // Override: RAPIDS must receive the true source tile ID
        axis_tx_tid_out = MY_TILE_ID[3:0];
    end else begin
        // SERV packets (CONFIG, STATUS) pass TID through
        axis_tx_tid_out = axis_tx_tid_in;
    end
end
```

This guarantees four properties:
1. Tiles cannot spoof source ID (security and correctness)
2. RAPIDS always receives the accurate `tid` for S2MM channel routing
3. Compute elements need not know their own tile ID
4. SERV monitors retain free use of `tid` for status identification

Protocol checkers at tile boundaries should flag any compute-element
PKT_DATA whose `tid` disagrees with the egress port's tile ID.

---

**Last Updated:** 2026-10-12
