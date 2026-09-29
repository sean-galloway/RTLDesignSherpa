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

# 3. External Entity Integration

## 3.1 RAPIDS and HIVE-C Connections

RAPIDS and HIVE-C are not in the mesh but have dedicated connections:

```
Tile Layout:
      HIVE-C (virtual 17)
         ^
         | (north port)
    +----+----+----+----+
    | T0 | T1 | T2 | T3 |
    +----+----+----+----+
    | T4 | T5 | T6 | T7 |
    +----+----+----+----+
    | T8 | T9 | T10| T11|
    +----+----+----+----+
    | T12| T13| T14| T15|
    +----+----+----+----+
         | (south port)
         v
    RAPIDS (virtual 16)
```

## 3.2 RAPIDS (Virtual Tile 16)

**Connection:**
- Physically connected to Router 12 (tile 12) south port
- All PKT_DESC packets routed to tile 12 first, then south
- PKT_DATA from RAPIDS enters at tile 12, routes normally

**Interface Signals:**

```verilog
// RAPIDS -> DELTA (injection)
logic [127:0] rapids_tx_tdata;
logic [15:0]  rapids_tx_tkeep;
logic         rapids_tx_tlast;
logic [1:0]   rapids_tx_tuser;   // Always PKT_DATA (2'b00)
logic [3:0]   rapids_tx_tid;     // Priority from descriptor
logic [3:0]   rapids_tx_tdest;   // Target tile (0-15)
logic         rapids_tx_tvalid;
logic         rapids_tx_tready;  // From Router 12

// DELTA -> RAPIDS (reception)
logic [127:0] rapids_rx_tdata;
logic [15:0]  rapids_rx_tkeep;
logic         rapids_rx_tlast;
logic [1:0]   rapids_rx_tuser;   // PKT_DATA or PKT_DESC
logic [3:0]   rapids_rx_tid;     // Source tile ID (for PKT_DATA)
logic [3:0]   rapids_rx_tdest;   // Always 16 (RAPIDS)
logic         rapids_rx_tvalid;
logic         rapids_rx_tready;  // From RAPIDS
```

**Routing to RAPIDS:**

```verilog
// Any tile sending to TDEST=16 routes to tile 12
// Example: Tile 7 -> Tile 11 -> Tile 15 -> Tile 14 -> Tile 13 -> Tile 12 -> RAPIDS
```

## 3.3 HIVE-C (Virtual Tile 17)

**Connection:**
- Physically connected to Router 3 (tile 3) north port
- All PKT_STATUS packets routed to tile 3 first, then north
- PKT_DESC/CONFIG from HIVE-C enters at tile 3, routes normally

**Interface Signals:**

```verilog
// HIVE-C -> DELTA (injection)
logic [127:0] hive_tx_tdata;
logic [15:0]  hive_tx_tkeep;
logic         hive_tx_tlast;
logic [1:0]   hive_tx_tuser;   // PKT_DESC (2'b01) or PKT_CONFIG (2'b10)
logic [3:0]   hive_tx_tid;     // Priority or broadcast ID
logic [3:0]   hive_tx_tdest;   // Target tile or 16 (RAPIDS for DESC)
logic         hive_tx_tvalid;
logic         hive_tx_tready;  // From Router 3

// DELTA -> HIVE-C (reception)
logic [127:0] hive_rx_tdata;
logic [15:0]  hive_rx_tkeep;
logic         hive_rx_tlast;
logic [1:0]   hive_rx_tuser;   // Always PKT_STATUS (2'b11)
logic [3:0]   hive_rx_tid;     // Reporting tile ID
logic [3:0]   hive_rx_tdest;   // Always 17 (HIVE-C)
logic         hive_rx_tvalid;
logic         hive_rx_tready;  // From HIVE-C
```

**Routing to HIVE-C:**

```verilog
// Any tile sending to TDEST=17 routes to tile 3
// Example: Tile 12 -> Tile 8 -> Tile 4 -> Tile 0 -> Tile 1 -> Tile 2 -> Tile 3 -> HIVE-C
```

## 3.4 Special Routing Cases

### Broadcast Configuration

PKT_CONFIG packets can target multiple tiles simultaneously:

```verilog
// Packet payload contains 32-bit tile mask
logic [31:0] tile_mask = pkt_data[127:96];

// Each router checks if it's targeted
if (tile_mask[my_tile_id] == 1'b1) begin
    // Accept packet locally
    forward_to_local_config();

    // Also forward to next hop if other tiles targeted
    if (tile_mask & ~(1 << my_tile_id)) begin
        continue_forwarding();
    end
end
```

**Example: Configure all tiles in row 2:**
```
tile_mask = 32'h0000_0F00  // Bits 8-11 set (tiles 8-11)
Each router 8-11 accepts locally and forwards
```

### Peer-to-Peer Data

Tiles can send PKT_DATA directly to each other:

```
Scenario: Tile 3 sends result to Tile 10

Tile 3 coords: col=3, row=0
Tile 10 coords: col=2, row=2

Step 1: X-dimension (col 3 -> col 2): go WEST
  R3 sends to R2
Step 2: X-dimension complete (col 2 == col 2)
Step 3: Y-dimension (row 0 -> row 2): go SOUTH
  R2 sends to R6 (row 1)
  R6 sends to R10 (row 2)
Step 4: Arrived at R10, send to local port

Total hops: 3 (R3->R2, R2->R6, R6->R10)
Latency: 3 hops × 3 cycles = 9 cycles (mesh mode)
```

---

**Back to:** [AXIS Interface Specification](01_axis_interface_spec.md) | **Next Chapter:** [Virtual Configuration Contexts](../ch04_programming_models/01_virtual_contexts.md)
