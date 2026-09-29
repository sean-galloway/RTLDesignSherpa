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

# 3. Packet Classifier

## 3.1 Purpose

The Packet Classifier examines packet headers (TUSER, TDEST) and determines the appropriate output port based on the configured routing algorithm.

## 3.2 Classification Flow

```
Packet arrives at input buffer
         |
         v
+------------------+
| Extract Header   |
| - TUSER[1:0]     |
| - TDEST[3:0]     |
| - TID[3:0]       |
+--------+---------+
         |
         v
+------------------+
| Decode Pkt Type  |
| PKT_DATA    (00) |
| PKT_DESC    (01) |
| PKT_CONFIG  (10) |
| PKT_STATUS  (11) |
+--------+---------+
         |
         v
+------------------+
| Route by Type    |
| See logic below  |
+--------+---------+
         |
         v
    Output Port
   (N/S/E/W/L)
```

## 3.3 Routing Logic by Packet Type

### PKT_DATA (0b00)

Route to compute tile or RAPIDS based on TDEST:

```verilog
if (pkt_tdest == 4'd16) begin
    // Destination: RAPIDS DMA (virtual tile 16)
    route_to_virtual_tile(16);  // Via tile 12 south port
end else if (pkt_tdest < 4'd16) begin
    // Destination: Physical tile 0-15
    route_via_xy_algorithm(current_tile, pkt_tdest);
end else begin
    // Invalid destination
    drop_packet();
    set_error_flag(ERR_INVALID_DEST);
end
```

### PKT_DESC (0b01)

Always route to RAPIDS (only valid destination):

```verilog
// PKT_DESC always goes to RAPIDS (virtual tile 16)
route_to_virtual_tile(16);
```

### PKT_CONFIG (0b10)

Route to tile(s) based on tile mask in payload:

```verilog
// Extract tile mask from payload
logic [31:0] tile_mask = pkt_data[127:96];

// Check if this tile is targeted
if (tile_mask[MY_TILE_ID] == 1'b1) begin
    // Accept locally
    output_port = PORT_LOCAL;

    // Also continue forwarding if other tiles targeted
    if (tile_mask & ~(1 << MY_TILE_ID)) begin
        // Determine next hop via XY routing
        // to reach remaining tiles in mask
        continue_forwarding();
    end
end else begin
    // Not for this tile, forward to next hop
    route_via_xy_algorithm(current_tile, next_tile_in_mask);
end
```

### PKT_STATUS (0b11)

Always route to HIVE-C monitoring aggregator:

```verilog
// PKT_STATUS always goes to HIVE-C (virtual tile 17)
route_to_virtual_tile(17);
```

## 3.4 XY Routing Implementation

```verilog
function [2:0] xy_route(
    input [3:0] current,
    input [3:0] destination
);
    logic [1:0] curr_x, curr_y;
    logic [1:0] dest_x, dest_y;

    // Extract coordinates
    curr_x = current[1:0];     // Column
    curr_y = current[3:2];     // Row

    dest_x = destination[1:0]; // Dest column
    dest_y = destination[3:2]; // Dest row

    // X-dimension first (deadlock-free)
    if (dest_x < curr_x) begin
        return PORT_WEST;
    end else if (dest_x > curr_x) begin
        return PORT_EAST;
    end else if (dest_y < curr_y) begin
        return PORT_NORTH;
    end else if (dest_y > curr_y) begin
        return PORT_SOUTH;
    end else begin
        return PORT_LOCAL;  // Arrived
    end
endfunction
```

## 3.5 Virtual Tile Handling

Special logic for virtual tiles (RAPIDS=16, HIVE-C=17):

```verilog
function [2:0] route_to_virtual_tile(
    input [3:0] virtual_id
);
    if (virtual_id == 16) begin
        // RAPIDS: Route to tile 12, then south
        if (MY_TILE_ID == 12) begin
            return PORT_SOUTH;  // Exit to RAPIDS
        end else begin
            return xy_route(MY_TILE_ID, 12);  // Route to tile 12
        end
    end else if (virtual_id == 17) begin
        // HIVE-C: Route to tile 3, then north
        if (MY_TILE_ID == 3) begin
            return PORT_NORTH;  // Exit to HIVE-C
        end else begin
            return xy_route(MY_TILE_ID, 3);  // Route to tile 3
        end
    end
endfunction
```

## 3.6 Performance

- **Classification latency:** 1 cycle (combinational + 1 FF stage)
- **Complexity:** O(1) - constant time for all packet types
- **Resources:** ~200 LUTs, ~150 FFs per router

---

**Next:** [Virtual Channel Allocator](04_virtual_channel_allocator.md)
