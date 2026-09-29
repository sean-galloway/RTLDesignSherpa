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

# 3. Packet Type Routing

## 3.1 AXIS TUSER Encoding

All AXIS interfaces use this encoding:

```verilog
// All AXIS interfaces use this encoding
typedef enum logic [1:0] {
    PKT_DATA   = 2'b00,  // Compute data (activations, weights, results)
    PKT_DESC   = 2'b01,  // DMA descriptor (HIVE-C -> RAPIDS only)
    PKT_CONFIG = 2'b10,  // Configuration command (HIVE-C/SERV -> Tiles)
    PKT_STATUS = 2'b11   // Status/monitoring (SERV -> HIVE-C)
} packet_type_t;
```

## 3.2 Routing Decision Logic

Each router examines TUSER[1:0] and TDEST[3:0]:

```verilog
always_comb begin
    case (pkt_tuser)
        PKT_DATA: begin
            // Route to compute tile or RAPIDS
            if (pkt_tdest == 4'd16) begin
                route_to_rapids();  // Virtual tile 16
            end else if (pkt_tdest < 4'd16) begin
                route_to_tile(pkt_tdest);  // Tile 0-15
            end else begin
                drop_packet();  // Invalid destination
            end
        end

        PKT_DESC: begin
            // Always route to RAPIDS (only valid destination)
            route_to_rapids();
        end

        PKT_CONFIG: begin
            // Route to tile(s) based on mask in payload
            // Supports multicast for broadcast configs
            route_by_tile_mask();
        end

        PKT_STATUS: begin
            // Always route to HIVE-C monitoring aggregator
            route_to_hive_c();  // Virtual tile 17
        end
    endcase
end
```

## 3.3 Virtual Tile Mapping

DELTA extends the 4x4 physical mesh with virtual tiles:

| Tile ID | Type | Location | Purpose |
|---------|------|----------|---------|
| 0-15 | Physical | Mesh positions (0,0) to (3,3) | Compute tiles |
| 16 | Virtual | External (south of tile 12) | RAPIDS DMA |
| 17 | Virtual | External (north of tile 3) | HIVE-C controller |

## Routing to Virtual Tiles

- Tile 16 (RAPIDS): Reached via tile 12 south port
- Tile 17 (HIVE-C): Reached via tile 3 north port
- Physical routing unaffected (XY still works)

---

**Next:** [Acronyms and References](04_acronyms.md)
