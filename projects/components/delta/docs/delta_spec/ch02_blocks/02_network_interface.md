# 2. Network Interface (NI)

## 2.1 Per-Tile Network Interface

Each tile has a Network Interface connecting the compute element to the router:

```
+------------------------------------------------+
|         Network Interface (Tile i)             |
|                                                |
|  From Compute Element / SERV Monitor:         |
|  +----------------------------------+          |
|  |  Injection Port (AXIS Master)    |          |
|  |  - Accepts from local sources    |          |
|  |  - Packetizes if needed          |          |
|  |  - Sets TUSER based on source:   |          |
|  |    • Compute -> PKT_DATA          |          |
|  |    • SERV -> PKT_CONFIG/STATUS    |          |
|  |  - Sets TDEST from local logic   |          |
|  +------------+---------------------+          |
|               |                                |
|               v                                |
|  +----------------------------------+          |
|  |  Packet Filter & Validator       |          |
|  |  - Checks local permissions       |          |
|  |  - Prevents unauthorized types    |          |
|  |  - Rate limits if configured      |          |
|  +------------+---------------------+          |
|               |                                |
|               v                                |
|          To Router                             |
|               |                                |
|               v                                |
|  From Router:                                  |
|  +----------------------------------+          |
|  |  Reception Port (AXIS Slave)      |          |
|  |  - Receives packets for this tile |          |
|  |  - Filters by TUSER:              |          |
|  |    • PKT_DATA -> Compute Element   |          |
|  |    • PKT_CONFIG -> Config Regs     |          |
|  |    • Others -> Drop/Error          |          |
|  +------------+---------------------+          |
|               |                                |
+---------------+--------------------------------+
                |
                v
    To Compute Element / Config Registers
```

## 2.2 Packet Filtering Rules

Each NI enforces these rules:

### Injection (Tile -> Network)

```verilog
// Compute elements can only send PKT_DATA
if (source == COMPUTE && pkt_tuser != PKT_DATA) begin
    reject_packet();
    set_error_flag(ERR_UNAUTHORIZED_TYPE);
end

// CRITICAL: Compute elements MUST set TID to own tile ID
// This allows RAPIDS to route incoming data to correct S2MM channel
if (source == COMPUTE && pkt_tuser == PKT_DATA) begin
    // Hardware enforces TID = MY_TILE_ID for data from compute
    pkt_tid_override = MY_TILE_ID[3:0];
end

// SERV monitors can send PKT_CONFIG (local) or PKT_STATUS (to HIVE-C)
if (source == SERV && !(pkt_tuser inside {PKT_CONFIG, PKT_STATUS})) begin
    reject_packet();
    set_error_flag(ERR_UNAUTHORIZED_TYPE);
end
```

### Reception (Network -> Tile)

```verilog
case (pkt_tuser)
    PKT_DATA: begin
        // Route to compute element
        forward_to_compute();
    end

    PKT_CONFIG: begin
        // Route to configuration registers
        forward_to_config_regs();
    end

    PKT_DESC, PKT_STATUS: begin
        // Not valid for regular tiles
        drop_packet();
        set_error_flag(ERR_INVALID_DEST);
    end
endcase
```

## 2.3 TID Enforcement

**CRITICAL: Network Interface Hardware Enforcement**

The TID field serves different purposes based on packet type. The NI hardware enforces correct TID values:

| Packet Type | TID Meaning | Set By | Enforced By NI |
|-------------|-------------|--------|----------------|
| PKT_DATA (to RAPIDS) | Source Tile ID (0-15) | NI (forced) | YES - override |
| PKT_DATA (to Tiles) | Priority/Sequence | RAPIDS MM2S | NO - pass through |
| PKT_DESC | Priority Level | HIVE-C | NO - pass through |
| PKT_CONFIG | Broadcast ID | HIVE-C/SERV | NO - pass through |
| PKT_STATUS | Reporting Tile ID | NI (forced) | YES - override |

**TID Override Logic:**

```verilog
// Network Interface enforces TID for specific packet types
always_comb begin
    if (pkt_source == LOCAL_COMPUTE && pkt_tuser == PKT_DATA) begin
        // Override TID to this tile's ID
        pkt_tid_out = MY_TILE_ID[3:0];
    end else if (pkt_source == LOCAL_SERV && pkt_tuser == PKT_STATUS) begin
        // Override TID to this tile's ID for status reports
        pkt_tid_out = MY_TILE_ID[3:0];
    end else begin
        // Pass through original TID
        pkt_tid_out = pkt_tid_in;
    end
end
```

---

**Next:** [Packet Classifier](03_packet_classifier.md)
