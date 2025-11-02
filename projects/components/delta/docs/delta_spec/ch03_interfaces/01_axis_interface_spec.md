# 1. AXIS Interface Specification

## 1.1 AXIS Signal Mapping

All network links use AXIS with these signals:

```verilog
// 128-bit data path
logic [127:0] TDATA;   // Payload (flit data)
logic [15:0]  TKEEP;   // Byte enables (usually all 1's)
logic         TLAST;   // End of packet marker
logic [1:0]   TUSER;   // Packet type (PKT_DATA/DESC/CONFIG/STATUS)
logic [3:0]   TID;     // Source tile ID (for PKT_DATA) or priority/sequence
logic [3:0]   TDEST;   // Destination tile (0-17)
logic         TVALID;  // Data valid
logic         TREADY;  // Receiver ready (backpressure)
```

## 1.2 TID Field Usage

**CRITICAL:** The TID field serves different purposes based on packet type:

| Packet Type | TID Meaning | Set By | Preserved By Router |
|-------------|-------------|--------|---------------------|
| PKT_DATA (to RAPIDS) | Source Tile ID (0-15) | Tile NI (enforced) | Yes - never modified |
| PKT_DATA (to Tiles) | Priority/Sequence | RAPIDS MM2S | Yes |
| PKT_DESC | Priority Level | HIVE-C | Yes |
| PKT_CONFIG | Broadcast ID | HIVE-C/SERV | Yes |
| PKT_STATUS | Reporting Tile ID | SERV (= MY_TILE_ID) | Yes |

### Router TID Handling

Routers NEVER modify TID field - it flows end-to-end from source to destination:

```verilog
// Routers NEVER modify TID field
// It flows end-to-end from source to destination
always_ff @(posedge clk) begin
    if (input_valid && output_ready) begin
        output_tid <= input_tid;  // Pass through unchanged
    end
end
```

## 1.3 Multi-Flit Packets

### Single-Flit Packet (<=128 bits)

```
Beat 0: TDATA[127:0] = payload
        TLAST = 1
        TUSER = packet type
        TDEST = destination
```

### Multi-Flit Packet (>128 bits)

```
Beat 0: TDATA[127:0] = payload[127:0]
        TLAST = 0

Beat 1: TDATA[127:0] = payload[255:128]
        TLAST = 0

Beat N: TDATA[127:0] = payload[...]
        TLAST = 1  (final beat)

Note: TUSER, TDEST carried only on first beat
      Router caches for subsequent beats
```

## 1.4 AXIS Handshaking

Standard AXIS ready/valid protocol:

```verilog
// Transfer occurs when both valid and ready are high
always_ff @(posedge clk) begin
    if (tvalid && tready) begin
        // Data transfer completes
        // Receiver captures tdata, tuser, tdest, etc.
    end
end

// Backpressure: Receiver asserts tready=0 to stall
// Source must hold tvalid=1 and all data stable until tready=1
```

## 1.5 Timing Diagram

```
         ___     ___     ___     ___     ___
clk    _|   |___|   |___|   |___|   |___|   |___

tvalid ________/```````````````\___________

tready ````````\___/```````````````````````

tdata  XXXXXXXX<D0><D1><D1><D2>XXXXXXXXXXX
                     ^   ^
                     |   |
       No transfer   |   Transfer completes
       (not ready)   |
                     Stall (data held)
```

---

**Next:** [Packet Format and Framing](02_packet_format.md)
