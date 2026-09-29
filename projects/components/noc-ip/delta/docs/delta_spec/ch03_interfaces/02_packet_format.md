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

# 2. Packet Format and Framing

## 2.1 Packet Examples

### PKT_DATA (Activation Transfer from RAPIDS to Tile)

```
TDATA  = {activation_data}  (128 bits per beat)
TKEEP  = 16'hFFFF            (all bytes valid)
TLAST  = 1                   (single flit, or =1 on final)
TUSER  = 2'b00               (PKT_DATA)
TID    = 4'd2                (priority level - set by RAPIDS MM2S)
TDEST  = 4'd5                (destination: tile 5)
```

### PKT_DATA (Results from Tile 7 back to RAPIDS)

```
TDATA  = {result_data}       (128 bits per beat)
TKEEP  = 16'hFFFF
TLAST  = 1
TUSER  = 2'b00               (PKT_DATA)
TID    = 4'd7                (CRITICAL: source tile ID - set by Tile 7 NI)
TDEST  = 4'd16               (destination: RAPIDS virtual tile)

// RAPIDS receives this and uses TID=7 to route to S2MM Channel 7
```

### PKT_DESC (DMA Descriptor from HIVE-C)

```
Beat 0:
TDATA  = descriptor[127:0]
TLAST  = 0
TUSER  = 2'b01               (PKT_DESC)
TID    = 4'd0                (high priority)
TDEST  = 4'd16               (destination: RAPIDS)

Beat 1:
TDATA  = descriptor[255:128]
TLAST  = 1
```

### PKT_CONFIG (Broadcast to All Tiles)

```
TDATA  = {tile_mask[31:0], command[31:0], payload[63:0]}
TLAST  = 1
TUSER  = 2'b10               (PKT_CONFIG)
TID    = 4'd0                (broadcast identifier)
TDEST  = 4'd15               (doesn't matter for broadcast)
                              (tile_mask determines actual targets)
```

### PKT_STATUS (SERV Report from Tile 3 to HIVE-C)

```
TDATA  = {tile_id[7:0], status_type[7:0], timestamp[47:0], data[63:0]}
TLAST  = 1
TUSER  = 2'b11               (PKT_STATUS)
TID    = 4'd3                (reporting tile ID - matches TDATA[127:120])
TDEST  = 4'd17               (destination: HIVE-C)
```

## 2.2 Payload Structure by Packet Type

### PKT_DATA Payload

```
TDATA[127:0] = data_payload
    [127:0]  : Actual data (activations, weights, results)
```

### PKT_DESC Payload (256 bits = 2 flits)

```
Beat 0 TDATA[127:0]:
    [63:0]   : source_address (DDR address for MM2S)
    [127:64] : dest_address (DDR address for S2MM)

Beat 1 TDATA[127:0]:
    [31:0]   : length (bytes to transfer)
    [35:32]  : dest_tile_id or source_tile_id
    [39:36]  : operation (MM2S=0, S2MM=1)
    [127:40] : reserved/control
```

### PKT_CONFIG Payload

```
TDATA[127:0]:
    [31:0]   : tile_mask (32 bits, one per potential tile)
    [63:32]  : command_code
    [127:64] : command_payload
```

### PKT_STATUS Payload

```
TDATA[127:0]:
    [7:0]    : tile_id (reporting tile)
    [15:8]   : status_type (congestion, error, periodic)
    [63:16]  : timestamp (48-bit cycle counter)
    [127:64] : status_data (type-specific)
```

---

**Next:** [External Entity Integration](03_external_entities.md)
