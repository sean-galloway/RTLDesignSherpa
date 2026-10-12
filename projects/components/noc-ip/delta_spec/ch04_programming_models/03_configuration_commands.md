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

# 3. Configuration Commands

## 3.1 Common PKT_CONFIG Commands

```
Command Code: 0x0001 - SET_ROUTING_MODE
  Payload[1:0] = context_id (0-3)
  
Command Code: 0x0002 - UPDATE_ROUTE_TABLE
  Payload[7:0]  = table_index
  Payload[39:8] = route_entry
  
Command Code: 0x0004 - SET_PRIORITY_WEIGHTS
  Payload[7:0]   = vc0_weight
  Payload[15:8]  = vc1_weight
  
Command Code: 0x0008 - FLUSH_BUFFERS
  No payload
  
Command Code: 0x0010 - RESET_STATISTICS
  No payload
  
Command Code: 0x0020 - SET_CONGESTION_THRESHOLD
  Payload[7:0] = threshold (buffer occupancy)

Command Code: 0x0040 - CONFIG_PREPARE
  No payload (prepares for context switch)

Command Code: 0x0080 - CONFIG_ACTIVATE
  No payload (activates after context switch)
```

## 3.2 Command Packet Structure

```
TDATA[127:0]:
  [31:0]   : tile_mask (which tiles to configure)
  [63:32]  : command_code (see above)
  [127:64] : command_payload (command-specific)

TLAST = 1 (single flit for most commands)
TUSER = 2'b10 (PKT_CONFIG)
TID = broadcast_id or priority
TDEST = ignored (tile_mask determines targets)
```

## 3.3 Response Handling

Most configuration commands do not generate responses. Status can be polled via:

```c
// Read router status register
uint32_t read_router_status(uint8_t tile_id) {
    // Addressed read via control interface
    // OR wait for periodic PKT_STATUS report
}
```

---

**Next:** [Complete System Flow](04_system_flow.md)
