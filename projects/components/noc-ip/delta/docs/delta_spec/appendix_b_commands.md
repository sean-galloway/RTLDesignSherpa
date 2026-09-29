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

# Appendix B: Configuration Commands

## B.1 Command Code Reference

| Code | Command | Payload | Description |
|------|---------|---------|-------------|
| 0x0001 | SET_ROUTING_MODE | context_id[1:0] | Change routing context (mesh/systolic/tree/custom) |
| 0x0002 | UPDATE_ROUTE_TABLE | table_idx[7:0], entry[31:0] | Update custom routing table entry |
| 0x0004 | SET_PRIORITY_WEIGHTS | vc0_wt[7:0], vc1_wt[7:0] | Adjust VC arbitration weights |
| 0x0008 | FLUSH_BUFFERS | none | Drain all router buffers |
| 0x0010 | RESET_STATISTICS | none | Clear packet counters |
| 0x0020 | SET_CONGESTION_THRESHOLD | threshold[7:0] | Set buffer occupancy threshold for congestion flag |
| 0x0040 | CONFIG_PREPARE | none | Prepare for context switch (quiesce network) |
| 0x0080 | CONFIG_ACTIVATE | none | Resume operation after context switch |
| 0x0100 | ENABLE_FILTER | types[3:0] | Enable packet type filtering |
| 0x0200 | DISABLE_FILTER | none | Disable packet type filtering |

## B.2 Broadcast vs Unicast

**Broadcast (tile_mask = 0xFFFF):**
- Reaches all 16 tiles
- Used for global configuration (context switch, reset stats)

**Multicast (tile_mask = subset):**
- Reaches specific tiles
- Example: Configure row 2 only (mask = 0x0F00)

**Unicast (tile_mask = single bit):**
- Reaches one tile
- Example: Update custom route on tile 7 (mask = 0x0080)

## B.3 Command Examples

### Example 1: Global Context Switch

```c
// Switch all tiles to systolic mode
pkt_config_t cmd;
cmd.tile_mask = 0xFFFF;              // All tiles
cmd.command = CMD_SET_ROUTING_MODE;
cmd.payload = CONTEXT_SYSTOLIC;      // Mode 1
send_config_packet(&cmd);
```

### Example 2: Configure Row 2 for Higher Priority

```c
// Set VC0 weight higher for tiles 8-11
pkt_config_t cmd;
cmd.tile_mask = 0x0F00;              // Tiles 8-11 (row 2)
cmd.command = CMD_SET_PRIORITY_WEIGHTS;
cmd.payload = (8 << 8) | 2;          // VC0=8, VC1=2
send_config_packet(&cmd);
```

### Example 3: Update Custom Route on Tile 7

```c
// Custom route: Tile 7 sends PKT_DATA to tile 10 via EAST port
pkt_config_t cmd;
cmd.tile_mask = 0x0080;              // Tile 7 only
cmd.command = CMD_UPDATE_ROUTE_TABLE;
cmd.payload = (0 << 8) | (2 << 0) | (10 << 3) | (PKT_DATA << 7);
//             ^table  ^port E   ^dest 10   ^pkt type
send_config_packet(&cmd);
```

---

**Back to:** [Index](delta_index.md)
