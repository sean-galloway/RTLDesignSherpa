# 3. Performance Counters

## 3.1 Packet Count Registers

### PKT_COUNT_TX Register (Offset 0x34)

```
Bits [31:0]: packet_count_tx (transmitted packets from this tile)

Counter increments on each TLAST sent from local port
Wraps at 2^32 - 1
```

### PKT_COUNT_RX Register (Offset 0x38)

```
Bits [31:0]: packet_count_rx (received packets to this tile)

Counter increments on each TLAST received at local port
Wraps at 2^32 - 1
```

## 3.2 Performance Monitoring Example

```c
// Monitor tile 7 packet rate
void monitor_tile_7(void) {
    uint32_t tx_start = read_reg_tile(7, PKT_COUNT_TX);
    uint32_t rx_start = read_reg_tile(7, PKT_COUNT_RX);
    
    // Wait 1 second (100M cycles @ 100 MHz)
    delay_cycles(100000000);
    
    uint32_t tx_end = read_reg_tile(7, PKT_COUNT_TX);
    uint32_t rx_end = read_reg_tile(7, PKT_COUNT_RX);
    
    uint32_t tx_rate = tx_end - tx_start;  // Packets/second
    uint32_t rx_rate = rx_end - rx_start;  // Packets/second
    
    printf("Tile 7: TX=%u pkt/s, RX=%u pkt/s\n", tx_rate, rx_rate);
}
```

## 3.3 Congestion Detection via Status Polling

```c
// Check for congestion across all tiles
void detect_congestion(void) {
    for (uint8_t tile = 0; tile < 16; tile++) {
        uint32_t status = read_reg_tile(tile, STATUS);
        uint8_t router_state = status & 0x7;
        
        if (router_state == 0b010) {  // CONGESTED
            // Extract buffer occupancies
            uint8_t north_occ = (status >> 3) & 0x1F;
            uint8_t south_occ = (status >> 8) & 0x1F;
            // ... other directions ...
            
            printf("Tile %u congested: N=%u S=%u\n", tile, north_occ, south_occ);
            
            // Take action: reduce injection rate, reroute traffic, etc.
        }
    }
}
```

## 3.4 SERV Monitor Integration

SERV monitors can read these registers and generate PKT_STATUS reports:

```c
// SERV firmware on each tile
void serv_monitor_loop(void) {
    while (1) {
        // Read local router status
        uint32_t status = read_local_reg(STATUS);
        uint8_t router_state = status & 0x7;
        
        if (router_state == 0b010) {  // Congested
            // Build status packet
            pkt_status_t pkt;
            pkt.tile_id = MY_TILE_ID;
            pkt.type = STATUS_CONGESTION;
            pkt.timestamp = get_cycle_count();
            pkt.data = status;  // Full status register
            
            // Inject via AXIS (TUSER=PKT_STATUS, TDEST=17 for HIVE-C)
            inject_status_packet(&pkt);
        }
        
        // Periodic monitoring
        delay(MONITOR_INTERVAL);
    }
}
```

---

**Back to:** [Configuration Register Bank](01_config_registers.md) | **Next:** [Appendix A - Tile Coordinates](../appendix_a_coordinates.md)
