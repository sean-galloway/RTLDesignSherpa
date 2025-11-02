# 2. Context Switching Mechanism

## 2.1 Switching Sequence

```
1. HIVE-C issues CONFIG_PREPARE command (PKT_CONFIG broadcast)
   - All tiles flush in-flight packets
   - Routers enter quiescent state
   - FIFOs drain (5-10 cycles)

2. HIVE-C broadcasts SET_ROUTING_MODE with context ID
   - Mode register updated: MODE_SELECT <- context_id
   - Routing table pointer switched
   - All routers update simultaneously (1 cycle)

3. HIVE-C issues CONFIG_ACTIVATE command
   - Tiles resume packet injection
   - Network operational in new mode

Total switching time: 10-20 cycles (deterministic)
```

## 2.2 Example: Switch from Mesh to Systolic

```c
// HIVE-C firmware code
void switch_to_systolic_mode(void) {
    // Step 1: Prepare for context switch
    pkt_config_t prep_pkt;
    prep_pkt.tile_mask = 0xFFFF;  // All 16 tiles
    prep_pkt.command = CMD_CONFIG_PREPARE;
    send_config_packet(&prep_pkt);
    
    // Wait for quiescence
    delay_cycles(10);
    
    // Step 2: Set new routing mode
    pkt_config_t mode_pkt;
    mode_pkt.tile_mask = 0xFFFF;
    mode_pkt.command = CMD_SET_ROUTING_MODE;
    mode_pkt.payload = CONTEXT_SYSTOLIC;  // Context 1
    send_config_packet(&mode_pkt);
    
    // Single-cycle update
    delay_cycles(1);
    
    // Step 3: Activate network
    pkt_config_t act_pkt;
    act_pkt.tile_mask = 0xFFFF;
    act_pkt.command = CMD_CONFIG_ACTIVATE;
    send_config_packet(&act_pkt);
    
    // Network now in systolic mode
}
```

## 2.3 Context Switch Timing

```
Cycle 0:   PREPARE command sent
Cycle 1-5: Packets in flight drain
Cycle 6:   Quiescent state reached
Cycle 7:   SET_ROUTING_MODE command sent
Cycle 8:   All routers update MODE_SELECT
Cycle 9:   ACTIVATE command sent
Cycle 10:  Network operational in new mode

Total: 10 cycles (deterministic)
```

---

**Next:** [Configuration Commands](03_configuration_commands.md)
