# Error Handling and Recovery

**Chapter:** 05.05
**Version:** 1.0
**Last Updated:** 2025-12-01

---

## Overview

This guide covers error detection, reporting, and recovery procedures for the STREAM DMA engine.

---

## Error Types

### AXI Protocol Errors

| Error | Response | Cause |
|-------|----------|-------|
| SLVERR (2'b10) | Slave error | Memory protection violation, invalid address |
| DECERR (2'b11) | Decode error | Address not mapped to any slave |

### Timeout Errors

| Error | Trigger | Detection |
|-------|---------|-----------|
| Descriptor fetch timeout | AR → R exceeds threshold | SCHED_ERROR register |
| Read data timeout | AR → RLAST exceeds threshold | RDMON packet |
| Write response timeout | AW → B exceeds threshold | WRMON packet |

### Internal Errors

| Error | Description | Detection |
|-------|-------------|-----------|
| Invalid descriptor | Valid bit not set | Channel enters ERROR state |
| FIFO overflow | Internal FIFO full | MON_FIFO_STATUS register |
| ID conflict | Transaction ID reused | Monitor status registers |

---

## Error Detection Registers

### SCHED_ERROR (0x170)

Per-channel scheduler error flags (sticky).

```c
uint32_t sched_error = read32(STREAM_BASE + 0x170);

// Check each channel
for (int ch = 0; ch < 8; ch++) {
    if (sched_error & (1 << ch)) {
        printf("Channel %d: Scheduler error\n", ch);
    }
}
```

### AXI_RD_COMPLETE (0x174) / AXI_WR_COMPLETE (0x178)

Per-channel completion status. If channel is idle but completion bit not set, error may have occurred.

```c
uint32_t ch_idle = read32(STREAM_BASE + 0x128);
uint32_t rd_complete = read32(STREAM_BASE + 0x174);
uint32_t wr_complete = read32(STREAM_BASE + 0x178);

// Check for incomplete transfer
uint32_t ch_mask = (1 << channel);
if ((ch_idle & ch_mask) && !(rd_complete & ch_mask)) {
    printf("Channel %d: Read incomplete\n", channel);
}
if ((ch_idle & ch_mask) && !(wr_complete & ch_mask)) {
    printf("Channel %d: Write incomplete\n", channel);
}
```

### MON_FIFO_STATUS (0x180)

Monitor FIFO status (if USE_AXI_MONITORS=1).

```c
uint32_t mon_status = read32(STREAM_BASE + 0x180);

#define MON_FIFO_FULL   (1 << 0)
#define MON_FIFO_EMPTY  (1 << 1)
#define MON_FIFO_OVFL   (1 << 2)
#define MON_FIFO_UNFL   (1 << 3)

if (mon_status & MON_FIFO_OVFL) {
    printf("Monitor FIFO overflow - packets lost\n");
}
```

### Channel State Registers (0x140-0x15F)

```c
#define CH_ERROR 0x20  // Error state (bit 5)

uint32_t ch_state = read32(STREAM_BASE + 0x140 + (channel * 4));
if (ch_state == CH_ERROR) {
    printf("Channel %d in error state\n", channel);
}
```

---

## Error Handling Procedures

### Procedure 1: Single Channel Error Recovery

```c
/**
 * Recover from error on a single channel
 * @param channel Channel number (0-7)
 * @return 0 on success, -1 if recovery failed
 */
int channel_error_recovery(int channel) {
    volatile uint32_t *regs = (volatile uint32_t *)STREAM_BASE;
    uint32_t ch_mask = (1 << channel);

    // 1. Log error state
    uint32_t sched_error = regs[0x170/4];
    uint32_t ch_state = regs[(0x140 + channel * 4)/4];
    printf("Channel %d error: sched_error=0x%02x, state=0x%02x\n",
           channel, sched_error, ch_state);

    // 2. Disable channel (prevent new operations)
    uint32_t ch_enable = regs[0x120/4];
    regs[0x120/4] = ch_enable & ~ch_mask;

    // 3. Assert channel reset
    regs[0x124/4] = ch_mask;

    // 4. Wait for reset (minimum 10 cycles, use 100us for safety)
    usleep(100);

    // 5. Release reset
    regs[0x124/4] = 0;

    // 6. Wait for channel to return to IDLE
    int timeout = 100;
    while (timeout-- > 0) {
        uint32_t state = regs[(0x140 + channel * 4)/4];
        if (state == 0x01) {  // CH_IDLE
            break;
        }
        usleep(100);
    }

    if (timeout <= 0) {
        printf("Channel %d failed to return to IDLE\n", channel);
        return -1;
    }

    // 7. Re-enable channel
    regs[0x120/4] = ch_enable;

    // 8. Clear any pending errors (read-to-clear if applicable)
    // SCHED_ERROR is typically sticky, cleared by reset

    printf("Channel %d recovered\n", channel);
    return 0;
}
```

### Procedure 2: Global Error Recovery

```c
/**
 * Full STREAM reset and recovery
 */
int stream_global_recovery(void) {
    volatile uint32_t *regs = (volatile uint32_t *)STREAM_BASE;

    // 1. Disable global enable
    regs[0x100/4] = 0;

    // 2. Reset all channels
    regs[0x124/4] = 0xFF;
    usleep(100);
    regs[0x124/4] = 0;

    // 3. Wait for all channels idle
    int timeout = 100;
    while (timeout-- > 0) {
        uint32_t ch_idle = regs[0x128/4];
        if (ch_idle == 0xFF) break;
        usleep(100);
    }

    if (timeout <= 0) {
        printf("STREAM global recovery failed\n");
        return -1;
    }

    // 4. Re-initialize STREAM
    stream_init(STREAM_BASE);

    printf("STREAM global recovery complete\n");
    return 0;
}
```

### Procedure 3: Timeout Error Handling

```c
/**
 * Handle timeout error
 */
int handle_timeout_error(int channel) {
    // 1. Increase timeout threshold
    uint32_t current_timeout = read32(STREAM_BASE + 0x204);
    write32(STREAM_BASE + 0x204, current_timeout * 2);

    // 2. Recover channel
    channel_error_recovery(channel);

    // 3. Optionally disable timeout temporarily for debug
    // uint32_t sched_ctrl = read32(STREAM_BASE + 0x200);
    // write32(STREAM_BASE + 0x200, sched_ctrl & ~(1 << 1));  // Disable timeout

    return 0;
}
```

---

## Interrupt-Based Error Handling

### Interrupt Service Routine

```c
void stream_isr(void) {
    volatile uint32_t *regs = (volatile uint32_t *)STREAM_BASE;

    // Check scheduler errors
    uint32_t sched_error = regs[0x170/4];
    if (sched_error) {
        for (int ch = 0; ch < 8; ch++) {
            if (sched_error & (1 << ch)) {
                // Queue error recovery for this channel
                queue_error_recovery(ch);
            }
        }
    }

    // Check monitor FIFO (if using AXI-Lite error FIFO)
    uint32_t mon_status = regs[0x180/4];
    if (!(mon_status & MON_FIFO_EMPTY)) {
        // Process error packets from FIFO
        process_error_fifo();
    }

    // Check completion status
    uint32_t rd_complete = regs[0x174/4];
    uint32_t wr_complete = regs[0x178/4];

    // Signal completion to waiting threads
    for (int ch = 0; ch < 8; ch++) {
        uint32_t mask = (1 << ch);
        if ((rd_complete & mask) && (wr_complete & mask)) {
            signal_completion(ch);
        }
    }
}
```

### Error FIFO Processing (AXI-Lite)

```c
/**
 * Read and process error packets from monitor error FIFO
 * (via s_axil_err_* interface)
 */
void process_error_fifo(void) {
    volatile uint32_t *err_fifo = (volatile uint32_t *)AXIL_ERR_BASE;

    while (1) {
        // Check if FIFO empty
        uint32_t status = read32(STREAM_BASE + 0x180);
        if (status & MON_FIFO_EMPTY) break;

        // Read 64-bit packet (two reads)
        uint32_t pkt_low = err_fifo[0];   // Read from AXIL slave
        uint32_t pkt_high = err_fifo[1];  // Auto-advances FIFO

        // Parse packet
        uint8_t pkt_type = (pkt_high >> 24) & 0xFF;
        uint8_t agent_id = (pkt_high >> 16) & 0xFF;
        uint8_t channel = (pkt_high >> 8) & 0xFF;

        printf("Error packet: type=%02x, agent=%02x, channel=%d, data=%08x\n",
               pkt_type, agent_id, channel, pkt_low);

        // Handle specific error types
        switch (pkt_type) {
            case 0x10:  // AXI SLVERR
                handle_axi_error(channel, "SLVERR", pkt_low);
                break;
            case 0x11:  // AXI DECERR
                handle_axi_error(channel, "DECERR", pkt_low);
                break;
            case 0x20:  // Timeout
                handle_timeout_error(channel);
                break;
            default:
                printf("Unknown error type: 0x%02x\n", pkt_type);
        }
    }
}
```

---

## Debugging Error Conditions

### Enable Verbose Monitoring

```c
void enable_debug_monitoring(void) {
    // Enable all packet types on monitors
    write32(STREAM_BASE + 0x24C, 0xFFFF);  // DAXMON_PKT_MASK
    write32(STREAM_BASE + 0x26C, 0xFFFF);  // RDMON_PKT_MASK
    write32(STREAM_BASE + 0x28C, 0xFFFF);  // WRMON_PKT_MASK

    // Enable debug masks
    write32(STREAM_BASE + 0x25C, 0xFF00FF);  // DAXMON debug + addr masks
    write32(STREAM_BASE + 0x27C, 0xFF00FF);  // RDMON debug + addr masks
    write32(STREAM_BASE + 0x29C, 0xFF00FF);  // WRMON debug + addr masks

    printf("Debug monitoring enabled\n");
}
```

### Dump Channel State

```c
void dump_channel_state(int channel) {
    volatile uint32_t *regs = (volatile uint32_t *)STREAM_BASE;

    printf("=== Channel %d State ===\n", channel);

    // Channel enable/reset
    uint32_t ch_enable = regs[0x120/4];
    uint32_t ch_reset = regs[0x124/4];
    printf("Enable: %d, Reset: %d\n",
           (ch_enable >> channel) & 1,
           (ch_reset >> channel) & 1);

    // Channel status
    uint32_t ch_idle = regs[0x128/4];
    uint32_t desc_idle = regs[0x12C/4];
    uint32_t sched_idle = regs[0x130/4];
    printf("Idle: %d, DescEng: %d, Sched: %d\n",
           (ch_idle >> channel) & 1,
           (desc_idle >> channel) & 1,
           (sched_idle >> channel) & 1);

    // Channel FSM state
    uint32_t ch_state = regs[(0x140 + channel * 4)/4];
    const char *state_names[] = {
        "IDLE", "FETCH_DESC", "XFER_DATA", "COMPLETE",
        "NEXT_DESC", "ERROR", "RESERVED"
    };
    int state_idx = 0;
    for (int i = 0; i < 7; i++) {
        if (ch_state & (1 << i)) {
            state_idx = i;
            break;
        }
    }
    printf("State: %s (0x%02x)\n", state_names[state_idx], ch_state);

    // Errors and completion
    uint32_t sched_error = regs[0x170/4];
    uint32_t rd_complete = regs[0x174/4];
    uint32_t wr_complete = regs[0x178/4];
    printf("Error: %d, RdComplete: %d, WrComplete: %d\n",
           (sched_error >> channel) & 1,
           (rd_complete >> channel) & 1,
           (wr_complete >> channel) & 1);
}
```

---

## Common Error Scenarios

### Scenario 1: Address Decode Error (DECERR)

**Symptom:** Channel enters ERROR state immediately after kick-off

**Cause:** Descriptor address not mapped in system

**Solution:**
```c
// Verify descriptor address is valid
if (!is_valid_dma_address(desc_phys)) {
    printf("Invalid descriptor address: 0x%llx\n", desc_phys);
    return -1;
}
```

### Scenario 2: Memory Protection Error (SLVERR)

**Symptom:** Transfer fails mid-operation

**Cause:** Source or destination address in protected region

**Solution:**
```c
// Verify source/destination are DMA-accessible
if (!is_dma_accessible(src_addr) || !is_dma_accessible(dst_addr)) {
    printf("Address not DMA-accessible\n");
    return -1;
}
```

### Scenario 3: Timeout During High Load

**Symptom:** Intermittent timeout errors under heavy system load

**Cause:** Memory latency exceeds configured timeout

**Solution:**
```c
// Increase timeout based on system load
void adjust_timeout_for_load(int load_factor) {
    uint32_t base_timeout = 10000;
    write32(STREAM_BASE + 0x204, base_timeout * load_factor);
}
```

### Scenario 4: Invalid Descriptor

**Symptom:** Channel enters ERROR state after descriptor fetch

**Cause:** Descriptor valid bit not set, or corrupted descriptor

**Solution:**
```c
// Always verify descriptor before kick-off
void verify_descriptor(stream_descriptor_t *desc) {
    if (!(desc->control & DESC_VALID)) {
        printf("Descriptor valid bit not set!\n");
    }
    if (desc->length == 0) {
        printf("Descriptor length is zero!\n");
    }
}
```

---

## Related Documentation

- **[Single Transfer](02_single_transfer.md)** - Basic transfer operation
- **[Register Map](../ch04_registers/register_map.md)** - Error register definitions
- **[Configuration Reference](../ch06_configuration/config_reference.md)** - Timeout configuration

---

**Last Updated:** 2025-12-01
