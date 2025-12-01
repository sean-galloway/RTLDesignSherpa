# Multi-Channel Operations

**Chapter:** 05.04
**Version:** 1.0
**Last Updated:** 2025-12-01

---

## Overview

STREAM supports 8 independent DMA channels that share common resources. This guide covers concurrent channel operations, priority management, and resource sharing strategies.

---

## Channel Architecture

### Shared Resources

All 8 channels share the following resources:

| Resource | Type | Impact |
|----------|------|--------|
| Descriptor Fetch AXI Master | 256-bit read | Channels take turns fetching descriptors |
| Data Read AXI Master | 512-bit (configurable) | Shared bandwidth for source reads |
| Data Write AXI Master | 512-bit (configurable) | Shared bandwidth for destination writes |
| SRAM Buffer | Configurable depth | Shared storage for in-flight data |
| MonBus Reporter | 64-bit packets | Shared monitoring infrastructure |

### Channel Independence

Despite shared resources, each channel maintains:
- Independent descriptor chains
- Independent FSM state
- Independent completion status
- Independent error flags

---

## Channel Management Registers

### CHANNEL_ENABLE (0x120)

Enable/disable individual channels:

```c
#define REG_CHANNEL_ENABLE  0x120

// Enable specific channels
void enable_channels(uint8_t channel_mask) {
    write32(STREAM_BASE + REG_CHANNEL_ENABLE, channel_mask);
}

// Examples:
enable_channels(0xFF);  // All 8 channels
enable_channels(0x0F);  // Channels 0-3 only
enable_channels(0x01);  // Channel 0 only
```

### CHANNEL_RESET (0x124)

Reset individual channels (self-clearing):

```c
#define REG_CHANNEL_RESET  0x124

// Reset specific channels
void reset_channels(uint8_t channel_mask) {
    write32(STREAM_BASE + REG_CHANNEL_RESET, channel_mask);
    // Bits auto-clear after reset completes
}
```

### CHANNEL_IDLE (0x140)

Check which channels are idle:

```c
#define REG_CHANNEL_IDLE  0x140

uint8_t get_idle_channels(void) {
    return read32(STREAM_BASE + REG_CHANNEL_IDLE) & 0xFF;
}

// Check if specific channel is idle
int is_channel_idle(int channel) {
    return (get_idle_channels() >> channel) & 1;
}
```

---

## Concurrent Channel Operations

### Starting Multiple Channels

```c
/**
 * Kick off multiple channels concurrently
 * @param desc_addrs Array of descriptor addresses (one per channel)
 * @param channel_mask Bitmask of channels to start
 */
void start_channels(uint64_t *desc_addrs, uint8_t channel_mask) {
    // Kick off each enabled channel
    for (int ch = 0; ch < 8; ch++) {
        if (channel_mask & (1 << ch)) {
            stream_kick_off(ch, desc_addrs[ch]);
        }
    }
}

// Example: Start 4 channels with different descriptors
uint64_t descriptors[8] = {
    0x10000000,  // Channel 0 descriptor
    0x10001000,  // Channel 1 descriptor
    0x10002000,  // Channel 2 descriptor
    0x10003000,  // Channel 3 descriptor
    0, 0, 0, 0   // Channels 4-7 not used
};

start_channels(descriptors, 0x0F);  // Start channels 0-3
```

### Waiting for Multiple Channels

```c
/**
 * Wait for all specified channels to complete
 * @param channel_mask Bitmask of channels to wait for
 * @param timeout_ms Maximum wait time in milliseconds
 * @return 0 on success, -1 on timeout, channel number on error
 */
int wait_all_channels(uint8_t channel_mask, int timeout_ms) {
    volatile uint32_t *regs = (volatile uint32_t *)STREAM_BASE;
    int elapsed = 0;

    while (elapsed < timeout_ms) {
        // Check for errors on any channel
        uint32_t sched_error = regs[0x170/4];
        uint8_t error_channels = sched_error & channel_mask;
        if (error_channels) {
            // Return first channel with error
            for (int ch = 0; ch < 8; ch++) {
                if (error_channels & (1 << ch)) {
                    return ch + 1;  // Positive = error on channel
                }
            }
        }

        // Check if all channels complete
        uint32_t ch_idle = regs[0x140/4];
        uint32_t rd_complete = regs[0x174/4];
        uint32_t wr_complete = regs[0x178/4];

        uint8_t complete = (ch_idle & rd_complete & wr_complete) & channel_mask;
        if (complete == channel_mask) {
            return 0;  // All complete
        }

        usleep(1000);
        elapsed++;
    }

    return -1;  // Timeout
}
```

### Polling Individual Channels

```c
/**
 * Check completion status of individual channels
 * @return Bitmask of completed channels
 */
uint8_t poll_completed_channels(void) {
    volatile uint32_t *regs = (volatile uint32_t *)STREAM_BASE;

    uint32_t ch_idle = regs[0x140/4];
    uint32_t rd_complete = regs[0x174/4];
    uint32_t wr_complete = regs[0x178/4];

    return (ch_idle & rd_complete & wr_complete) & 0xFF;
}

// Usage: Process channels as they complete
void process_channel_completions(uint8_t channel_mask) {
    uint8_t pending = channel_mask;

    while (pending) {
        uint8_t completed = poll_completed_channels() & pending;

        for (int ch = 0; ch < 8; ch++) {
            if (completed & (1 << ch)) {
                printf("Channel %d completed\n", ch);
                process_channel_result(ch);
                pending &= ~(1 << ch);
            }
        }

        usleep(100);  // Brief delay before next poll
    }
}
```

---

## Priority-Based Operation

### Descriptor Priority Field

Each descriptor contains an 8-bit priority field:

```c
#define DESC_PRIORITY(p) ((uint64_t)(p) << 8)

// Higher value = higher priority
// Range: 0 (lowest) to 255 (highest)

// Set priority when building descriptor
desc->control = DESC_VALID | DESC_PRIORITY(128);  // Medium priority
```

### Priority Scheduling

When multiple channels compete for shared resources:

1. **Higher priority** channels serviced first
2. **Equal priority** channels use round-robin arbitration
3. **Starvation prevention** via timeout mechanism

### Priority Configuration Example

```c
/**
 * Configure multi-channel priority scheme for video processing
 */
void configure_video_priorities(void) {
    // High priority: Real-time video stream
    // Medium priority: Display output
    // Low priority: Background processing

    // Channel 0: Video input (highest priority)
    video_desc.control = DESC_VALID | DESC_PRIORITY(255);

    // Channel 1: Display output (high priority)
    display_desc.control = DESC_VALID | DESC_PRIORITY(200);

    // Channel 2: Audio (high priority, time-sensitive)
    audio_desc.control = DESC_VALID | DESC_PRIORITY(200);

    // Channels 3-7: Background tasks (lower priority)
    for (int i = 3; i < 8; i++) {
        background_desc[i].control = DESC_VALID | DESC_PRIORITY(50);
    }
}
```

---

## Resource Sharing Strategies

### Strategy 1: Dedicated Channel Assignment

Assign specific channels to specific functions:

```c
// Channel assignment
#define CH_VIDEO_IN      0
#define CH_VIDEO_OUT     1
#define CH_AUDIO         2
#define CH_NETWORK       3
#define CH_BACKGROUND_0  4
#define CH_BACKGROUND_1  5
#define CH_BACKGROUND_2  6
#define CH_BACKGROUND_3  7

// Each subsystem uses its dedicated channel
void start_video_input(uint64_t desc_addr) {
    stream_kick_off(CH_VIDEO_IN, desc_addr);
}
```

### Strategy 2: Channel Pooling

Use available channels dynamically:

```c
/**
 * Acquire an idle channel from pool
 * @return Channel number (0-7) or -1 if none available
 */
int acquire_channel(void) {
    uint8_t idle = get_idle_channels();
    uint8_t enabled = read32(STREAM_BASE + REG_CHANNEL_ENABLE) & 0xFF;

    // Find first idle and enabled channel
    uint8_t available = idle & enabled;
    for (int ch = 0; ch < 8; ch++) {
        if (available & (1 << ch)) {
            return ch;
        }
    }

    return -1;  // No channel available
}

/**
 * Release channel back to pool
 */
void release_channel(int channel) {
    // Channel becomes available automatically when idle
    // Optionally reset to clear any state
    // reset_channels(1 << channel);
}

// Usage: Dynamic channel allocation
int ch = acquire_channel();
if (ch >= 0) {
    stream_kick_off(ch, desc_addr);
    wait_channel_complete(ch, timeout);
    release_channel(ch);
}
```

### Strategy 3: Load Balancing

Distribute work across multiple channels:

```c
/**
 * Distribute large transfer across multiple channels
 * @param src Base source address
 * @param dst Base destination address
 * @param total_size Total transfer size in bytes
 * @param num_channels Number of channels to use (1-8)
 */
int parallel_transfer(uint64_t src, uint64_t dst, size_t total_size, int num_channels) {
    if (num_channels > 8) num_channels = 8;

    size_t chunk_size = (total_size + num_channels - 1) / num_channels;
    chunk_size = (chunk_size + 63) & ~63;  // Align to 64 bytes

    descriptor_chain_t *chains[8];
    uint8_t channel_mask = 0;

    // Create one descriptor per channel
    for (int ch = 0; ch < num_channels; ch++) {
        size_t offset = ch * chunk_size;
        size_t remaining = total_size - offset;
        size_t this_size = (remaining < chunk_size) ? remaining : chunk_size;

        if (this_size == 0) break;

        chains[ch] = alloc_chain(1);
        chain_add_transfer(chains[ch], src + offset, dst + offset, this_size);
        chain_finalize(chains[ch], (ch == num_channels - 1));  // IRQ on last only

        stream_kick_off(ch, chains[ch]->phys_base);
        channel_mask |= (1 << ch);
    }

    // Wait for all channels
    int result = wait_all_channels(channel_mask, 30000);

    // Cleanup
    for (int ch = 0; ch < num_channels; ch++) {
        if (channel_mask & (1 << ch)) {
            free_chain(chains[ch]);
        }
    }

    return result;
}
```

---

## Performance Considerations

### Bandwidth Sharing

With shared AXI masters, bandwidth is divided among active channels:

| Active Channels | Per-Channel Bandwidth |
|-----------------|----------------------|
| 1 | 100% |
| 2 | ~50% each |
| 4 | ~25% each |
| 8 | ~12.5% each |

**Note:** Actual bandwidth depends on memory latency, burst sizes, and priority settings.

### Optimal Channel Usage

| Scenario | Recommended Channels | Rationale |
|----------|---------------------|-----------|
| Single large transfer | 1-2 | Maximize per-channel bandwidth |
| Multiple independent transfers | 4-8 | Hide memory latency |
| Mixed size transfers | 2-4 | Balance throughput and latency |
| Real-time + background | 2 + 6 | Dedicate channels by priority |

### SRAM Buffer Sizing

When using multiple channels, SRAM buffer usage increases:

```c
// Rule of thumb:
// Buffer per channel = burst_size * outstanding_transactions
// Total buffer = num_active_channels * buffer_per_channel

// Example: 8 channels, 16-beat bursts, 4 outstanding per channel
// Buffer needed = 8 * 16 * 4 * 64 bytes = 32KB minimum
```

---

## Complete Example: Multi-Channel Video Processing

```c
/**
 * Video frame processing with multi-channel DMA
 * - Channel 0: Input frame read
 * - Channel 1: Processed frame write
 * - Channel 2-3: Overlay data transfers
 */
int process_video_frame(uint64_t input_frame, uint64_t output_frame,
                        uint64_t overlay_src, uint64_t overlay_dst,
                        size_t frame_size) {

    // Initialize channels
    write32(STREAM_BASE + REG_CHANNEL_ENABLE, 0x0F);  // Enable CH0-3

    // Build descriptors with appropriate priorities
    stream_descriptor_t *input_desc = alloc_descriptor();
    build_copy_descriptor(input_desc, input_frame, SRAM_BASE, frame_size, 0);
    input_desc->control |= DESC_PRIORITY(255);  // Highest

    stream_descriptor_t *output_desc = alloc_descriptor();
    build_copy_descriptor(output_desc, PROCESSED_BASE, output_frame, frame_size, 1);
    output_desc->control |= DESC_PRIORITY(250);  // High

    stream_descriptor_t *overlay0_desc = alloc_descriptor();
    build_copy_descriptor(overlay0_desc, overlay_src, overlay_dst, OVERLAY_SIZE, 0);
    overlay0_desc->control |= DESC_PRIORITY(100);  // Medium

    stream_descriptor_t *overlay1_desc = alloc_descriptor();
    build_copy_descriptor(overlay1_desc, overlay_src + OVERLAY_SIZE,
                         overlay_dst + OVERLAY_SIZE, OVERLAY_SIZE, 0);
    overlay1_desc->control |= DESC_PRIORITY(100);  // Medium

    // Flush all descriptors
    cache_flush(input_desc, sizeof(*input_desc));
    cache_flush(output_desc, sizeof(*output_desc));
    cache_flush(overlay0_desc, sizeof(*overlay0_desc));
    cache_flush(overlay1_desc, sizeof(*overlay1_desc));

    // Start all channels
    stream_kick_off(0, virt_to_phys(input_desc));
    stream_kick_off(1, virt_to_phys(output_desc));
    stream_kick_off(2, virt_to_phys(overlay0_desc));
    stream_kick_off(3, virt_to_phys(overlay1_desc));

    // Wait for completion
    int result = wait_all_channels(0x0F, 16);  // 16ms timeout (60fps budget)

    // Cleanup
    free(input_desc);
    free(output_desc);
    free(overlay0_desc);
    free(overlay1_desc);

    return result;
}
```

---

## Troubleshooting Multi-Channel Issues

### Issue: Channel Starvation

**Symptom:** Low-priority channel never completes

**Solution:**
```c
// Ensure no extreme priority differences
// Use priorities 50-200 for most transfers
// Reserve 255 for time-critical only
// Check timeout settings (allows lower priority through)
```

### Issue: Unexpected Ordering

**Symptom:** Channels complete in unexpected order

**Cause:** Arbitration depends on many factors

**Solution:**
```c
// If ordering matters, use explicit synchronization:
// 1. Start channel A
// 2. Wait for channel A complete
// 3. Start channel B
// Or use descriptor chaining on single channel
```

### Issue: Performance Degradation

**Symptom:** Total throughput lower than expected with many channels

**Solution:**
```c
// Reduce active channel count
// Increase burst sizes
// Ensure SRAM buffer large enough
// Check for memory contention external to STREAM
```

---

## Related Documentation

- **[Single Transfer](02_single_transfer.md)** - Basic transfer operation
- **[Chained Transfers](03_chained_transfers.md)** - Descriptor chains
- **[Error Handling](05_error_handling.md)** - Error recovery

---

**Last Updated:** 2025-12-01
