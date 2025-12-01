# Single Transfer Programming

**Chapter:** 05.02
**Version:** 1.0
**Last Updated:** 2025-12-01

---

## Overview

This guide demonstrates how to perform a single DMA transfer using STREAM. A single transfer involves one descriptor that copies data from a source address to a destination address.

---

## Descriptor Format

STREAM uses 256-bit (32-byte) descriptors:

```
Descriptor Memory Layout (256 bits = 32 bytes):
+--------+--------+--------+--------+--------+--------+--------+--------+
| Byte 0 |   1    |   2    |   3    |   4    |   5    |   6    |   7    |  src_addr [63:0]
+--------+--------+--------+--------+--------+--------+--------+--------+
| Byte 8 |   9    |  10    |  11    |  12    |  13    |  14    |  15    |  dst_addr [63:0]
+--------+--------+--------+--------+--------+--------+--------+--------+
| Byte 16|  17    |  18    |  19    |  20    |  21    |  22    |  23    |  length [31:0] | next_ptr [31:0]
+--------+--------+--------+--------+--------+--------+--------+--------+
| Byte 24|  25    |  26    |  27    |  28    |  29    |  30    |  31    |  control [63:0]
+--------+--------+--------+--------+--------+--------+--------+--------+

Control Field Bits:
  [0]   valid          - Descriptor is valid (must be 1)
  [1]   gen_irq        - Generate interrupt on completion
  [2]   last           - Last descriptor in chain
  [3]   error          - Error flag (read-only, set by hardware)
  [7:4] channel_id     - Channel ID (informational for debug)
  [15:8] desc_priority - Transfer priority (higher = higher priority)
```

---

## Kick-Off Address Map

Each channel has two APB registers for the 64-bit descriptor address:

| Channel | LOW Register | HIGH Register | Description |
|---------|--------------|---------------|-------------|
| 0 | 0x000 | 0x004 | Channel 0 kick-off |
| 1 | 0x008 | 0x00C | Channel 1 kick-off |
| 2 | 0x010 | 0x014 | Channel 2 kick-off |
| 3 | 0x018 | 0x01C | Channel 3 kick-off |
| 4 | 0x020 | 0x024 | Channel 4 kick-off |
| 5 | 0x028 | 0x02C | Channel 5 kick-off |
| 6 | 0x030 | 0x034 | Channel 6 kick-off |
| 7 | 0x038 | 0x03C | Channel 7 kick-off |

**Write Sequence:** Write LOW first, then HIGH. Transfer starts after HIGH write completes.

---

## Simple Memory Copy Example

### Step 1: Allocate and Initialize Descriptor

```c
#include <stdint.h>
#include <string.h>

// Descriptor structure (must match hardware layout)
typedef struct __attribute__((packed)) {
    uint64_t src_addr;           // [63:0]   Source address
    uint64_t dst_addr;           // [127:64] Destination address
    uint32_t length;             // [159:128] Length in BEATS
    uint32_t next_descriptor_ptr; // [191:160] Next descriptor (0 = last)
    uint64_t control;            // [255:192] Control bits
} stream_descriptor_t;

// Control field helpers
#define DESC_VALID      (1ULL << 0)
#define DESC_GEN_IRQ    (1ULL << 1)
#define DESC_LAST       (1ULL << 2)
#define DESC_PRIORITY(p) ((uint64_t)(p) << 8)

// Calculate length in beats from bytes
// DATA_WIDTH = 512 bits = 64 bytes per beat
#define BYTES_TO_BEATS(bytes) (((bytes) + 63) / 64)

// Allocate descriptor (must be 32-byte aligned for descriptor fetch)
stream_descriptor_t *alloc_descriptor(void) {
    void *ptr;
    if (posix_memalign(&ptr, 32, sizeof(stream_descriptor_t)) != 0) {
        return NULL;
    }
    memset(ptr, 0, sizeof(stream_descriptor_t));
    return (stream_descriptor_t *)ptr;
}
```

### Step 2: Build the Descriptor

```c
/**
 * Build a simple memory copy descriptor
 * @param desc      Pointer to descriptor (must be 32-byte aligned)
 * @param src       Source physical address (must be 64-byte aligned)
 * @param dst       Destination physical address (must be 64-byte aligned)
 * @param size      Transfer size in bytes
 * @param irq       Generate interrupt on completion
 */
void build_copy_descriptor(stream_descriptor_t *desc,
                           uint64_t src, uint64_t dst,
                           size_t size, int irq) {
    desc->src_addr = src;
    desc->dst_addr = dst;
    desc->length = BYTES_TO_BEATS(size);
    desc->next_descriptor_ptr = 0;  // No chaining (single descriptor)

    desc->control = DESC_VALID | DESC_LAST;
    if (irq) {
        desc->control |= DESC_GEN_IRQ;
    }
    // Priority 0 (default)
}
```

### Step 3: Kick Off the Transfer

```c
#define STREAM_BASE 0x10000000  // Platform-specific

/**
 * Start a DMA transfer on specified channel
 * @param channel   Channel number (0-7)
 * @param desc_addr Physical address of descriptor
 */
void stream_kick_off(int channel, uint64_t desc_addr) {
    volatile uint32_t *regs = (volatile uint32_t *)STREAM_BASE;

    // Calculate kick-off register offsets
    // Each channel uses 8 bytes (2 x 32-bit registers)
    uint32_t low_offset = (channel * 8) / 4;       // 0x00, 0x08, 0x10, ...
    uint32_t high_offset = low_offset + 1;         // 0x04, 0x0C, 0x14, ...

    // Write LOW first, then HIGH (transfer starts after HIGH)
    regs[low_offset] = (uint32_t)(desc_addr & 0xFFFFFFFF);
    regs[high_offset] = (uint32_t)(desc_addr >> 32);
}
```

### Step 4: Wait for Completion

```c
#define REG_CHANNEL_IDLE     0x128
#define REG_SCHED_ERROR      0x170
#define REG_AXI_RD_COMPLETE  0x174
#define REG_AXI_WR_COMPLETE  0x178

/**
 * Wait for channel to complete or error
 * @param channel Channel number (0-7)
 * @return 0 on success, -1 on error, -2 on timeout
 */
int stream_wait_complete(int channel, int timeout_ms) {
    volatile uint32_t *regs = (volatile uint32_t *)STREAM_BASE;
    uint32_t ch_mask = (1 << channel);
    int elapsed = 0;

    while (elapsed < timeout_ms) {
        // Check for error
        uint32_t sched_error = regs[REG_SCHED_ERROR/4];
        if (sched_error & ch_mask) {
            return -1;  // Error occurred
        }

        // Check for idle (transfer complete)
        uint32_t ch_idle = regs[REG_CHANNEL_IDLE/4];
        uint32_t rd_complete = regs[REG_AXI_RD_COMPLETE/4];
        uint32_t wr_complete = regs[REG_AXI_WR_COMPLETE/4];

        if ((ch_idle & ch_mask) &&
            (rd_complete & ch_mask) &&
            (wr_complete & ch_mask)) {
            return 0;  // Success
        }

        usleep(1000);  // 1ms delay
        elapsed++;
    }

    return -2;  // Timeout
}
```

---

## Complete Example: 4KB Memory Copy

```c
/**
 * Copy 4KB from source to destination using STREAM channel 0
 */
int example_4kb_copy(uint64_t src_phys, uint64_t dst_phys) {
    // 1. Allocate and build descriptor
    stream_descriptor_t *desc = alloc_descriptor();
    if (!desc) return -1;

    build_copy_descriptor(desc, src_phys, dst_phys, 4096, 1);

    // 2. Get physical address of descriptor
    uint64_t desc_phys = virt_to_phys(desc);

    // 3. Flush descriptor to memory (ensure coherency)
    cache_flush(desc, sizeof(*desc));

    // 4. Kick off transfer on channel 0
    stream_kick_off(0, desc_phys);

    // 5. Wait for completion (5 second timeout)
    int result = stream_wait_complete(0, 5000);

    // 6. Invalidate destination cache
    cache_invalidate((void *)phys_to_virt(dst_phys), 4096);

    // 7. Free descriptor
    free(desc);

    return result;
}
```

---

## Alignment Requirements

| Item | Alignment | Reason |
|------|-----------|--------|
| Descriptor address | 32 bytes | 256-bit AXI fetch |
| Source address | 64 bytes | 512-bit data width |
| Destination address | 64 bytes | 512-bit data width |
| Transfer length | N/A | Any number of beats |

**Note:** STREAM requires aligned addresses. Unaligned transfers are not supported (see RAPIDS for alignment fixup).

---

## Transfer Size Calculation

```c
// DATA_WIDTH = 512 bits = 64 bytes
// Length field is in BEATS (not bytes)

// Transfer size = length * 64 bytes
// Example: length = 64 beats = 64 * 64 = 4096 bytes (4KB)

// Maximum single descriptor transfer:
// length = 2^32 - 1 beats = ~256 GB (practical limit is memory size)
```

---

## Status Checking

### Channel State Register (0x140 - 0x15F)

```c
// Read channel N state (7-bit one-hot)
uint32_t ch_state = regs[(0x140 + (channel * 4))/4];

#define CH_IDLE       0x01  // Waiting for descriptor
#define CH_FETCH_DESC 0x02  // Fetching descriptor
#define CH_XFER_DATA  0x04  // Transfer in progress
#define CH_COMPLETE   0x08  // Transfer complete
#define CH_NEXT_DESC  0x10  // Fetching next chained descriptor
#define CH_ERROR      0x20  // Error state

switch (ch_state) {
    case CH_IDLE:       printf("Channel idle\n"); break;
    case CH_FETCH_DESC: printf("Fetching descriptor\n"); break;
    case CH_XFER_DATA:  printf("Transfer in progress\n"); break;
    case CH_COMPLETE:   printf("Transfer complete\n"); break;
    case CH_NEXT_DESC:  printf("Chaining to next\n"); break;
    case CH_ERROR:      printf("Error!\n"); break;
}
```

---

## Common Issues

### Issue: Transfer Never Starts

**Check:**
1. Is channel enabled? (`CHANNEL_ENABLE` register)
2. Is global enable set? (`GLOBAL_CTRL` register)
3. Is descriptor address aligned to 32 bytes?
4. Is descriptor in accessible memory?

### Issue: Transfer Hangs

**Check:**
1. Are source/destination addresses aligned to 64 bytes?
2. Is memory accessible (not protected)?
3. Is timeout configured? (check `SCHED_TIMEOUT`)
4. Is the AXI interconnect responding?

### Issue: Data Corruption

**Check:**
1. Cache coherency - flush descriptor, invalidate destination
2. Descriptor format - verify bit layout matches hardware
3. Memory barriers - ensure writes complete before kick-off

---

## Related Documentation

- **[Initialization](01_initialization.md)** - Setup before transfers
- **[Chained Transfers](03_chained_transfers.md)** - Multi-descriptor chains
- **[Error Handling](05_error_handling.md)** - Error recovery

---

**Last Updated:** 2025-12-01
