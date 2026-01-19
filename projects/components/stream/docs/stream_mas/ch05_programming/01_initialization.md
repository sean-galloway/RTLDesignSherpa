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

# Initialization and Configuration

**Chapter:** 05.01
**Version:** 1.0
**Last Updated:** 2025-12-01

---

## Overview

This guide covers the initialization sequence for the STREAM DMA engine, including power-on setup, register configuration, and channel preparation.

---

## Power-On Initialization Sequence

### Step 1: Reset Handling

```c
// Wait for reset deassertion (hardware controlled)
// All registers initialize to safe defaults

// Reset sequence (external):
// 1. Assert aresetn = 0 for minimum 10 clock cycles
// 2. Deassert aresetn = 1 synchronous to aclk rising edge
// 3. Wait 5 cycles for internal stabilization
```

### Step 2: Read VERSION Register

```c
#define STREAM_BASE         0x00000000  // Platform-specific
#define REG_GLOBAL_CTRL     0x100
#define REG_VERSION         0x108
#define REG_CHANNEL_ENABLE  0x120

// Verify STREAM is present and correct version
uint32_t version = read32(STREAM_BASE + REG_VERSION);
uint8_t major = (version >> 24) & 0xFF;
uint8_t minor = (version >> 16) & 0xFF;
printf("STREAM Version: %d.%d\n", major, minor);
```

### Step 3: Global Enable

```c
// Enable STREAM globally
// GLOBAL_CTRL[0] = global_en
write32(STREAM_BASE + REG_GLOBAL_CTRL, 0x00000001);
```

### Step 4: Channel Configuration

```c
// Enable all 8 channels (or subset as needed)
write32(STREAM_BASE + REG_CHANNEL_ENABLE, 0x000000FF);

// For single-channel operation:
// write32(STREAM_BASE + REG_CHANNEL_ENABLE, 0x00000001);  // Channel 0 only
```

### Step 5: Scheduler Configuration

```c
#define REG_SCHED_CTRL      0x200
#define REG_SCHED_TIMEOUT   0x204

// Enable scheduler with timeout and error detection
// Bits: [0]=enable, [1]=timeout_en, [2]=err_en
write32(STREAM_BASE + REG_SCHED_CTRL, 0x00000007);

// Set timeout threshold (adjust for memory latency)
// Example: 10000 cycles for DDR4 at 200MHz
write32(STREAM_BASE + REG_SCHED_TIMEOUT, 10000);
```

### Step 6: Descriptor Engine Configuration

```c
#define REG_DESCENG_CTRL    0x220

// Enable descriptor engine with prefetch
// Bits: [0]=enable, [1]=prefetch, [7:4]=fifo_thresh
write32(STREAM_BASE + REG_DESCENG_CTRL, 0x00000083);  // enable + prefetch + thresh=8
```

### Step 7: AXI Transfer Configuration

```c
#define REG_AXI_XFER_CONFIG 0x2A0

// Configure burst sizes (16 beats read, 16 beats write)
// [7:0]=rd_beats, [15:8]=wr_beats
write32(STREAM_BASE + REG_AXI_XFER_CONFIG, 0x00000F0F);  // 16 beats each
```

### Step 8: Monitor Configuration (Optional)

```c
#define REG_DAXMON_ENABLE   0x240
#define REG_RDMON_ENABLE    0x260
#define REG_WRMON_ENABLE    0x280

// Enable monitors with error detection only (minimal overhead)
// Bits: [0]=mon_en, [1]=err_en, [3]=timeout_en
write32(STREAM_BASE + REG_DAXMON_ENABLE, 0x0000000B);  // Descriptor monitor
write32(STREAM_BASE + REG_RDMON_ENABLE,  0x0000000B);  // Read monitor
write32(STREAM_BASE + REG_WRMON_ENABLE,  0x0000000B);  // Write monitor
```

---

## Complete Initialization Example

```c
/**
 * Initialize STREAM DMA engine
 * @param base_addr Base address of STREAM registers
 * @return 0 on success, -1 on error
 */
int stream_init(uintptr_t base_addr) {
    volatile uint32_t *regs = (volatile uint32_t *)base_addr;

    // 1. Verify STREAM is present
    uint32_t version = regs[0x108/4];
    if ((version & 0xFFFF0000) == 0) {
        return -1;  // Invalid version, STREAM not present
    }

    // 2. Global enable
    regs[0x100/4] = 0x00000001;

    // 3. Enable all channels
    regs[0x120/4] = 0x000000FF;

    // 4. Scheduler configuration
    regs[0x200/4] = 0x00000007;  // enable + timeout + error detection
    regs[0x204/4] = 10000;       // timeout cycles

    // 5. Descriptor engine
    regs[0x220/4] = 0x00000083;  // enable + prefetch + thresh=8

    // 6. AXI transfer config
    regs[0x2A0/4] = 0x00001010;  // 16 beats read/write

    // 7. Enable monitors (errors only)
    regs[0x240/4] = 0x0000000B;  // DAXMON
    regs[0x260/4] = 0x0000000B;  // RDMON
    regs[0x280/4] = 0x0000000B;  // WRMON

    return 0;
}
```

---

## Configuration Presets

### Minimal (Low Power/Area)

```c
void stream_init_minimal(uintptr_t base) {
    volatile uint32_t *r = (volatile uint32_t *)base;
    r[0x100/4] = 0x00000001;  // Global enable
    r[0x120/4] = 0x00000001;  // Channel 0 only
    r[0x200/4] = 0x00000003;  // Scheduler: enable + timeout
    r[0x204/4] = 500;         // Short timeout (SRAM)
    r[0x220/4] = 0x00000041;  // DescEng: enable + thresh=4
    r[0x2A0/4] = 0x00000808;  // 8-beat bursts
    // Monitors disabled (default)
}
```

### High Performance

```c
void stream_init_high_perf(uintptr_t base) {
    volatile uint32_t *r = (volatile uint32_t *)base;
    r[0x100/4] = 0x00000001;  // Global enable
    r[0x120/4] = 0x000000FF;  // All 8 channels
    r[0x200/4] = 0x00000007;  // Scheduler: full enable
    r[0x204/4] = 20000;       // Long timeout
    r[0x220/4] = 0x000000F3;  // DescEng: enable + prefetch + thresh=15
    r[0x2A0/4] = 0x00004040;  // 64-beat bursts
    r[0x2B0/4] = 0x00000003;  // Perf profiler enabled
}
```

---

## Verification After Initialization

```c
int stream_verify_init(uintptr_t base) {
    volatile uint32_t *r = (volatile uint32_t *)base;

    // Check global status
    uint32_t status = r[0x104/4];  // GLOBAL_STATUS
    if (status & 0x80000000) {
        printf("ERROR: STREAM in error state\n");
        return -1;
    }

    // Check all enabled channels are idle
    uint32_t ch_idle = r[0x128/4];  // CHANNEL_IDLE
    uint32_t ch_enable = r[0x120/4];
    if ((ch_idle & ch_enable) != ch_enable) {
        printf("WARNING: Not all channels idle\n");
        return -1;
    }

    return 0;
}
```

---

## Related Documentation

- **[Register Map](../ch04_registers/register_map.md)** - Complete register definitions
- **[Single Transfer](02_single_transfer.md)** - Basic transfer operation
- **[Configuration Reference](../ch06_configuration/config_reference.md)** - All configuration options

---

**Last Updated:** 2025-12-01
