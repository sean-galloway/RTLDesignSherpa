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

### APB PIT 8254 - Initialization and Programming Guide

#### Power-On Initialization Sequence

**Step 1: Verify Reset State**

After power-on or reset, verify the PIT is in expected reset state:

```c
// Expected reset values
assert(read_register(PIT_CONFIG) == 0x00000000);    // PIT disabled
assert(read_register(PIT_STATUS) == 0x00303030);    // All counters: NULL_COUNT=1, OUT=0
assert(read_register(COUNTER0_DATA) == 0x00000000); // No count loaded
assert(read_register(COUNTER1_DATA) == 0x00000000);
assert(read_register(COUNTER2_DATA) == 0x00000000);
```

**Step 2: Configure Global Settings**

The PIT must be disabled during initial configuration:

```c
// Ensure PIT is disabled before programming
write_register(PIT_CONFIG, 0x00);  // PIT_ENABLE=0
```

**Step 3: Program Counter Control Words**

Each counter must be configured with a control word before use:

```c
// Configure Counter 0: Mode 0, binary, LSB+MSB access
uint32_t control_word_0 = (0 << 6) |  // SC=00 (Counter 0)
                          (3 << 4) |  // RW=11 (LSB+MSB)
                          (0 << 1) |  // MODE=000 (Mode 0)
                          (0 << 0);   // BCD=0 (binary)
write_register(PIT_CONTROL, control_word_0);  // Write 0x30

// Configure Counter 1: Mode 0, binary, LSB+MSB access
uint32_t control_word_1 = (1 << 6) |  // SC=01 (Counter 1)
                          (3 << 4) |  // RW=11 (LSB+MSB)
                          (0 << 1) |  // MODE=000 (Mode 0)
                          (0 << 0);   // BCD=0 (binary)
write_register(PIT_CONTROL, control_word_1);  // Write 0x70

// Configure Counter 2: Mode 0, binary, LSB+MSB access
uint32_t control_word_2 = (2 << 6) |  // SC=10 (Counter 2)
                          (3 << 4) |  // RW=11 (LSB+MSB)
                          (0 << 1) |  // MODE=000 (Mode 0)
                          (0 << 0);   // BCD=0 (binary)
write_register(PIT_CONTROL, control_word_2);  // Write 0xB0
```

**Step 4: Load Initial Count Values**

After configuring control words, load count values:

```c
// Load Counter 0 with count of 1000
write_register(COUNTER0_DATA, 1000);

// Load Counter 1 with count of 2000
write_register(COUNTER1_DATA, 2000);

// Load Counter 2 with count of 5000
write_register(COUNTER2_DATA, 5000);
```

**Step 5: Verify Configuration**

Read back status to confirm configuration:

```c
uint32_t status = read_register(PIT_STATUS);

// Extract counter 0 status
uint8_t counter0_status = status & 0xFF;
assert((counter0_status & 0x40) == 0);  // NULL_COUNT should be 0 (count loaded)
assert((counter0_status & 0x30) == 0x30);  // RW_MODE should be 3 (LSB+MSB)
assert((counter0_status & 0x0E) == 0x00);  // MODE should be 0
assert((counter0_status & 0x01) == 0x00);  // BCD should be 0
```

**Step 6: Enable PIT and Start Counting**

```c
// Enable global PIT operation
write_register(PIT_CONFIG, 0x01);  // PIT_ENABLE=1

// Counters will now begin counting (assuming GATE inputs are high)
```

**Step 7: Monitor Operation**

```c
// Wait for counter 0 to reach terminal count
while (1) {
    uint32_t status = read_register(PIT_STATUS);
    uint8_t counter0_status = status & 0xFF;
    bool out_high = (counter0_status >> 7) & 0x1;

    if (out_high) {
        printf("Counter 0 reached terminal count!\n");
        break;
    }

    // Optional: read current counter value
    uint32_t current_count = read_register(COUNTER0_DATA) & 0xFFFF;
    printf("Counter 0 current value: %u\n", current_count);
}
```

#### Complete Initialization Function

```c
/**
 * Initialize PIT with three counters
 * @param counter0_count Initial count for counter 0
 * @param counter1_count Initial count for counter 1
 * @param counter2_count Initial count for counter 2
 * @return 0 on success, -1 on error
 */
int pit_initialize(uint16_t counter0_count, uint16_t counter1_count, uint16_t counter2_count) {
    // Step 1: Disable PIT during configuration
    write_register(PIT_CONFIG, 0x00);

    // Step 2: Configure counter 0 control word
    // Mode 0, binary, LSB+MSB access
    write_register(PIT_CONTROL, 0x30);

    // Step 3: Load counter 0 count value
    write_register(COUNTER0_DATA, counter0_count);

    // Step 4: Configure counter 1 control word
    write_register(PIT_CONTROL, 0x70);

    // Step 5: Load counter 1 count value
    write_register(COUNTER1_DATA, counter1_count);

    // Step 6: Configure counter 2 control word
    write_register(PIT_CONTROL, 0xB0);

    // Step 7: Load counter 2 count value
    write_register(COUNTER2_DATA, counter2_count);

    // Step 8: Verify configuration
    uint32_t status = read_register(PIT_STATUS);

    // Check all counters have counts loaded (NULL_COUNT=0)
    if ((status & 0x00404040) != 0) {
        printf("ERROR: Counter configuration failed (NULL_COUNT bits set)\n");
        return -1;
    }

    // Step 9: Enable PIT
    write_register(PIT_CONFIG, 0x01);

    printf("PIT initialized successfully\n");
    printf("  Counter 0: %u counts\n", counter0_count);
    printf("  Counter 1: %u counts\n", counter1_count);
    printf("  Counter 2: %u counts\n", counter2_count);

    return 0;
}
```

#### Usage Example

```c
int main(void) {
    // Initialize PIT with different count values
    if (pit_initialize(1000, 5000, 10000) != 0) {
        printf("PIT initialization failed!\n");
        return -1;
    }

    // Monitor counter 0 terminal count
    printf("Waiting for Counter 0 to reach terminal count...\n");

    while (1) {
        uint32_t status = read_register(PIT_STATUS);
        if (status & 0x80) {  // Counter 0 OUT bit
            printf("Counter 0 reached terminal count!\n");
            break;
        }

        // Print current count every 100 iterations
        static int count = 0;
        if (++count >= 100) {
            uint32_t current = read_register(COUNTER0_DATA) & 0xFFFF;
            printf("Counter 0: %u\n", current);
            count = 0;
        }
    }

    // Disable PIT after use
    write_register(PIT_CONFIG, 0x00);

    return 0;
}
```

#### Runtime Configuration Changes

**Changing Count Value During Operation:**

```c
// To change counter 0 count value while running:

// 1. Disable PIT (stops all counters)
write_register(PIT_CONFIG, 0x00);

// 2. Write new count value
write_register(COUNTER0_DATA, new_count);

// 3. Re-enable PIT (counter restarts with new value)
write_register(PIT_CONFIG, 0x01);
```

**Alternative: Write While Enabled (Immediate Restart)**

```c
// Writing counter data while enabled causes immediate reload and restart
// No need to disable PIT first (but counter will restart from new value)

write_register(COUNTER0_DATA, new_count);  // Counter reloads and restarts
```

#### Common Initialization Errors

**Error 1: Enabling PIT Before Programming**

```c
// ❌ WRONG: Enable before configuration
write_register(PIT_CONFIG, 0x01);  // Enable too early!
write_register(PIT_CONTROL, 0x30);
write_register(COUNTER0_DATA, 1000);

// ✅ CORRECT: Configure first, then enable
write_register(PIT_CONFIG, 0x00);  // Disable during config
write_register(PIT_CONTROL, 0x30);
write_register(COUNTER0_DATA, 1000);
write_register(PIT_CONFIG, 0x01);  // Enable after config
```

**Error 2: Not Waiting for Count Load**

```c
// ❌ WRONG: Enable immediately after write
write_register(COUNTER0_DATA, 1000);
write_register(PIT_CONFIG, 0x01);  // May enable before count fully loaded

// ✅ CORRECT: Verify count loaded (or add small delay)
write_register(COUNTER0_DATA, 1000);
// Optional: verify NULL_COUNT cleared
uint32_t status = read_register(PIT_STATUS);
assert((status & 0x40) == 0);  // Counter 0 NULL_COUNT should be 0
write_register(PIT_CONFIG, 0x01);
```

**Error 3: Wrong Control Word Format**

```c
// ❌ WRONG: Incorrect bit positions
uint32_t cw = (0 << 0) |  // Counter select in wrong position!
              (3 << 6) |  // RW in wrong position!
              (0 << 4);   // Mode in wrong position!

// ✅ CORRECT: Proper bit positions per Intel 8254 spec
uint32_t cw = (0 << 6) |  // SC[7:6] = Counter select
              (3 << 4) |  // RW[5:4] = Read/Write mode
              (0 << 1) |  // M[3:1] = Mode
              (0 << 0);   // BCD[0] = Counting mode
```

#### Debugging Initialization Issues

**Check 1: Verify Register Access**

```c
// Test read/write capability
write_register(PIT_CONFIG, 0x02);  // Write non-zero value
uint32_t readback = read_register(PIT_CONFIG);
if (readback != 0x02) {
    printf("ERROR: Register access failed! Read 0x%08X, expected 0x02\n", readback);
}
```

**Check 2: Verify Control Word Decode**

```c
// After writing control word, read status to verify decode
write_register(PIT_CONTROL, 0x30);  // Counter 0, RW=11, Mode 0
uint32_t status = read_register(PIT_STATUS);
uint8_t counter0_status = status & 0xFF;

printf("Counter 0 Status: 0x%02X\n", counter0_status);
printf("  RW_MODE: %u (expect 3)\n", (counter0_status >> 4) & 0x3);
printf("  MODE: %u (expect 0)\n", (counter0_status >> 1) & 0x7);
printf("  BCD: %u (expect 0)\n", counter0_status & 0x1);
```

**Check 3: Verify Count Load**

```c
// After writing count, read back to verify
write_register(COUNTER0_DATA, 1234);
uint32_t readback = read_register(COUNTER0_DATA) & 0xFFFF;
if (readback != 1234) {
    printf("ERROR: Count value mismatch! Read %u, expected 1234\n", readback);
}
```

---

**Version:** 1.0
**Last Updated:** 2025-11-08
