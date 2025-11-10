### APB PIT 8254 - Common Use Cases

#### Use Case 1: Simple Timeout Timer

**Application:** Generate an interrupt after a fixed delay

**Implementation:**

```c
/**
 * Configure PIT counter as simple timeout timer
 * @param counter_num Counter to use (0, 1, or 2)
 * @param timeout_us Timeout in microseconds
 * @param clock_freq_hz PIT clock frequency in Hz
 * @return 0 on success, -1 on error
 */
int pit_timeout_start(uint8_t counter_num, uint32_t timeout_us, uint32_t clock_freq_hz) {
    // Calculate count value from timeout
    // counts = (timeout_us * clock_freq_hz) / 1,000,000
    uint64_t counts = ((uint64_t)timeout_us * clock_freq_hz) / 1000000ULL;

    // Check if count fits in 16 bits
    if (counts > 65535) {
        printf("ERROR: Timeout too long (max %u us at %u Hz)\n",
               (uint32_t)((65535ULL * 1000000ULL) / clock_freq_hz), clock_freq_hz);
        return -1;
    }

    // Disable PIT during configuration
    write_register(PIT_CONFIG, 0x00);

    // Build control word: Counter N, Mode 0, binary, LSB+MSB
    uint32_t control_word = (counter_num << 6) |  // SC = counter number
                            (3 << 4) |            // RW = LSB+MSB
                            (0 << 1) |            // MODE = 0 (one-shot)
                            (0 << 0);             // BCD = 0 (binary)
    write_register(PIT_CONTROL, control_word);

    // Load count value
    uint32_t data_reg_addr = 0x010 + (counter_num * 4);
    write_register(data_reg_addr, (uint32_t)counts);

    // Enable PIT
    write_register(PIT_CONFIG, 0x01);

    printf("Timeout timer started: %u us (%llu counts) on Counter %u\n",
           timeout_us, counts, counter_num);

    return 0;
}

/**
 * Check if timeout has expired
 * @param counter_num Counter number (0, 1, or 2)
 * @return 1 if expired, 0 if still counting
 */
int pit_timeout_expired(uint8_t counter_num) {
    uint32_t status = read_register(PIT_STATUS);

    // Extract status byte for specified counter
    uint8_t counter_status = (status >> (counter_num * 8)) & 0xFF;

    // Check OUT bit (bit 7)
    return (counter_status >> 7) & 0x1;
}

/**
 * Usage example
 */
void example_timeout(void) {
    // Start 100ms timeout on Counter 0 (assuming 10 MHz PIT clock)
    pit_timeout_start(0, 100000, 10000000);

    // Poll until timeout expires
    printf("Waiting for timeout...\n");
    while (!pit_timeout_expired(0)) {
        // Do other work here
    }
    printf("Timeout expired!\n");

    // Disable PIT
    write_register(PIT_CONFIG, 0x00);
}
```

#### Use Case 2: RTOS System Tick

**Application:** Generate periodic interrupt for RTOS scheduler

**Implementation:**

```c
/**
 * Configure PIT for RTOS system tick
 * @param tick_rate_hz Desired tick rate (e.g., 1000 for 1ms ticks)
 * @param clock_freq_hz PIT clock frequency
 * @return 0 on success, -1 on error
 */
int pit_rtos_tick_init(uint32_t tick_rate_hz, uint32_t clock_freq_hz) {
    // Calculate counts per tick
    uint32_t counts = clock_freq_hz / tick_rate_hz;

    if (counts > 65535) {
        printf("ERROR: Tick rate too slow for 16-bit counter\n");
        return -1;
    }

    // Use Counter 0 for system tick
    write_register(PIT_CONFIG, 0x00);  // Disable

    // Configure Counter 0: Mode 0, binary, LSB+MSB
    write_register(PIT_CONTROL, 0x30);

    // Load count value
    write_register(COUNTER0_DATA, counts);

    // Enable PIT
    write_register(PIT_CONFIG, 0x01);

    printf("RTOS tick configured: %u Hz (%u counts per tick)\n",
           tick_rate_hz, counts);

    return 0;
}

/**
 * RTOS tick interrupt handler
 */
void pit_tick_isr(void) {
    // Clear interrupt by reading status
    uint32_t status = read_register(PIT_STATUS);

    // Reload counter for next tick (one-shot mode requires manual reload)
    // Note: In Mode 0, must reload after each terminal count
    uint32_t counts = read_register(COUNTER0_DATA) & 0xFFFF;
    write_register(COUNTER0_DATA, counts);

    // Call RTOS tick handler
    rtos_tick();
}

/**
 * Usage example with interrupt
 */
void example_rtos_tick(void) {
    // Initialize 1ms system tick (10 MHz clock)
    pit_rtos_tick_init(1000, 10000000);

    // Register interrupt handler
    register_interrupt_handler(TIMER0_IRQ, pit_tick_isr);

    // Enable timer interrupt
    enable_interrupt(TIMER0_IRQ);

    // RTOS runs, tick ISR called every 1ms
    while (1) {
        rtos_schedule();
    }
}
```

**Note on Mode 0 for Periodic Operation:**

Mode 0 is one-shot by design. For periodic operation, the interrupt handler must reload the counter after each terminal count. Future PIT implementations may add Mode 2 or Mode 3 for automatic periodic operation.

#### Use Case 3: Multiple Independent Timers

**Application:** Three different timeout values running concurrently

**Implementation:**

```c
/**
 * Multi-timer manager structure
 */
typedef struct {
    uint8_t counter_num;
    uint32_t timeout_us;
    uint32_t counts;
    bool active;
} pit_timer_t;

static pit_timer_t timers[3];
static uint32_t pit_clock_freq = 10000000;  // 10 MHz

/**
 * Initialize multi-timer system
 */
void pit_multi_timer_init(void) {
    write_register(PIT_CONFIG, 0x00);  // Disable during init

    for (int i = 0; i < 3; i++) {
        timers[i].counter_num = i;
        timers[i].active = false;

        // Configure each counter: Mode 0, binary, LSB+MSB
        uint32_t control_word = (i << 6) | (3 << 4) | (0 << 1) | (0 << 0);
        write_register(PIT_CONTROL, control_word);
    }

    write_register(PIT_CONFIG, 0x01);  // Enable
}

/**
 * Start a timer
 */
int pit_timer_start(uint8_t timer_id, uint32_t timeout_us) {
    if (timer_id >= 3) return -1;

    pit_timer_t *timer = &timers[timer_id];

    // Calculate counts
    uint64_t counts = ((uint64_t)timeout_us * pit_clock_freq) / 1000000ULL;
    if (counts > 65535) return -1;

    timer->timeout_us = timeout_us;
    timer->counts = (uint32_t)counts;
    timer->active = true;

    // Load count value
    uint32_t data_reg = 0x010 + (timer_id * 4);
    write_register(data_reg, timer->counts);

    printf("Timer %u started: %u us\n", timer_id, timeout_us);
    return 0;
}

/**
 * Check if timer expired
 */
bool pit_timer_expired(uint8_t timer_id) {
    if (timer_id >= 3 || !timers[timer_id].active) return false;

    uint32_t status = read_register(PIT_STATUS);
    uint8_t counter_status = (status >> (timer_id * 8)) & 0xFF;
    bool out = (counter_status >> 7) & 0x1;

    if (out) {
        timers[timer_id].active = false;
        printf("Timer %u expired\n", timer_id);
    }

    return out;
}

/**
 * Usage example
 */
void example_multi_timer(void) {
    pit_multi_timer_init();

    // Start three different timeouts
    pit_timer_start(0, 10000);   // 10 ms
    pit_timer_start(1, 50000);   // 50 ms
    pit_timer_start(2, 100000);  // 100 ms

    // Poll all timers
    while (1) {
        if (pit_timer_expired(0)) {
            printf("Task A: Timer 0 fired\n");
            // Handle timer 0 event
        }

        if (pit_timer_expired(1)) {
            printf("Task B: Timer 1 fired\n");
            // Handle timer 1 event
        }

        if (pit_timer_expired(2)) {
            printf("Task C: Timer 2 fired\n");
            // All done
            break;
        }
    }

    write_register(PIT_CONFIG, 0x00);  // Disable
}
```

#### Use Case 4: Performance Profiling

**Application:** Measure code execution time with microsecond precision

**Implementation:**

```c
/**
 * Profiler using PIT counter
 */
typedef struct {
    uint32_t start_count;
    uint32_t clock_freq;
} pit_profiler_t;

static pit_profiler_t profiler;

/**
 * Initialize profiler (uses Counter 2)
 */
void pit_profiler_init(uint32_t clock_freq_hz) {
    profiler.clock_freq = clock_freq_hz;

    write_register(PIT_CONFIG, 0x00);

    // Configure Counter 2: Mode 0, binary, LSB+MSB
    write_register(PIT_CONTROL, 0xB0);

    // Load maximum count (65535) for longest measurement
    write_register(COUNTER2_DATA, 65535);

    write_register(PIT_CONFIG, 0x01);

    printf("Profiler initialized (max measurement: %u us)\n",
           (65535 * 1000000U) / clock_freq_hz);
}

/**
 * Start profiling measurement
 */
void pit_profile_start(void) {
    // Read current counter value as start reference
    profiler.start_count = read_register(COUNTER2_DATA) & 0xFFFF;
}

/**
 * Stop profiling and return elapsed time in microseconds
 */
uint32_t pit_profile_stop(void) {
    // Read current counter value
    uint32_t end_count = read_register(COUNTER2_DATA) & 0xFFFF;

    // Calculate elapsed counts (counter counts down)
    uint32_t elapsed_counts;
    if (profiler.start_count >= end_count) {
        elapsed_counts = profiler.start_count - end_count;
    } else {
        // Counter wrapped through zero
        elapsed_counts = profiler.start_count + (65535 - end_count) + 1;
    }

    // Convert to microseconds
    uint32_t elapsed_us = (elapsed_counts * 1000000ULL) / profiler.clock_freq;

    return elapsed_us;
}

/**
 * Usage example
 */
void example_profiling(void) {
    pit_profiler_init(10000000);  // 10 MHz clock

    // Profile some code
    pit_profile_start();

    // Code to measure
    for (volatile int i = 0; i < 10000; i++) {
        // Busy loop
    }

    uint32_t elapsed = pit_profile_stop();
    printf("Code execution time: %u us\n", elapsed);

    // Profile another section
    pit_profile_start();
    complex_function();
    elapsed = pit_profile_stop();
    printf("Complex function: %u us\n", elapsed);

    write_register(PIT_CONFIG, 0x00);
}
```

#### Use Case 5: Watchdog Timer

**Application:** Detect system lockup

**Implementation:**

```c
/**
 * Watchdog timer using PIT Counter 1
 */
#define WATCHDOG_TIMEOUT_MS 1000  // 1 second timeout

void pit_watchdog_init(uint32_t clock_freq_hz) {
    // Calculate counts for timeout
    uint32_t counts = (WATCHDOG_TIMEOUT_MS * clock_freq_hz) / 1000;

    write_register(PIT_CONFIG, 0x00);

    // Configure Counter 1: Mode 0, binary, LSB+MSB
    write_register(PIT_CONTROL, 0x70);

    write_register(COUNTER1_DATA, counts);

    write_register(PIT_CONFIG, 0x01);

    printf("Watchdog initialized: %u ms timeout\n", WATCHDOG_TIMEOUT_MS);
}

/**
 * Pet the watchdog (reset timer)
 */
void pit_watchdog_pet(void) {
    // Reload counter to reset timeout
    uint32_t counts = (WATCHDOG_TIMEOUT_MS * 10000000U) / 1000;
    write_register(COUNTER1_DATA, counts);
}

/**
 * Check if watchdog expired
 */
bool pit_watchdog_expired(void) {
    uint32_t status = read_register(PIT_STATUS);
    uint8_t counter1_status = (status >> 8) & 0xFF;
    return (counter1_status >> 7) & 0x1;
}

/**
 * Usage example
 */
void example_watchdog(void) {
    pit_watchdog_init(10000000);

    while (1) {
        // Main application loop
        do_work();

        // Pet watchdog to prevent timeout
        pit_watchdog_pet();

        // If do_work() hangs, watchdog will expire
        if (pit_watchdog_expired()) {
            printf("WATCHDOG TIMEOUT! System locked up!\n");
            system_reset();
        }
    }
}
```

#### Best Practices Summary

**1. Always Disable PIT During Configuration**
```c
write_register(PIT_CONFIG, 0x00);  // Disable first
// Configure counters...
write_register(PIT_CONFIG, 0x01);  // Enable when done
```

**2. Verify Count Values Fit in 16 Bits**
```c
if (counts > 65535) {
    printf("ERROR: Count too large\n");
    return -1;
}
```

**3. Use Appropriate Counter for Application**
- Counter 0: System tick, main application timer
- Counter 1: Watchdog, secondary timeout
- Counter 2: Profiling, debugging measurements

**4. Handle Counter Wrap in Profiling**
```c
// Down-counter wraps through 0
if (start >= end) {
    elapsed = start - end;
} else {
    elapsed = start + (65535 - end) + 1;
}
```

**5. Clear Interrupts Properly**
```c
void pit_isr(void) {
    // Read status to acknowledge
    uint32_t status = read_register(PIT_STATUS);

    // Reload counter if needed (Mode 0)
    write_register(COUNTER0_DATA, reload_value);

    // Handle interrupt
    // ...
}
```

---

**Version:** 1.0
**Last Updated:** 2025-11-08
