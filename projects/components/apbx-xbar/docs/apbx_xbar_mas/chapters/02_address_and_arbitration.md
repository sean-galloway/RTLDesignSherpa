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

# Address Decode and Arbitration

**Component:** APB Crossbar (MxN Interconnect)
**Version:** 1.0
**Status:** Production Ready

---

## Overview

This document details the two core mechanisms of the APB Crossbar:
1. **Address Decode** - How incoming addresses map to specific slaves
2. **Arbitration** - How multiple masters share access to the same slave

---

## Address Decode

### Address Map Structure

The crossbar uses a fixed 64KB (0x10000 bytes) region per slave:

```
BASE_ADDR + 0x0000_0000 → 0x0000_FFFF : Slave 0 (64KB)
BASE_ADDR + 0x0001_0000 → 0x0001_FFFF : Slave 1 (64KB)
BASE_ADDR + 0x0002_0000 → 0x0002_FFFF : Slave 2 (64KB)
BASE_ADDR + 0x0003_0000 → 0x0003_FFFF : Slave 3 (64KB)
...
BASE_ADDR + 0x000F_0000 → 0x000F_FFFF : Slave 15 (64KB)
```

**Default BASE_ADDR:** 0x10000000

**Total Address Space:** (number of slaves) × 64KB

### Decode Algorithm

The crossbar extracts the slave index from the upper bits of the address offset:

```systemverilog
offset = PADDR - BASE_ADDR
slave_index = offset[16 +: $clog2(S)]   // ceil(log2(S)) bits above the 64KB window
```

### Out-of-Range Addresses

This applies to the variants that DECODE -- `1to4`, `2to4`,
`2to2_mixed`. In `1to1` and `2to1` there is a single slave, no address
decode, and `BASE_ADDR` is unused: every access is forwarded to that
slave whatever its address, and the slave's own response is returned.

For the decoding variants, an access outside
`[BASE_ADDR, BASE_ADDR + S x 64KB)` is a **decode miss**. The crossbar
accepts it and answers locally with **PSLVERR**;
no slave sees the transfer, and the arbiters are not involved. The
master's transaction completes normally (PREADY asserts) with the error
flagged, so a bad pointer surfaces as an APB error response rather than
a hang.

Earlier RTL left `cmd_ready` low on a miss, which wedged the master in
ACCESS with PREADY low and no error signature (APBX-002). Regression:
the decode-miss scenarios in `test_apbx_xbar_1to4.py`,
`test_apbx_xbar_2to4.py`, and `test_apbx_xbar_2to2_mixed.py`.

**Why bit 16 upward?**
- 64KB = 0x10000 = 2^16 bytes
- Lower 16 bits (offset[15:0]) are byte address within slave
- `ceil(log2(S))` bits starting at bit 16 select the slave: [17:16]
  for a 4-slave variant, [16] for 2 slaves. The shipped variants wire
  exactly those bits -- `m0_slave_sel` is 2 bits wide on 1to4/2to4,
  1 bit on 2to2_mixed, NOT a 4-bit index
- The generator supports up to 16 slaves; bits above the index field
  do not select a slave, they fail the range check and become a
  decode miss

### Address Decode Flow Diagram

The following diagram shows a concrete example of how address 0x10023456 routes to Slave 2:

### Figure 2.1: Address Decode Flow

![Address Decode Flow](../assets/png/address_decode_flow.png)

The figure shows step-by-step routing of address 0x10023456 to Slave 2.

### Decode Example Walkthrough

**Scenario:** Master accesses address 0x10023456 with BASE_ADDR = 0x10000000

**Step 1: Calculate Offset**
```
offset = PADDR - BASE_ADDR
       = 0x10023456 - 0x10000000
       = 0x00023456
```

**Step 2: Extract Slave Index**
```
slave_index = offset[17:16]        // S=4 -> 2 bits
            = 0x00023456 >> 16
            = 0x2
```

**Step 3: Parallel Decode**

The crossbar checks all slave ranges in parallel:
- Slave 0: 0x00000 - 0x0FFFF → NO MATCH
- Slave 1: 0x10000 - 0x1FFFF → NO MATCH
- **Slave 2: 0x20000 - 0x2FFFF → MATCH** ✓
- Slave 3: 0x30000 - 0x3FFFF → NO MATCH

**Step 4: Route to Arbiter**

Transaction request forwarded to Arbiter[2] (Slave 2's arbiter)

**Step 5: Forward to Slave**

After arbitration grant, transaction forwarded via apb4_master[2] to physical Slave 2

**Final Address Sent to Slave:** 0x10023456 (full address preserved)

### Multiple Address Maps

You can create multiple distinct address maps by using different BASE_ADDR values:

**Example: Two Crossbars**

```systemverilog
// Peripheral Bus: 0x1000_0000 - 0x1003_FFFF
apbx_xbar_1to4 #(
    .BASE_ADDR(32'h1000_0000)
) u_periph_xbar (...);
// Slaves at: 0x1000_0000, 0x1001_0000, 0x1002_0000, 0x1003_0000

// Memory-Mapped I/O: 0x8000_0000 - 0x8003_FFFF
apbx_xbar_1to4 #(
    .BASE_ADDR(32'h8000_0000)
) u_mmio_xbar (...);
// Slaves at: 0x8000_0000, 0x8001_0000, 0x8002_0000, 0x8003_0000
```

---

## Arbitration

### Per-Slave Round-Robin

Each slave has an **independent arbiter** that implements round-robin scheduling:

**Key Properties:**
- **Fair:** No master can starve another
- **Independent:** Each slave arbitrates separately
- **Predictable:** Priority rotates after each grant
- **Persistent:** Grant held from command through response

### Round-Robin Timing Diagram

The following timing diagram shows 2 masters (M0, M1) competing for access to Slave 0:

### Waveform 2.1: Round-Robin Arbitration Timing

![Round-Robin Arbitration Timing](../assets/wavedrom/arbitration_round_robin.png)

### Arbitration Example Walkthrough

**Scenario:** Master 0 and Master 1 both want to access Slave 0

**Initial State:**
- Priority: M0 (M0 has priority initially)
- Slave 0: IDLE

**Transaction 1: M0 Requests Slave 0**
```
Cycle 1: M0 asserts request (M0_PSEL, M0_PADDR=0x1000_0000)
Cycle 2: Arbiter[0] grants to M0 (only requester)
         M0_PENABLE asserted
         S0_PSEL asserted to Slave 0
Cycle 3: Slave 0 responds (S0_PREADY)
         Transaction completes
         Priority rotates: M1 now has priority
```

**Transaction 2: M0 and M1 Both Request Slave 0**
```
Cycle 4: M0 asserts request (M0_PADDR=0x1000_0010)
         M1 asserts request (M1_PADDR=0x1000_0000) -- CONFLICT!
Cycle 5: Arbiter[0] grants to M1 (has priority)
         M1_PENABLE asserted
         S0_PSEL asserted to Slave 0
         M0 blocked, waits
Cycle 6: Slave 0 responds (S0_PREADY)
         M1 transaction completes
         Priority rotates: M0 now has priority
```

**Transaction 3: M0 Request (After Rotation)**
```
Cycle 7: M0 still asserting request (was blocked)
Cycle 8: Arbiter[0] grants to M0 (now has priority)
         M0_PENABLE asserted
         S0_PSEL asserted to Slave 0
Cycle 9: Slave 0 responds (S0_PREADY)
         Transaction completes
         Priority rotates: M1 now has priority
```

**Result:** Fair access - each master gets served in turn when both request

### Multi-Slave Parallelism

**Key Feature:** Different slaves can be accessed simultaneously by different masters

**Example: Parallel Transactions**

```
Time T0:
- Master 0 accesses Slave 0 (UART) - GRANTED
- Master 1 accesses Slave 2 (Timer) - GRANTED
Both transactions proceed in parallel (no conflict)

Time T1:
- Master 0 accesses Slave 0 (UART) - GRANTED
- Master 1 accesses Slave 0 (UART) - BLOCKED (arbitration)
Master 1 waits for Master 0 to complete

Time T2:
- Master 0 completes, releases Slave 0
- Master 1 accesses Slave 0 (UART) - GRANTED
Priority rotated for Slave 0's arbiter
```

**Benefit:** Maximum throughput when masters access different slaves

### Grant Persistence

**Critical Property:** Once granted, a master holds the slave until response completes

**Why This Matters:**

```
WITHOUT Grant Persistence:
- Master 0 granted Slave 0
- Master 0 asserts PENABLE
- *Grant could change here* ← BREAKS PROTOCOL!
- Slave 0 responds to wrong master

WITH Grant Persistence:
- Master 0 granted Slave 0
- Master 0 asserts PENABLE
- Grant held until PREADY asserted ← SAFE
- Slave 0 responds to correct master
- Grant released for next transaction
```

**Implementation:** Grant signal registered and held from PSEL assertion through PREADY response

### Arbitration Latency

**Best Case (No Contention):**
- 1 cycle: the grant is REGISTERED (`grant <= w_next_grant;` in
  `arbiter_round_robin`), so request → grant is never same-cycle
- Fabric overhead is the dominant term, not APB's 2-cycle minimum:
  a full transfer measures 9 cycles (see "Transaction Latency" below)

**Worst Case (Maximum Contention):**
- Wait for the masters ahead in the round-robin to complete FULL
  transactions -- the grant is held until the response handshake
  (`WAIT_GNT_ACK(1)`), so each is ~9 cycles, not 1
- Example: 2 masters, worst case ≈ one full transaction of wait
- Example: 4 masters, worst case = 3 full transactions ~= 27 cycles

**Average Case (Random Access Pattern):**
- (M-1)/2 full transactions of average wait (~9 cycles each)
- Statistical fairness over time

---

## Integration Examples

### Example 1: CPU to 4 Peripherals (No Contention)

```systemverilog
apbx_xbar_1to4 #(
    .BASE_ADDR(32'h1000_0000)
) u_periph_xbar (
    // Single master (CPU)
    // .m0_apb_PSEL(cpu_apb_PSEL), .m0_apb_PENABLE(...), ...  (elided)

    // 4 slaves (UART, GPIO, Timer, SPI)
    .s0_apb_* (uart_*),   // 0x1000_0000
    .s1_apb_* (gpio_*),   // 0x1001_0000
    .s2_apb_* (timer_*),  // 0x1002_0000
    .s3_apb_* (spi_*)     // 0x1003_0000
);
```

**Behavior:**
- No arbitration needed (single master)
- Pure address decode functionality
- Zero arbitration overhead

### Example 2: CPU + DMA to 4 Peripherals (Potential Contention)

```systemverilog
apbx_xbar_2to4 #(
    .BASE_ADDR(32'h4000_0000)
) u_soc_xbar (
    // Two masters
    // .m0_apb_PSEL(cpu_apb_PSEL), .m0_apb_PENABLE(...), ...  (elided)
    // .m1_apb_PSEL(dma_apb_PSEL), ...                        (elided)

    // 4 slaves
    .s0_apb_* (mem_ctrl_*),  // 0x4000_0000
    .s1_apb_* (uart_*),      // 0x4001_0000
    .s2_apb_* (i2c_*),       // 0x4002_0000
    .s3_apb_* (adc_*)        // 0x4003_0000
);
```

**Behavior:**
- Each slave has independent arbiter
- CPU and DMA can access different slaves simultaneously
- If both access same slave, round-robin arbitration
- Fair access guaranteed

---

## Performance Characteristics

### Throughput

**Single Master:**
- Back-to-back transactions supported, but NOT overlapped: `apb4_slave`
  is a one-command-at-a-time FSM, so the next command is captured only
  after the previous transaction completes
- Measured sustained cadence: 1 transfer per 9 pclk cycles at an
  always-ready slave -- identical to single-transfer latency, because
  nothing overlaps (an earlier "zero bubble" claim described a pipeline
  this RTL does not have)

**Multiple Masters (Same Slave):**
- Round-robin introduces fair sharing
- Each master gets ~1/M of bandwidth
- Example: 2 masters = 50% bandwidth each

**Multiple Masters (Different Slaves):**
- Full parallelism
- Each master gets 100% of its target slave
- Total system bandwidth = (number of slaves) × slave_bandwidth

### Latency

**Components:**

1. **Address Decode:** 0 cycles (combinational, parallel)
2. **Arbitration Decision:** 1 cycle (grant is registered)
3. **Master APB phases:** 2 cycles (PSEL, then PENABLE)
4. **Boundary IP + skid buffers:** ~6 cycles -- `apb4_slave` capture,
   registered cmd skid, `apb4_master` IDLE→SETUP→ACCESS, registered rsp
   skid, `apb4_slave` BUSY→PREADY
5. **Slave Response:** Variable (adds to the above)

**Total Minimum Latency: 9 cycles** (8 of them ACCESS->PREADY) (uncontended, zero-wait slave --
measured on `apbx_xbar_1to1`). APB's 2-cycle minimum applies to a
directly-attached slave; it does not apply through this fabric, which
converts APB→cmd/rsp→APB across registered buffers in both directions.

**With Contention:** add one full transaction (~9 cycles) per master
ahead in the round-robin

---

## Design Notes

### Why 64KB Per Slave?

**Rationale:**
- Sufficient for most APB peripherals (typically 256B - 4KB register space)
- Simple decode logic (single shift operation)
- Allows up to 16 slaves with clean byte alignment
- Software-friendly (each peripheral has "round" base address)

**Alternatives:**
- Smaller regions (4KB, 16KB) → more slaves, more complex decode
- Larger regions (256KB, 1MB) → fewer slaves, wasted address space

### Why Round-Robin?

**Advantages:**
- Fair: Prevents starvation
- Simple: Minimal logic (counter + comparator)
- Predictable: Software can reason about worst-case latency
- No configuration: Works out-of-box

**Alternatives:**
- Fixed priority → Can starve low-priority masters
- Weighted fair queuing → More complex, requires configuration
- Lottery scheduling → Unpredictable, harder to verify

---

## Troubleshooting

### Issue: Wrong Slave Selected

**Check:**
1. BASE_ADDR parameter correct?
2. Address within expected range?
3. Calculated slave_index matches expectation?

**Debug:**
```systemverilog
offset = PADDR - BASE_ADDR
slave_index = offset >> 16
expected_slave = slave_index  // Should match actual PSEL
```

### Issue: Master Starved

**Check:**
1. Other masters continuously accessing same slave?
2. Round-robin priority rotating correctly? (grant is released at the
   RESPONSE handshake -- `grant_ack = grant && rsp_valid && rsp_ready`
   with `WAIT_GNT_ACK(1)` -- so a master that never completes a
   transaction holds its grant)
3. Is the starved master's address actually decoding in range? An
   out-of-range access completes locally with PSLVERR and never reaches
   an arbiter.

There is no timeout or monitoring knob to enable: `arbiter_round_robin`
has no timeout logic, parameter, or port. An earlier revision of this
checklist referenced one.

**Expected Behavior:**
- Each master should get grant within M transactions
- No master should wait indefinitely

### Issue: Back-to-Back Transactions Stalling

**Check:**
1. Grant persistence working?
2. Slave asserting PREADY correctly?
3. No unintended pipeline bubbles?

**Expected Behavior:**
- Consecutive transactions from same master should flow without gaps
- Only arbitration conflicts should introduce wait states

---

## Next Steps

- See [Architecture](01_architecture.md) for top-level design overview
- See [PRD.md](../../PRD.md) for complete specification
- See [CLAUDE.md](../../CLAUDE.md) for integration guidance
- See [README.md](../../README.md) for quick start guide

---

**Version:** 1.0
**Last Updated:** 2025-10-25
**Maintained By:** RTL Design Sherpa Project
