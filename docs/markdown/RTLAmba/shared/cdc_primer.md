<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# CDC Primer: Clock Domain Crossing Techniques

This document categorizes the clock domain crossing approaches available in RTL Design Sherpa and provides guidance on when to use each one. All modules listed here are production-ready with formal verification.

---

## The Three Vector CDC Categories

When you need to move multi-bit data across clock domains, there are three fundamental approaches. They differ in how they guarantee that the destination samples stable data.

| Category | Stability Guarantee | Throughput | Complexity | Use When |
|----------|-------------------|------------|------------|----------|
| **Open-Loop** | Source holds data stable | Low (~1 transfer per 6 dst clocks) | Minimal | Config registers, infrequent updates |
| **Closed-Loop Handshake** | Explicit req/ack acknowledgment | Medium (~1 per 5-8 dst clocks) | Moderate | Control signals, command/response |
| **Async FIFO** | Gray-coded pointer synchronization | High (1 per dst clock sustained) | Higher | Streaming data, DMA, packet transfer |

---

## Category 1: Open-Loop CDC

**Principle:** The source asserts a single-cycle valid pulse and holds data stable. A synchronized copy of the valid pulse propagates to the destination domain, which latches the data when the pulse arrives. There is no acknowledge path -- the source must guarantee the hold time.

**When it works:** The source naturally holds data for multiple destination clock periods. This is common for:
- Fast source to slow destination (the fast domain's data persists for many slow clocks)
- Configuration register writes (software writes once, hardware reads later)
- Status flags that change infrequently

**When it fails:** If the source can change data before the destination has sampled it. Without an acknowledge, there is no backpressure.

### Module: `cdc_open_loop`

```systemverilog
cdc_open_loop #(
    .DATA_WIDTH  (32),
    .SYNC_STAGES (3)
) u_cfg_cdc (
    .clk_src   (cpu_clk),
    .rst_src_n (cpu_rst_n),
    .src_valid (cfg_write_pulse),   // Single-cycle pulse
    .src_data  (cfg_write_data),    // Must be stable for 4+ dst clocks

    .clk_dst   (periph_clk),
    .rst_dst_n (periph_rst_n),
    .dst_valid (cfg_update_pulse),  // Single-cycle in dst domain
    .dst_data  (cfg_update_data)    // Latched, stable until next update
);
```

**Internals:** Uses [sync_pulse](../../RTLCommon/sync_pulse.md) for the valid crossing and a simple holding register for data.

**Minimum spacing:** Source valid pulses must be separated by at least `SYNC_STAGES + 1` destination clock cycles. Violating this loses transfers silently.

**Documentation:** [cdc_open_loop.md](cdc_open_loop.md)

### Supporting Primitives

| Module | Purpose | Doc |
|--------|---------|-----|
| [sync_pulse](../../RTLCommon/sync_pulse.md) | Single-cycle pulse crossing (toggle + edge detect) | rtl/common/ |
| [cdc_synchronizer](cdc_synchronizer.md) | Multi-flop synchronizer for quasi-static signals | rtl/amba/shared/ |
| [glitch_free_n_dff_arn](../../RTLCommon/glitch_free_n_dff_arn.md) | N-stage synchronizer primitive with ASYNC_REG | rtl/common/ |
| [reset_sync](../../RTLCommon/reset_sync.md) | Reset synchronizer (async assert, sync deassert) | rtl/common/ |

---

## Category 2: Closed-Loop Handshake CDC

**Principle:** The source asserts a request and holds data stable. The destination synchronizes the request, samples the data, and sends back an acknowledge. The source waits for the acknowledge before releasing the data or starting a new transfer. This explicit round-trip guarantees data stability regardless of clock frequency ratios.

Two variants exist, differing in how the request/acknowledge signals encode "new transfer":

### 2-Phase (Toggle / NRZ)

Each new transfer is signaled by a **transition** (toggle) of the request bit. The destination detects the edge and toggles its acknowledge bit in response. Two synchronizer crossings per transfer (req toggle + ack toggle).

```
Source:  data stable, toggle req ----[sync]----> Destination sees edge, latches data
                                                  toggle ack ----[sync]----> Source sees edge, done
```

**Advantage:** Faster -- half the control-path round trip of 4-phase.
**Disadvantage:** Edge detection is slightly trickier to reason about.

### 4-Phase (Level / RZ)

Each transfer uses full rise-and-fall cycles: req rises, ack rises, req falls, ack falls. Four synchronizer crossings per transfer.

```
Source:  data stable, req=1 ----[sync]----> Destination sees req=1, latches data
                                             ack=1 ----[sync]----> Source sees ack=1, req=0
                                             ack=0 (after req=0 propagates) ----> Ready for next
```

**Advantage:** Simpler level-based logic, easier to verify.
**Disadvantage:** Slower -- four crossings instead of two.

### Modules

| Module | Variant | Latency | Doc |
|--------|---------|---------|-----|
| [cdc_2_phase_handshake](cdc_2_phase_handshake.md) | Toggle (NRZ) | ~5-6 dst clocks | rtl/amba/shared/ |
| [cdc_4_phase_handshake](cdc_4_phase_handshake.md) | Level (RZ) | ~7-8 dst clocks | rtl/amba/shared/ |

Both modules have identical port interfaces and are drop-in interchangeable:

```systemverilog
// Change only the module name to switch variants
cdc_2_phase_handshake #(   // or cdc_4_phase_handshake
    .DATA_WIDTH     (64),
    .SYNC_STAGES    (3),
    .TIMEOUT_CYCLES (1000)
) u_pkt_cdc (
    .clk_src     (mon_clk),
    .rst_src_n   (mon_rst_n),
    .src_valid   (pkt_valid),
    .src_ready   (pkt_ready),    // Backpressure to source
    .src_data    (pkt_data),
    .src_timeout (pkt_timeout),  // Stall detection

    .clk_dst     (sys_clk),
    .rst_dst_n   (sys_rst_n),
    .dst_valid   (rx_valid),
    .dst_ready   (rx_ready),
    .dst_data    (rx_data)
);
```

### Protocol-Level CDC Using Handshakes

The handshake modules are building blocks for protocol-level CDC:

| Module | Protocol | Handshake Used | Doc |
|--------|----------|---------------|-----|
| [apb_slave_cdc](../apb/apb_slave_cdc.md) | APB4 | Selectable 2-phase or 4-phase | rtl/amba/apb/ |
| [apb5_slave_cdc](../apb5/apb5_slave_cdc.md) | APB5 | Selectable 2-phase or 4-phase | rtl/amba/apb5/ |

---

## Category 3: Gray-Coded Pointers / Async FIFO

**Principle:** Instead of synchronizing data directly, synchronize the read and write **pointers** of a dual-port memory. The pointers are Gray-coded so that only one bit changes per increment. This means any sample during a transition yields either the old or new pointer value -- never a corrupted intermediate. The memory itself is dual-ported (one port per clock domain) and requires no synchronization.

This is the dominant technique for streaming data across clock domains. If you are moving continuous data rather than occasional transfers, this is what you reach for.

### How It Works

```
Write Domain:                              Read Domain:
  wr_ptr (binary) ---> bin2gray --->        gray2bin ---> Compare with rd_ptr
                        [sync N stages]                   for empty detection
                        
  gray2bin <--- [sync N stages] <--- bin2gray <--- rd_ptr (binary)
  Compare with wr_ptr for full detection
```

1. Each domain maintains its own pointer in binary (for memory addressing)
2. Each pointer is converted to Gray code (for safe CDC crossing)
3. The Gray-coded pointer is synchronized into the other domain
4. Full/empty flags are derived by comparing the local pointer with the synchronized remote pointer
5. The dual-port memory is addressed by the binary pointers directly (no CDC needed for data)

### Standard Gray Code vs Johnson Counter

The repository provides two async FIFO implementations that differ in how they encode pointers:

**Standard Gray Code** (`fifo_async`): Uses `bin2gray` / `gray2bin` converters with standard binary-reflected Gray code. Depth must be a power of 2 (because standard Gray codes only have single-bit transitions for power-of-2 counts).

**Johnson Counter** (`fifo_async_div2`): Uses a Johnson counter sequence, which is a subset of Gray code that supports even (non-power-of-2) depths. A Johnson counter of N bits cycles through 2N states, each differing by one bit. The `grayj2bin` converter decodes the Johnson sequence back to binary for pointer comparison.

| FIFO | Pointer Encoding | Depth Constraint | Best For |
|------|-----------------|------------------|----------|
| [fifo_async](../../RTLCommon/fifo_async.md) | Standard Gray code | Power of 2 only | Most use cases |
| [fifo_async_div2](../../RTLCommon/fifo_async_div2.md) | Johnson counter | Any even number | Odd-sized buffers, area optimization |

### Modules

| Module | Description | Depth | Doc |
|--------|-------------|-------|-----|
| [fifo_async](../../RTLCommon/fifo_async.md) | Basic async FIFO, Gray-coded pointers | Power of 2 | rtl/common/ |
| [fifo_async_div2](../../RTLCommon/fifo_async_div2.md) | Async FIFO, Johnson counter pointers | Any even | rtl/common/ |
| [gaxi_fifo_async](../gaxi/gaxi_fifo_async.md) | GAXI-interface async FIFO | Configurable | rtl/amba/gaxi/ |
| [gaxi_skid_buffer_async](../gaxi/gaxi_skid_buffer_async.md) | Pipelined async FIFO (skid + async) | Configurable | rtl/amba/gaxi/ |

### Usage Example

```systemverilog
fifo_async #(
    .DATA_WIDTH    (64),
    .DEPTH         (16),       // Must be power of 2
    .N_FLOP_CROSS  (3),        // Synchronizer stages
    .ALMOST_WR_MARGIN (2),     // Almost-full threshold
    .ALMOST_RD_MARGIN (2)      // Almost-empty threshold
) u_stream_cdc (
    // Write domain
    .wr_clk     (src_clk),
    .wr_rst_n   (src_rst_n),
    .wr_en      (src_valid && !wr_full),
    .wr_data    (src_data),
    .wr_full    (wr_full),
    .wr_almost_full (wr_almost_full),

    // Read domain
    .rd_clk     (dst_clk),
    .rd_rst_n   (dst_rst_n),
    .rd_en      (dst_ready && !rd_empty),
    .rd_data    (dst_data),
    .rd_empty   (rd_empty),
    .rd_almost_empty (rd_almost_empty)
);
```

### Supporting Primitives

| Module | Purpose | Doc |
|--------|---------|-----|
| [bin2gray](../../RTLCommon/bin2gray.md) | Binary to Gray code converter | rtl/common/ |
| [gray2bin](../../RTLCommon/gray2bin.md) | Gray code to binary converter | rtl/common/ |
| [grayj2bin](../../RTLCommon/grayj2bin.md) | Johnson counter to binary converter | rtl/common/ |
| [counter_bingray](../../RTLCommon/counter_bingray.md) | Dual binary+Gray output counter | rtl/common/ |
| [counter_johnson](../../RTLCommon/counter_johnson.md) | Johnson counter for div2 FIFOs | rtl/common/ |
| [glitch_free_n_dff_arn](../../RTLCommon/glitch_free_n_dff_arn.md) | N-stage synchronizer for pointer crossing | rtl/common/ |

---

## Decision Guide: Which CDC Technique?

```
Need to cross clock domains with multi-bit data?
|
+-- Is data streaming / continuous?
|   |
|   +-- YES --> Async FIFO (fifo_async or gaxi_fifo_async)
|   |           Sustained 1-per-clock throughput, buffered
|   |
|   +-- NO, occasional transfers -->
|       |
|       +-- Does the source need backpressure (flow control)?
|           |
|           +-- YES --> Closed-loop handshake
|           |           (cdc_2_phase_handshake or cdc_4_phase_handshake)
|           |
|           +-- NO, source can guarantee hold time -->
|               |
|               +-- Open-loop (cdc_open_loop)
|                   Simplest, lowest area, no ack needed
|
Single-bit signal?
|
+-- Level / quasi-static --> cdc_synchronizer or glitch_free_n_dff_arn
+-- Single-cycle pulse   --> sync_pulse
+-- Reset signal          --> reset_sync
```

### Quick Reference

| Scenario | Module | Why |
|----------|--------|-----|
| Config register update (CPU -> peripheral) | `cdc_open_loop` | Infrequent, no backpressure needed |
| Interrupt signal (1 bit, pulse) | `sync_pulse` | Single-cycle event |
| Status register read (slow -> fast) | `cdc_synchronizer` | Quasi-static level |
| APB slave in different clock domain | `apb_slave_cdc` | Full protocol CDC |
| Monitor packet crossing | `cdc_2_phase_handshake` | Occasional, needs flow control |
| DMA data stream | `fifo_async` | High throughput, continuous |
| AXI channel crossing | `gaxi_skid_buffer_async` | Pipelined, GAXI protocol |
| Reset distribution | `reset_sync` | Async assert, sync deassert |

---

## Common Mistakes

**1. Using a multi-flop synchronizer for multi-bit buses that change simultaneously**

Multi-flop synchronizers (2FF/3FF) are safe for single-bit signals or Gray-coded values. If multiple bits can change at once, different bits may be sampled from different time points, producing a value that never existed.

Fix: Use a handshake or async FIFO.

**2. Using set_false_path on CDC data buses**

`set_false_path` tells the tool to ignore timing entirely. For handshake and open-loop CDC, the data bus must arrive within a bounded window (roughly SYNC_STAGES destination clocks). Use `set_max_delay -datapath_only` instead.

**3. Assuming async FIFO depth = 2 is enough**

A depth-2 async FIFO has only 1 usable entry (full when wr_ptr != rd_ptr by 1). The synchronized pointers lag by SYNC_STAGES cycles, so the effective throughput drops. Use depth >= 4 for practical designs.

**4. Sending a new open-loop transfer before the previous one is sampled**

Without an acknowledge, the source has no way to know the destination has latched the data. If the source writes again too soon, the first transfer is silently lost. Minimum spacing: SYNC_STAGES + 1 destination clocks.

---

## References

- Clifford E. Cummings, "Clock Domain Crossing (CDC) Design and Verification Techniques Using SystemVerilog" (SNUG 2008)
- Clifford E. Cummings, "Simulation and Synthesis Techniques for Asynchronous FIFO Design" (SNUG 2002)
- IEEE 1800-2017 SystemVerilog LRM, Section on synchronizer modeling

---

**Last Updated:** 2026-04-21

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
