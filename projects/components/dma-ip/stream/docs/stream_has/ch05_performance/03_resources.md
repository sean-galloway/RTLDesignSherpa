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

# Resource Estimates

## Measured Core Area

Out-of-context Vivado synthesis of `stream_core` at 256-bit data, with
monitors off and a 100 MHz clock (2026-10-17):

| Build | LUTs | Flops | Worst slack |
|-------|-----:|------:|------------:|
| 8 channels, one descriptor engine per channel (`SHARED_ENGINES = 0`) | 25.8k | 14.9k | +3.24 ns |
| 8 channels, shared descriptor engine (default) | 20.7k | 11.7k | +2.50 ns |
| 16 channels, shared descriptor engine | 36.8k | 19.4k | +1.79 ns |

: Measured stream_core Area and Timing

Sharing the descriptor engine removes about a fifth of the 8-channel core's
LUTs and flops: the per-channel AR issue logic, the address-range comparators,
the 256-bit holding registers and the MonBus reporters. The 16-channel build
costs about 1.8 times the 8-channel build and still closes at 100 MHz.

## Measured Board Build (Genesys 2)

Source: two placed-and-routed Genesys 2 builds made on 2026-10-17 from the same RTL, differing only in `SHARED_ENGINES`. The bitstreams are `stream_perf_genesys2_8ch_pce.bit` (`SHARED_ENGINES = 0`) and `stream_perf_genesys2_8ch.bit` (`SHARED_ENGINES = 1`). Both builds use 8 channels, 128-bit data, 256 entries per channel, 8 outstanding reads and writes, AXI monitors off and `GEN_MON = 0`, at 100 MHz on the `xc7k325tffg900-2` with Vivado 2025.1. The STREAM rows are the `u_stream` instance of the hierarchical post-route report; the whole-design rows include the characterization harness.

| Resource | Per-channel engines | Shared engine | Change |
|----------|---------------------|---------------|--------|
| Whole design, Slice LUTs | 63,642 | 62,111 | -1,531 (-2.4 %) |
| Whole design, Slice registers | 56,536 | 54,111 | -2,425 (-4.3 %) |
| STREAM (`u_stream`), LUTs | 30,781 | 29,247 | -1,534 (-5.0 %) |
| STREAM (`u_stream`), flip-flops | 23,079 | 20,654 | -2,425 (-10.5 %) |
| Descriptor engines, LUTs / flip-flops | 4,974 / 4,120 (8 engines) | 3,825 / 1,725 (1 engine) | -1,149 / -2,395 |
| Block RAM tiles | 26 | 26 | 0 |
| DSP | 64 | 64 | 0 |
| Worst setup slack | +0.612 ns | +0.377 ns | |

: Post-Route Utilization, SHARED_ENGINES 0 and 1

The board saving is smaller than the out-of-context figure above for two reasons. The board build has `GEN_MON = 0`, so the per-channel MonBus reporters that sharing removes are not built in either case. And the shared engine keeps a descriptor FIFO and an extended-descriptor FIFO per channel; together they are 1,840 LUTs of distributed RAM, almost half the engine. Block RAM and DSP are unchanged because the descriptor engine uses neither. Both builds meet timing with no failing endpoint.

## FPGA Resource Summary (Estimates)

The estimates below predate the measurements above and are kept for the
per-block breakdown. Typical configuration (8 channels, 512-bit data width,
4096-entry SRAM per channel):

| Resource | Estimate | Notes |
|----------|----------|-------|
| **LUTs** | 15,000 - 25,000 | Logic and control |
| **Registers** | 20,000 - 30,000 | Pipeline and state |
| **Block RAM** | 40 - 60 | SRAM buffer |
| **DSP** | 0 | No DSP usage |

---

## Resource Breakdown by Block

### APB Configuration Slave

| Resource | Estimate |
|----------|----------|
| LUTs | 500 - 800 |
| Registers | 400 - 600 |
| BRAM | 0 |

### Descriptor Engine

One shared engine for every channel in the default build.

| Resource | Estimate |
|----------|----------|
| LUTs | 1,500 - 2,500 |
| Registers | 1,000 - 1,500 |
| BRAM | 1 (descriptor FIFO) |

### Scheduler (8 channels)

| Resource | Estimate |
|----------|----------|
| LUTs | 3,000 - 5,000 |
| Registers | 4,000 - 6,000 |
| BRAM | 0 |

### Channel Arbiter

| Resource | Estimate |
|----------|----------|
| LUTs | 500 - 1,000 |
| Registers | 200 - 400 |
| BRAM | 0 |

### AXI Read Engine

| Resource | Estimate |
|----------|----------|
| LUTs | 2,000 - 3,500 |
| Registers | 3,000 - 4,500 |
| BRAM | 0 |

### SRAM Buffer

| Resource | Estimate |
|----------|----------|
| LUTs | 100 - 200 |
| Registers | 100 - 200 |
| BRAM | 32 - 64 (depth/width dependent) |

### AXI Write Engine

| Resource | Estimate |
|----------|----------|
| LUTs | 2,000 - 3,500 |
| Registers | 3,000 - 4,500 |
| BRAM | 0 |

### MonBus Reporter

| Resource | Estimate |
|----------|----------|
| LUTs | 800 - 1,200 |
| Registers | 600 - 900 |
| BRAM | 1 (event FIFO) |

---

## SRAM Sizing

SRAM buffer size depends on configuration:

| Configuration | BRAM (18Kb) | BRAM (36Kb) |
|---------------|-------------|-------------|
| 512b x 1024 | 16 | 8 |
| 512b x 2048 | 32 | 16 |
| 512b x 4096 | 64 | 32 |
| 256b x 4096 | 32 | 16 |
| 128b x 4096 | 16 | 8 |

---

## Scaling with Parameters

### Channel Count Impact

| Channels | LUT Delta | Register Delta |
|----------|-----------|----------------|
| 1 | Base | Base |
| 2 | +500 | +800 |
| 4 | +1,500 | +2,400 |
| 8 | +3,500 | +5,600 |
| 16 | measured: see Measured Core Area | |

### Data Width Impact

| Data Width | LUT Delta | Register Delta | BRAM Delta |
|------------|-----------|----------------|------------|
| 128 bits | -30% | -40% | -75% |
| 256 bits | -15% | -20% | -50% |
| 512 bits | Base | Base | Base |

---

## ASIC Estimates

For 28nm technology node (typical):

| Metric | Estimate |
|--------|----------|
| **Gate Count** | 200K - 350K gates |
| **Area** | 0.2 - 0.4 mm2 |
| **SRAM Area** | 0.1 - 0.2 mm2 (4096x512) |
| **Total Area** | 0.3 - 0.6 mm2 |

### Power Estimates

| Condition | Power |
|-----------|-------|
| Idle (clock gated) | <1 mW |
| Idle (clock running) | 10 - 20 mW |
| Single channel active | 50 - 100 mW |
| All channels active | 150 - 300 mW |

---

## Timing Estimates

### Target Frequencies

| Technology | Target Fmax |
|------------|-------------|
| Xilinx Ultrascale+ | 250 MHz |
| Agilex | 250 MHz |
| 28nm ASIC | 400 MHz |
| 16nm ASIC | 600 MHz |

### Critical Paths

| Path | Concern Level | Mitigation |
|------|---------------|------------|
| AXI data path | Low | Fully pipelined |
| SRAM read/write | Low | Registered outputs |
| Arbiter decision | Medium | Priority encoder depth |
| Descriptor parse | Low | Simple combinational |

---

**Last Updated:** 2026-01-03
