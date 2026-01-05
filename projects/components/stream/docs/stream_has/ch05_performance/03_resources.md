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

## FPGA Resource Summary

Estimates for typical configuration (8 channels, 512-bit data width, 4096-entry SRAM):

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
| Intel Agilex | 250 MHz |
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
