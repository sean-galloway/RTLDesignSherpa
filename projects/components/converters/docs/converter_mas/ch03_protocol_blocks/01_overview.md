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

# 3.1 Protocol Conversion Overview

Protocol converters enable communication between components using different communication protocols, essential for integrating diverse IP blocks in complex SoC designs.

## 3.1.1 Available Converters

### AXI4 to AXI4-Lite (Protocol Downgrade)

| Module | Function | Test Status |
|--------|----------|-------------|
| axi4_to_axil4_rd | Read burst decomposition | 14/14 passing |
| axi4_to_axil4_wr | Write burst decomposition | 14/14 passing |
| axi4_to_axil4 | Full bidirectional wrapper | Composed |

: Table 3.1: AXI4 to AXI4-Lite Converters

### AXI4-Lite to AXI4 (Protocol Upgrade)

| Module | Function | Test Status |
|--------|----------|-------------|
| axil4_to_axi4_rd | Read protocol upgrade | 7/7 passing |
| axil4_to_axi4_wr | Write protocol upgrade | 7/7 passing |
| axil4_to_axi4 | Full bidirectional wrapper | Composed |

: Table 3.2: AXI4-Lite to AXI4 Converters

### Other Protocol Converters

| Module | Function | Status |
|--------|----------|--------|
| axi4_to_apb_convert | Full AXI4-to-APB bridge | Production |
| peakrdl_to_cmdrsp | Register interface adapter | Production |
| uart_axil_bridge | UART to AXI4-Lite | Planned |

: Table 3.3: Other Protocol Converters

## 3.1.2 Protocol Comparison

### Figure 3.1: Protocol Feature Comparison

![Protocol Comparison](../assets/mermaid/protocol_comparison.png)

### Feature Matrix

| Feature | AXI4 | AXI4-Lite | APB |
|---------|------|-----------|-----|
| Channels | 5 (AW, W, B, AR, R) | 5 (simplified) | 1 (combined) |
| Bursts | Up to 256 beats | Single beat only | Single beat |
| Out-of-order | Yes (ID-based) | No | No |
| Pipelining | Yes | Optional | No (2-phase) |
| Data widths | 8-1024 bits | 32/64 bits | 8-32 bits |

: Table 3.4: Protocol Feature Comparison

## 3.1.3 Conversion Strategies

### AXI4 to AXI4-Lite

**Challenge:** Decompose multi-beat bursts into sequential single beats.

**Strategy:**
1. Accept AXI4 burst transaction
2. Issue N single-beat AXI4-Lite transactions
3. Aggregate responses
4. Return combined response to AXI4 master

**Complexity:** Medium (FSM-based decomposition)

### AXI4-Lite to AXI4

**Challenge:** Add AXI4 burst signals with appropriate defaults.

**Strategy:**
1. Pass through all AXI4-Lite signals
2. Add default values for burst signals (LEN=0, SIZE=2, BURST=INCR)
3. Add default IDs (configurable)

**Complexity:** Very low (combinational only)

### AXI4 to APB

**Challenge:** Bridge 5-channel AXI4 to 2-phase APB protocol.

**Strategy:**
1. Accept AXI4 transaction
2. Execute APB setup phase
3. Execute APB access phase
4. Return AXI4 response

**Complexity:** High (full protocol FSM)

## 3.1.4 Performance Characteristics

| Converter | Single-Beat | Burst (N) | Area |
|-----------|-------------|-----------|------|
| axi4_to_axil4 | 0 cycles | 2N cycles | ~450 LUTs |
| axil4_to_axi4 | 0 cycles | N/A | ~110 LUTs |
| axi4_to_apb | 3-5 cycles | (3-5)N cycles | ~300 LUTs |

: Table 3.5: Protocol Converter Performance

### Key Observations

1. **Zero-overhead upgrade:** AXI4-Lite to AXI4 is purely combinational
2. **Burst penalty:** AXI4 to AXI4-Lite doubles cycle count for bursts
3. **APB overhead:** 3-5 cycle minimum per APB transaction

## 3.1.5 Use Case Guidelines

### When to Use AXI4 to AXI4-Lite

**Use when:**
- CPU/DMA with burst support needs simple peripheral access
- Want to simplify peripheral design (no burst handling)
- Data widths match (no width conversion needed)
- Burst performance is not critical

**Avoid when:**
- High-bandwidth streaming data
- Latency-critical paths
- Many back-to-back bursts

### When to Use AXI4-Lite to AXI4

**Use when:**
- Legacy AXI4-Lite IP connects to AXI4 fabric
- Designing simple peripheral for AXI4 system
- Want zero-overhead protocol upgrade
- Don't need burst capability

**Avoid when:**
- Need actual burst support (use native AXI4)
- Width conversion needed (use width converters)

### When to Use AXI4 to APB

**Use when:**
- AXI4 masters need APB peripheral access
- Building CPU-to-peripheral bridges
- Integrating legacy APB devices

**Avoid when:**
- High-performance paths (APB is slow)
- Streaming data (APB is sequential)

## 3.1.6 Integration Patterns

### Pattern 1: CPU to Peripherals

```
CPU (AXI4) → AXI4-to-AXIL4 → AXIL4 Peripherals
                          → AXI4-to-APB → APB Peripherals
```

### Pattern 2: Simple IP in AXI4 Fabric

```
Simple IP (AXIL4) → AXIL4-to-AXI4 → AXI4 Crossbar
```

### Pattern 3: Mixed System

```
CPU (AXI4) → AXI4 Crossbar → DDR (AXI4)
                           → AXI4-to-AXIL4 → Config Regs (AXIL4)
                           → AXI4-to-APB → UART, GPIO (APB)
```

---

**Next:** [AXI4 to AXI4-Lite](02_axi4_to_axil4.md)
