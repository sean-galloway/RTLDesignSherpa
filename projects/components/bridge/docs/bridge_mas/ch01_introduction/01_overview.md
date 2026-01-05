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

# Overview

## Bridge Micro-Architecture

This document describes the internal micro-architecture of Bridge, a multi-protocol AXI4 crossbar generator. Bridge creates parameterized SystemVerilog RTL from CSV/TOML configuration files.

## Key Capabilities

### Multi-Protocol Support

Bridge supports three AMBA protocols:

| Protocol | Use Case | Conversion |
|----------|----------|------------|
| AXI4 Full | High-bandwidth memory | Direct or width convert |
| AXI4-Lite | Register access | Protocol downgrade |
| APB | Low-speed peripherals | Full conversion |

: Table 1.1: Supported Protocols

### Channel-Specific Masters

Bridge generates optimized port interfaces:

| Type | Channels | Signals | Use Case |
|------|----------|---------|----------|
| Full (rw) | AW, W, B, AR, R | 100% | CPU, config master |
| Write-only (wr) | AW, W, B | ~60% | DMA write engine |
| Read-only (rd) | AR, R | ~40% | DMA read engine |

: Table 1.2: Channel-Specific Master Types

### Automatic Converters

Bridge inserts converters automatically:

- **Width converters** - Handle data width mismatches
- **Protocol converters** - AXI4 to APB conversion
- **Per-path optimization** - Only where needed

## Architecture Summary

### Block Organization

```
Bridge NxM
├── Master Adapters (M instances)
│   ├── Skid buffers
│   └── ID extension
├── Crossbar Core
│   ├── Address decode
│   ├── Per-slave arbiters
│   └── Channel muxes
├── Slave Routers (N instances)
│   ├── Protocol converters
│   └── Width converters
└── Response Routing
    ├── ID extraction
    └── Master demux
```

### Signal Flow

```
Master → Adapter → Decode → Arbiter → Mux → Converter → Slave
                                              ↓
Master ← Demux ← ID Extract ← Response ← Converter ← Slave
```

## Document Organization

| Chapter | Content |
|---------|---------|
| Ch 2 | Block Descriptions |
| Ch 3 | FSM Design |
| Ch 4 | ID Management |
| Ch 5 | Converters |
| Ch 6 | Generated RTL |
| Ch 7 | Verification |

: Table 1.3: Document Organization

## Related Documentation

- **Bridge HAS** - High-level architecture and integration
- **PRD.md** - Product requirements
- **Generator source** - `bin/bridge_csv_generator.py`
