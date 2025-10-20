# 1. Executive Summary

DELTA is a configurable mesh Network-on-Chip (NoC) that routes four distinct packet types between the RAPIDS DMA engine, HIVE control system, and compute tiles. The network implements intelligent packet filtering and routing based on AXIS TUSER encoding, ensuring protocol isolation between data, control, and monitoring traffic.

## Key Features

- 4x4 mesh topology (16 compute tiles) for proof-of-concept
- Four packet types: DATA, DESC, CONFIG, STATUS
- Virtual configuration contexts for topology reconfiguration
- Wormhole flow control with virtual channels
- XY dimension-ordered routing (deadlock-free)
- Per-tile packet filtering and forwarding rules
- AXIS protocol throughout

## Design Goals

1. **Protocol Isolation**: Four packet types routed independently without interference
2. **Flexible Topologies**: Virtual contexts support mesh, systolic, tree, and custom modes
3. **Deadlock-Free**: XY routing with virtual channels guarantees forward progress
4. **Educational Focus**: Clear architecture with hooks for experimentation
5. **Integration**: Seamless connection to RAPIDS DMA and HIVE control plane

## Target Applications

- Machine learning inference acceleration
- Tensor operations on distributed compute tiles
- Network-on-Chip research and education
- Configurable interconnect exploration

---

**Next:** [System Integration](02_system_integration.md)
