# 1. Virtual Configuration Contexts

## 1.1 Supported Topologies

DELTA supports multiple routing modes via virtual contexts:

### Context 0 - Mesh (XY Routing)

- Standard 2D mesh with XY dimension-ordered routing
- Default mode, always available
- Deadlock-free by construction

### Context 1 - Systolic

- Direct nearest-neighbor communication only
- Router bypass for lowest latency (1-2 cycles/hop)
- North->South and West->East data flow
- Used for matrix multiplication, convolution

### Context 2 - Tree Reduction

- Hierarchical aggregation topology
- Bottom row (tiles 12-15) as leaf nodes
- Top row (tiles 0-3) as aggregators
- Optimized for global reduction operations (sum, max)

### Context 3 - Custom/Debug

- User-programmable routing tables
- Supports arbitrary topologies
- Enables experimentation with novel routing algorithms

## 1.2 Context Characteristics

| Context | Latency | Throughput | Use Case |
|---------|---------|------------|----------|
| Mesh (0) | Medium (3-24 cycles) | High | General-purpose |
| Systolic (1) | Low (1-2 cycles/hop) | Very High | Matrix ops |
| Tree (2) | Variable | Medium | Reductions |
| Custom (3) | User-defined | User-defined | Research |

---

**Next:** [Context Switching](02_context_switching.md)
