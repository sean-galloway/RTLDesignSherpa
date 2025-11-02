# Appendix C: Performance Characteristics

## C.1 Latency Model

### Single-Hop Latency

- Input buffering: 1 cycle
- Routing decision: 1 cycle
- Crossbar traversal: 1 cycle
- Output buffering: 1 cycle (optional)
- **Total: 3-4 cycles per hop**

### Multi-Hop Examples (4×4 Mesh)

| Source -> Dest | Hops | Latency (cycles) | Notes |
|----------------|------|------------------|-------|
| T0 -> T1 | 1 | 3-4 | Adjacent (horizontal) |
| T0 -> T4 | 1 | 3-4 | Adjacent (vertical) |
| T0 -> T5 | 2 | 6-8 | XY: East, then South |
| T0 -> T15 | 6 | 18-24 | Worst case (diagonal) |
| T7 -> T12 | 5 | 15-20 | Example peer-to-peer |
| Any -> RAPIDS (avg) | 3.5 | 10-14 | Average to virtual tile 16 |
| Any -> HIVE-C (avg) | 3.5 | 10-14 | Average to virtual tile 17 |

### Context-Dependent Latency

| Context | Per-Hop Latency | Notes |
|---------|-----------------|-------|
| Mesh (XY) | 3-4 cycles | Standard routing |
| Systolic | 1-2 cycles | Router bypass, nearest-neighbor only |
| Tree | Variable | Depends on position in tree |
| Custom | User-defined | Configurable via routing tables |

## C.2 Throughput Analysis

### Per-Link Bandwidth

- 128 bits @ 100 MHz = 1.6 GB/s per direction
- Full-duplex: 3.2 GB/s aggregate per link

### Bisection Bandwidth (4×4 Mesh)

- Horizontal cuts: 4 links × 1.6 GB/s = 6.4 GB/s
- Vertical cuts: 4 links × 1.6 GB/s = 6.4 GB/s
- **Total: 6.4 GB/s bisection**

### Network Aggregate

- 40 total links (24 H + 16 V) in 4×4 mesh
- 40 × 1.6 GB/s = 64 GB/s aggregate
- Actual sustained: 60-70% (38-45 GB/s) due to contention

### Per-Tile Injection/Reception

- Maximum: 1.6 GB/s (single local port)
- Practical: 1.2-1.4 GB/s (accounting for flow control)

## C.3 Resource Utilization

### Per Router (LUTs/FFs/BRAM)

| Component | LUTs | FFs | BRAM (36Kb) |
|-----------|------|-----|-------------|
| Input buffers (5×8 flits) | 2,000 | 1,600 | 64 bits |
| Routing logic | 200 | 150 | 0 |
| VC allocator | 150 | 100 | 0 |
| Crossbar (5×5) | 400 | 200 | 0 |
| Output buffers (5×4 flits) | 800 | 600 | 32 bits |
| **Total per router** | **~3,550** | **~2,650** | **~2** |

### Full 4×4 Network

- 16 routers × 3,550 LUTs = 56,800 LUTs
- 16 routers × 2,650 FFs = 42,400 FFs
- 16 routers × 2 BRAM = 32 BRAM blocks
- **Plus NI overhead: +9,600 LUTs, +6,400 FFs, +4 BRAM**
- **Total DELTA: ~66,400 LUTs, ~48,800 FFs, ~36 BRAM**

### FPGA Utilization Examples

| FPGA Device | LUTs Available | % Used | FFs Available | % Used | BRAM Available | % Used |
|-------------|----------------|--------|---------------|--------|----------------|--------|
| Artix-7 XC7A100T | 63,400 | 105% | 126,800 | 38% | 135 | 27% |
| Kintex-7 XC7K325T | 203,800 | 33% | 407,600 | 12% | 445 | 8% |
| Virtex-7 XC7VX485T | 303,600 | 22% | 607,200 | 8% | 1,030 | 3% |

**Note:** 4×4 DELTA requires mid-range FPGA (Kintex-7 or higher)

## C.4 Power Estimation

### Dynamic Power @ 100 MHz

- Routers (16×): ~120 mW each = 1,920 mW
- Network Interfaces (16×): ~30 mW each = 480 mW
- Interconnect wiring: ~200 mW
- **Total: ~2,600 mW (2.6 W) @ 100 MHz**

### Scaling with Frequency

| Frequency | Est. Power | Notes |
|-----------|-----------|-------|
| 50 MHz | ~1.3 W | Low-power mode |
| 100 MHz | ~2.6 W | Typical operation |
| 200 MHz | ~5.5 W | High-performance (if timing met) |

## C.5 Scalability

### Larger Mesh Sizes

| Mesh Size | Tiles | Routers | Est. LUTs | Est. Power @ 100MHz |
|-----------|-------|---------|-----------|---------------------|
| 2×2 | 4 | 4 | ~16,600 | ~0.7 W |
| 4×4 | 16 | 16 | ~66,400 | ~2.6 W |
| 8×8 | 64 | 64 | ~265,600 | ~10 W |
| 16×16 | 256 | 256 | ~1,062,400 | ~40 W |

**Note:** 8×8 and larger require high-end FPGAs or ASICs

---

**Back to:** [Index](delta_index.md)

**Document Version:** 0.3 (Early Draft - Proof of Concept)
**Last Updated:** 2025-10-19
**Status:** Preliminary specification, subject to significant change
**Maintained By:** DELTA Development Team
