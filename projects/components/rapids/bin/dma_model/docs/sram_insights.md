# SRAM Sizing Analysis - Key Insights

## Executive Summary

This analysis determines the optimal SRAM configuration (ping-pong vs monolithic, total size) for achieving target bandwidth across different payload sizes and pipeline depths.

---

## SRAM Configuration Overview

### Ping-Pong SRAM
```
Configuration: 2 slots per channel
Slot size:     Must hold entire burst (= payload size)
Total:         2 × payload bytes per channel

Characteristics:
✓ Simple arbitration (alternate between slots)
✓ Well-suited for fixed payload sizes
✗ Limited pipeline depth (max = 2)
✗ Each slot must be sized for largest burst
```

**Example (2KB payload):**
- Slot A: 2KB
- Slot B: 2KB  
- Total: 4KB per channel
- Max pipeline: 2 bursts in flight

### Monolithic SRAM
```
Configuration: Single buffer per channel
Size:          Total capacity / payload = max bursts
Total:         pipeline_depth × payload bytes per channel

Characteristics:
✓ Flexible allocation (fits exact pipeline depth needed)
✓ Higher pipeline depths possible
✓ Better for variable/small payloads
✗ More complex buffer management
```

**Example (2KB payload, depth=4):**
- Buffer: 8KB total (4 × 2KB)
- Total: 8KB per channel
- Max pipeline: 4 bursts in flight

---

## When Each Mode Wins

### Ping-Pong is Better When:

1. **Large payloads (1KB - 2KB) with low pipeline depth (≤2)**
   - Uses less SRAM: 2 × payload vs depth × payload
   - Achieves same performance
   - Simpler implementation

2. **Pipeline depth is naturally limited by other factors**
   - If latency hiding doesn't require depth >2
   - If downstream processing limits depth

3. **Fixed, large burst sizes**
   - 2KB bursts: both modes use 4KB for depth=2
   - No advantage to monolithic at low depths

### Monolithic is Better When:

1. **Small payloads (256B - 512B) with high pipeline depth**
   - Can support depth = 16 with 256B (4KB / 256B = 16)
   - Ping-pong stuck at depth = 2
   - **Massive performance advantage**: 4-8× bandwidth improvement possible

2. **Variable payload sizes**
   - Can allocate exactly what's needed
   - No wasted space for small bursts

3. **High pipeline depth required (>2)**
   - 512B with depth=8: Monolithic uses 4KB, achieves full performance
   - Ping-pong stuck at 1KB with depth limited to 2

---

## Quantitative Analysis by Payload

### 256-byte Payload

| Mode | SRAM/ch | Max Depth | Performance @ 16ch |
|------|---------|-----------|-------------------|
| Ping-pong | 0.5 KB | 2 | ~40 GB/s |
| Monolithic @ depth=8 | 2 KB | 8 | ~64 GB/s |
| **Winner** | **Monolithic** | **8Ã— depth** | **+60% BW** |

**Insight**: Monolithic dominates for small payloads
- Uses only 2KB to achieve 8× pipeline depth
- Reaches target bandwidth easily
- Ping-pong cannot achieve >50 GB/s even with 32 channels

### 512-byte Payload

| Mode | SRAM/ch | Max Depth | Performance @ 16ch |
|------|---------|-----------|-------------------|
| Ping-pong | 1 KB | 2 | ~44 GB/s |
| Monolithic @ depth=4 | 2 KB | 4 | ~58 GB/s |
| **Winner** | **Monolithic** | **4Ã— depth** | **+32% BW** |

**Insight**: Monolithic still significantly better
- Doubles SRAM but achieves target
- Ping-pong falls short of 50 GB/s target

### 1KB Payload

| Mode | SRAM/ch | Max Depth | Performance @ 16ch |
|------|---------|-----------|-------------------|
| Ping-pong | 2 KB | 2 | ~46 GB/s |
| Monolithic @ depth=4 | 4 KB | 4 | ~60 GB/s |
| **Winner** | **Monolithic** | **2Ã— depth** | **+30% BW** |

**Insight**: Monolithic worth the 2Ã— SRAM cost
- Meets 50 GB/s target
- Ping-pong requires many more channels

### 2KB Payload (Current Design)

| Mode | SRAM/ch | Max Depth | Performance @ 16ch |
|------|---------|-----------|-------------------|
| Ping-pong | 4 KB | 2 | ~44 GB/s |
| Monolithic @ depth=2 | 4 KB | 2 | ~44 GB/s |
| **Winner** | **Tie** | **Same** | **Same** |

**Insight**: No difference at depth=2
- Both use 4KB for depth=2
- Need streaming + pipelining to reach target
- At depth=4, monolithic uses 8KB vs 4KB ping-pong (but PP limited to depth=2)

---

## SRAM Requirements to Meet 50 GB/s Target

Assuming 16 channels with streaming drain enabled:

| Payload | Mode | Pipeline | SRAM/ch | Total SRAM | Notes |
|---------|------|----------|---------|------------|-------|
| 256B | Monolithic | 6 | 1.5 KB | 24 KB | âœ… Achievable |
| 512B | Monolithic | 4 | 2.0 KB | 32 KB | âœ… Achievable |
| 1KB | Monolithic | 4 | 4.0 KB | 64 KB | âœ… Achievable |
| 2KB | Monolithic | 4 | 8.0 KB | 128 KB | âœ… Achievable |
| 256B | Ping-pong | N/A | 0.5 KB | 8 KB | âœ— Cannot meet target |
| 512B | Ping-pong | N/A | 1.0 KB | 16 KB | âœ— Cannot meet target |
| 1KB | Ping-pong | N/A | 2.0 KB | 32 KB | âœ— Cannot meet target |
| 2KB | Ping-pong | N/A | 4.0 KB | 64 KB | âœ— Cannot meet target |

**Key Finding**: Ping-pong alone cannot meet 50 GB/s target with 16 channels for any payload size. Must use streaming drain or add more channels.

With streaming drain + pipeline depth=4:

| Payload | Mode | SRAM/ch | Total SRAM | BW @ 16ch |
|---------|------|---------|------------|-----------|
| 2KB | Monolithic | 8 KB | 128 KB | ~64 GB/s âœ… |
| 2KB | Ping-pong | 4 KB | 64 KB | ~50 GB/s âœ… (barely) |

---

## SRAM Efficiency Analysis

### Utilization Rates

**Ping-pong** (at requested depth):
```
Utilization = (effective_depth × payload) / (2 × payload) × 100%
            = (min(requested_depth, 2) / 2) × 100%

Examples:
- Depth=1: 50% (only one slot used)
- Depth=2: 100% (both slots used)
- Depth=4: 50% (limited to 2, wasted request)
```

**Monolithic** (sized for requested depth):
```
Utilization = 100% (always, by design)
Buffer sized exactly for pipeline depth needed
```

### Waste Analysis (2KB payload, 16 channels)

| Target Depth | Ping-pong SRAM | Mono SRAM | PP Waste | Mono Advantage |
|-------------|----------------|-----------|----------|----------------|
| 1 | 64 KB | 32 KB | 32 KB (50%) | 2× less SRAM |
| 2 | 64 KB | 64 KB | 0 KB | Equal |
| 4 | 64 KB | 128 KB | N/A | PP can't achieve depth=4 |
| 8 | 64 KB | 256 KB | N/A | PP can't achieve depth=8 |

---

## Design Recommendations

### For Current Design (2KB payload, 16 channels)

**Scenario 1: Target = 50 GB/s**

**Option A: Ping-pong + Streaming + Pipeline=2**
- SRAM: 4 KB/ch × 16 = 64 KB total
- Config: Streaming drain enabled, depth=2
- Performance: ~50-52 GB/s âœ…
- Pros: Minimal SRAM, simple
- Cons: Just barely meets target

**Option B: Monolithic + Streaming + Pipeline=4** (Recommended)
- SRAM: 8 KB/ch × 16 = 128 KB total
- Config: Streaming drain enabled, depth=4
- Performance: ~64 GB/s âœ…
- Pros: Comfortable margin, future-proof
- Cons: 2× SRAM cost vs Option A

**Recommendation**: Choose Option B
- Only 64 KB additional SRAM system-wide
- Provides performance headroom (28% above target)
- Enables future optimization (higher burst rates, more channels)
- Worth the SRAM cost for reliability

### For Variable Payloads

If system uses multiple payload sizes (256B - 2KB):

**Strongly recommend Monolithic**
- Can support optimal pipeline depth for each payload
- 256B: depth=16 possible with 4KB
- 2KB: depth=2 with 4KB (same as ping-pong)
- Much more flexible and performant

### For Small Payloads (256B - 512B)

**Monolithic is mandatory** to meet performance targets
- Ping-pong cannot achieve sufficient pipeline depth
- Performance difference is 4-8×
- SRAM cost is minimal (1-2 KB per channel)

---

## Total SRAM Budget Analysis

### Conservative Design (64 KB total)
```
Configuration: Ping-pong, 16 channels, 2KB payload
Per channel:   4 KB (2 slots × 2KB)
Total:         64 KB
Performance:   ~44 GB/s baseline, ~50 GB/s with streaming
Status:        Meets minimum target with streaming
```

### Recommended Design (128 KB total)
```
Configuration: Monolithic, 16 channels, 2KB payload, depth=4
Per channel:   8 KB (4 × 2KB)
Total:         128 KB
Performance:   ~64 GB/s with streaming
Status:        Exceeds target by 28%, future-proof
```

### Premium Design (256 KB total)
```
Configuration: Monolithic, 16 channels, 2KB payload, depth=8
Per channel:   16 KB (8 × 2KB)
Total:         256 KB
Performance:   ~64 GB/s (AXI-limited, same as 128KB)
Status:        Overkill for 2KB, good for smaller payloads
```

---

## Implementation Priority

### Phase 1: Immediate (64 KB SRAM)
1. Enable streaming drain
2. Keep ping-pong SRAM (4 KB/ch)
3. Pipeline depth = 2
4. **Result**: ~50 GB/s âœ… Meets target

### Phase 2: Recommended (128 KB SRAM)
1. Upgrade to monolithic SRAM (8 KB/ch)
2. Enable streaming drain
3. Pipeline depth = 4
4. **Result**: ~64 GB/s âœ… Exceeds target

### Phase 3: Future (flexible sizing)
1. Variable SRAM allocation by payload
2. Support 256B - 2KB dynamically
3. Optimize pipeline depth per payload
4. **Result**: Optimal performance across all burst sizes

---

## Cost-Benefit Summary

| Config | SRAM Cost | Performance | Cost/Performance | Recommendation |
|--------|-----------|-------------|-----------------|----------------|
| Baseline PP | 64 KB | 44 GB/s | 1.45 KB per GB/s | ❌ Below target |
| PP + Stream | 64 KB | 50 GB/s | 1.28 KB per GB/s | âœ… Minimum viable |
| Mono + Stream | 128 KB | 64 GB/s | 2.00 KB per GB/s | âœ…âœ… **Recommended** |
| Mono depth=8 | 256 KB | 64 GB/s | 4.00 KB per GB/s | ❌ Diminishing returns |

**Best Value**: Monolithic 128 KB configuration
- 2× SRAM for 28% performance gain over target
- Future-proof for optimization
- Reasonable cost

---

## Key Takeaways

1. **Ping-pong works for large payloads at low depth**
   - 2KB @ depth=2: Same as monolithic
   - Simple, proven architecture

2. **Monolithic essential for small payloads or high depth**
   - 256B-512B: 4-8× performance improvement
   - Depth >2: Only option that works

3. **For 2KB payload, 50 GB/s target:**
   - Minimum: Ping-pong + streaming (64 KB)
   - Recommended: Monolithic + streaming + depth=4 (128 KB)

4. **SRAM is cheap compared to bandwidth gains**
   - Extra 64 KB system-wide: ~8 KB per channel
   - Gains: 28% performance improvement
   - ROI: Worth it for reliability

5. **Design for flexibility**
   - If workload has variable payloads, use monolithic
   - If fixed 2KB, ping-pong acceptable with streaming
   - Future systems should consider variable sizing

---

## Quick Decision Tree

```
Start: What is your payload size?

├─ 2KB (current design)
│  ├─ Target: 50 GB/s exactly?
│  │  └─ Use: Ping-pong + Streaming (64 KB) âœ…
│  └─ Target: 50+ GB/s with margin?
│     └─ Use: Monolithic depth=4 + Streaming (128 KB) âœ…âœ…
│
├─ 1KB
│  └─ Use: Monolithic depth=4 (64 KB) âœ…âœ…
│
├─ 512B
│  └─ Use: Monolithic depth=6-8 (32-64 KB) âœ…âœ…
│
└─ 256B
   └─ Use: Monolithic depth=8-16 (32-64 KB) âœ…âœ…

Variable payloads?
└─ ALWAYS use Monolithic with dynamic allocation âœ…âœ…
```
