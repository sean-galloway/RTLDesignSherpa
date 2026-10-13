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

# Descriptor Scheduling

HIVE-C implements a multi-level queue scheduler over the descriptor pool.
Scheduling is policy — all ordering decisions live in firmware; the hardware
contract is only that injected descriptors reach RAPIDS in injection order
per priority queue.

## Priority Levels

| Level | Class | Examples |
|-------|-------|----------|
| 0 (highest) | Real-time / latency-sensitive | Small control transfers, urgent spills |
| 1 | Standard compute data movement | Activation/weight loads, result drains |
| 2 | Background / prefetch | Next-layer prefetch, cache warming |
| 3 (lowest) | Debug / trace | Trace dumps, instrumentation |

: Descriptor priority classes

## Scheduling Policy

1. Round-robin within a priority level
2. Strict priority across levels: a non-empty higher level preempts issue
   (already-injected descriptors are never reordered)
3. Age-based promotion: a descriptor waiting 1000 cycles promotes one level
4. Deadline-aware tie-break for level-0 descriptors

## Channel-Aware S2MM Programming

The critical correctness rule: **S2MM descriptors must name the tile that will
send the results**, because RAPIDS matches incoming PKT_DATA `tid` against
armed S2MM channels.

```c
// Direct mapping: Tile N sends with TID=N, routes to Channel N
#define TILE_TO_CHANNEL(tile_id)  (tile_id)  // Identity mapping

void program_s2mm_descriptor(uint8_t source_tile) {
    descriptor_t desc;
    desc.type         = DESC_S2MM;                  // Network → Memory
    desc.src_addr     = 0;                          // Not used for S2MM
    desc.dst_addr     = result_buffer[source_tile]; // DDR write address
    desc.length       = result_size;
    desc.source_tile  = source_tile;                // Descriptor[15:12]
    desc.dest_tile    = 16;                         // RAPIDS virtual tile
    inject_descriptor(&desc);
    // RAPIDS arms S2MM Channel[source_tile]; a PKT_DATA with tid == source_tile
    // consumes this descriptor.
}
```

## Worked Example: Matrix-Multiply Layer

```c
void execute_matmul_layer(uint8_t num_tiles) {
    // Phase 1: send activations to all participating tiles (MM2S)
    for (int tile = 0; tile < num_tiles; tile++) {
        descriptor_t mm2s_desc;
        mm2s_desc.type        = DESC_MM2S;          // Memory → Network
        mm2s_desc.src_addr    = activation_buffer[tile];
        mm2s_desc.dst_addr    = 0;                  // Not used for MM2S
        mm2s_desc.length      = activation_size;
        mm2s_desc.dest_tile   = tile;               // TDEST routing to tile
        mm2s_desc.source_tile = 0;                  // Not used for MM2S
        mm2s_desc.priority    = 0;
        inject_descriptor(&mm2s_desc);
    }

    // Phase 2: pre-program S2MM descriptors for result collection.
    // CRITICAL: one per expected source tile, channel = tile_id.
    for (int tile = 0; tile < num_tiles; tile++) {
        program_s2mm_descriptor(tile);
    }

    wait_for_all_tiles_complete();
}
```

If a result arrives with a `tid` that matches no armed channel, RAPIDS
flags it; HIVE-C's error policy (log, halt, or degrade) applies. A missing
S2MM descriptor is a firmware bug, not a hardware fault — this is the
channel-mapping invariant the firmware must maintain.

---

**Last Updated:** 2026-10-12
