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

# Chained Descriptor Transfers

**Chapter:** 05.03
**Version:** 1.0
**Last Updated:** 2025-12-01

---

## Overview

STREAM supports descriptor chaining, allowing multiple transfers to execute sequentially without software intervention. This improves throughput by eliminating per-descriptor software overhead.

---

## Chain Concepts

### Descriptor Linking

Each descriptor contains a `next_descriptor_ptr` field:
- **Non-zero:** Address of next descriptor to fetch
- **Zero:** End of chain (no more descriptors)

Additionally, the `last` control bit explicitly marks chain termination.

### Chain Execution Flow

```
1. Software writes first descriptor address to CHx kick-off register
2. Hardware fetches descriptor from memory
3. Hardware executes transfer (src → dst)
4. If next_descriptor_ptr != 0 AND last != 1:
   a. Fetch next descriptor
   b. Execute transfer
   c. Repeat step 4
5. If next_descriptor_ptr == 0 OR last == 1:
   a. Mark channel complete
   b. Generate interrupt (if gen_irq set on last descriptor)
```

---

## Building a Descriptor Chain

### Memory Layout

```
Descriptor 0 @ 0x1000_0000:
  src_addr = 0x8000_0000
  dst_addr = 0x9000_0000
  length = 64 beats (4KB)
  next_descriptor_ptr = 0x1000_0020  ──────┐
  control = VALID                          │
                                           │
Descriptor 1 @ 0x1000_0020:  <─────────────┘
  src_addr = 0x8000_1000
  dst_addr = 0x9000_1000
  length = 64 beats (4KB)
  next_descriptor_ptr = 0x1000_0040  ──────┐
  control = VALID                          │
                                           │
Descriptor 2 @ 0x1000_0040:  <─────────────┘
  src_addr = 0x8000_2000
  dst_addr = 0x9000_2000
  length = 64 beats (4KB)
  next_descriptor_ptr = 0x0000_0000        │
  control = VALID | LAST | GEN_IRQ   <─────┘ (End of chain)
```

---

## Code Example: Scatter-Gather Copy

### Define Descriptor Chain Structure

```c
#define MAX_CHAIN_LENGTH 16

typedef struct {
    stream_descriptor_t *descriptors[MAX_CHAIN_LENGTH];
    int count;
    uint64_t phys_base;  // Physical base address of descriptor array
} descriptor_chain_t;

// Allocate contiguous descriptor array
descriptor_chain_t *alloc_chain(int max_descriptors) {
    descriptor_chain_t *chain = malloc(sizeof(descriptor_chain_t));
    if (!chain) return NULL;

    // Allocate contiguous array (32-byte aligned)
    void *desc_mem;
    size_t size = max_descriptors * sizeof(stream_descriptor_t);
    if (posix_memalign(&desc_mem, 32, size) != 0) {
        free(chain);
        return NULL;
    }
    memset(desc_mem, 0, size);

    // Set up pointers
    for (int i = 0; i < max_descriptors; i++) {
        chain->descriptors[i] = (stream_descriptor_t *)desc_mem + i;
    }
    chain->count = 0;
    chain->phys_base = virt_to_phys(desc_mem);

    return chain;
}
```

### Add Descriptors to Chain

```c
/**
 * Add a transfer to the descriptor chain
 * @param chain  Chain to add to
 * @param src    Source physical address
 * @param dst    Destination physical address
 * @param size   Transfer size in bytes
 * @return 0 on success, -1 if chain full
 */
int chain_add_transfer(descriptor_chain_t *chain,
                       uint64_t src, uint64_t dst, size_t size) {
    if (chain->count >= MAX_CHAIN_LENGTH) {
        return -1;
    }

    stream_descriptor_t *desc = chain->descriptors[chain->count];

    desc->src_addr = src;
    desc->dst_addr = dst;
    desc->length = BYTES_TO_BEATS(size);
    desc->control = DESC_VALID;

    // Link to next descriptor (will be updated by finalize)
    // Physical address = base + (index + 1) * descriptor_size
    desc->next_descriptor_ptr = 0;  // Will be set by chain_finalize()

    chain->count++;
    return 0;
}

/**
 * Finalize chain - link descriptors and mark last
 * @param chain  Chain to finalize
 * @param irq    Generate interrupt on completion
 */
void chain_finalize(descriptor_chain_t *chain, int irq) {
    if (chain->count == 0) return;

    // Link all descriptors except last
    for (int i = 0; i < chain->count - 1; i++) {
        // Next descriptor is at base + (i+1) * 32 bytes
        uint64_t next_phys = chain->phys_base + (i + 1) * sizeof(stream_descriptor_t);
        chain->descriptors[i]->next_descriptor_ptr = (uint32_t)next_phys;
    }

    // Mark last descriptor
    stream_descriptor_t *last = chain->descriptors[chain->count - 1];
    last->next_descriptor_ptr = 0;
    last->control |= DESC_LAST;
    if (irq) {
        last->control |= DESC_GEN_IRQ;
    }

    // Flush all descriptors to memory
    cache_flush(chain->descriptors[0], chain->count * sizeof(stream_descriptor_t));
}
```

### Execute the Chain

```c
/**
 * Execute descriptor chain on specified channel
 * @param channel Channel number (0-7)
 * @param chain   Finalized descriptor chain
 * @return 0 on success, error code otherwise
 */
int chain_execute(int channel, descriptor_chain_t *chain) {
    if (chain->count == 0) return -1;

    // Kick off with first descriptor address
    stream_kick_off(channel, chain->phys_base);

    // Wait for completion
    return stream_wait_complete(channel, 30000);  // 30 second timeout
}
```

---

## Complete Example: Multi-Buffer Scatter-Gather

```c
/**
 * Copy multiple non-contiguous buffers to contiguous destination
 * (Gather operation)
 */
int gather_copy(uint64_t *src_buffers, size_t *src_sizes, int num_buffers,
                uint64_t dst_base) {
    descriptor_chain_t *chain = alloc_chain(num_buffers);
    if (!chain) return -1;

    uint64_t dst_offset = 0;

    // Build chain for each source buffer
    for (int i = 0; i < num_buffers; i++) {
        int ret = chain_add_transfer(chain,
                                     src_buffers[i],
                                     dst_base + dst_offset,
                                     src_sizes[i]);
        if (ret != 0) {
            free_chain(chain);
            return -1;
        }
        dst_offset += src_sizes[i];
    }

    // Finalize with interrupt
    chain_finalize(chain, 1);

    // Execute on channel 0
    int result = chain_execute(0, chain);

    // Cleanup
    free_chain(chain);

    return result;
}

/**
 * Copy contiguous source to multiple non-contiguous buffers
 * (Scatter operation)
 */
int scatter_copy(uint64_t src_base,
                 uint64_t *dst_buffers, size_t *dst_sizes, int num_buffers) {
    descriptor_chain_t *chain = alloc_chain(num_buffers);
    if (!chain) return -1;

    uint64_t src_offset = 0;

    // Build chain for each destination buffer
    for (int i = 0; i < num_buffers; i++) {
        int ret = chain_add_transfer(chain,
                                     src_base + src_offset,
                                     dst_buffers[i],
                                     dst_sizes[i]);
        if (ret != 0) {
            free_chain(chain);
            return -1;
        }
        src_offset += dst_sizes[i];
    }

    // Finalize with interrupt
    chain_finalize(chain, 1);

    // Execute on channel 0
    int result = chain_execute(0, chain);

    // Cleanup
    free_chain(chain);

    return result;
}
```

---

## Chain Performance Considerations

### Prefetch Mode

Enable prefetch for better chain throughput:

```c
// Enable descriptor prefetch
// DESCENG_CTRL[1] = prefetch_enable
write32(STREAM_BASE + 0x220, 0x00000083);  // enable + prefetch + thresh=8
```

**With Prefetch:**
- Next descriptor fetched while current transfer executes
- Hides descriptor fetch latency
- ~15-30% throughput improvement for chained transfers

**Without Prefetch:**
- Wait for transfer complete, then fetch next
- Simpler logic, easier to debug

### Optimal Chain Length

| Chain Length | Overhead | Use Case |
|--------------|----------|----------|
| 1-2 descriptors | ~5% | Single transfers, low latency |
| 4-8 descriptors | ~2% | Typical scatter-gather |
| 16+ descriptors | <1% | Large file transfers |

: Optimal Chain Length

**Note:** Very long chains (100+) may cause timeout issues. Consider breaking into multiple chains.

---

## Chain Termination Methods

### Method 1: Zero next_descriptor_ptr

```c
desc->next_descriptor_ptr = 0;  // Chain ends
```

### Method 2: Set last flag

```c
desc->control |= DESC_LAST;  // Explicit termination
```

### Recommended: Both

```c
desc->next_descriptor_ptr = 0;
desc->control |= DESC_LAST | DESC_GEN_IRQ;
```

---

## Interrupt Placement

### Option A: Interrupt on Last Only

```c
// Only last descriptor generates interrupt
for (int i = 0; i < chain->count; i++) {
    chain->descriptors[i]->control = DESC_VALID;
}
chain->descriptors[chain->count-1]->control |= DESC_LAST | DESC_GEN_IRQ;
```

**Pros:** Minimal interrupt overhead
**Cons:** No progress visibility

### Option B: Interrupt on Each

```c
// Every descriptor generates interrupt
for (int i = 0; i < chain->count; i++) {
    chain->descriptors[i]->control = DESC_VALID | DESC_GEN_IRQ;
}
chain->descriptors[chain->count-1]->control |= DESC_LAST;
```

**Pros:** Progress tracking
**Cons:** High interrupt rate

### Option C: Periodic Interrupts

```c
// Interrupt every N descriptors
for (int i = 0; i < chain->count; i++) {
    chain->descriptors[i]->control = DESC_VALID;
    if ((i + 1) % 4 == 0) {  // Every 4th descriptor
        chain->descriptors[i]->control |= DESC_GEN_IRQ;
    }
}
chain->descriptors[chain->count-1]->control |= DESC_LAST | DESC_GEN_IRQ;
```

**Pros:** Balanced progress/overhead
**Cons:** More complex

---

## Error Handling in Chains

If an error occurs mid-chain:

1. Channel enters `CH_ERROR` state
2. Remaining descriptors are NOT processed
3. `SCHED_ERROR` register shows which channel errored
4. Software must reset channel and restart from beginning

```c
// Check for chain error
uint32_t sched_error = read32(STREAM_BASE + 0x170);
if (sched_error & (1 << channel)) {
    // Error occurred - reset channel
    write32(STREAM_BASE + 0x124, (1 << channel));  // CHANNEL_RESET
    usleep(10000);  // Wait for reset
    write32(STREAM_BASE + 0x124, 0);  // Release reset

    // Determine which descriptor failed (check channel state)
    // Restart chain or report error
}
```

---

## Related Documentation

- **[Single Transfer](02_single_transfer.md)** - Basic transfer operation
- **[Multi-Channel](04_multi_channel.md)** - Concurrent channel usage
- **[Error Handling](05_error_handling.md)** - Error recovery

---

**Last Updated:** 2025-12-01
