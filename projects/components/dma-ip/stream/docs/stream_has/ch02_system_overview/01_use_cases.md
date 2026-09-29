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

# Use Cases

## Primary Use Cases

### Memory-to-Memory Data Movement

**Description:** Transfer data between two memory regions without CPU involvement.

**Operation:**
1. Software prepares descriptor(s) in memory with source/destination addresses
2. Software writes first descriptor address to channel control register
3. STREAM autonomously fetches descriptor and executes transfer
4. Optional interrupt notifies software of completion

**Key Benefits:**
- CPU offloading for bulk data transfers
- Deterministic transfer timing
- Support for large transfer sizes via descriptor chaining

---

### Scatter-Gather Operations

**Description:** Collect data from multiple non-contiguous source regions into a contiguous destination, or distribute contiguous source data to multiple destinations.

**Gather Example:**
```
Descriptor 0: src=0x1000, dst=0x8000, len=64 beats
Descriptor 1: src=0x3000, dst=0x8100, len=32 beats  (chained)
Descriptor 2: src=0x5000, dst=0x8180, len=16 beats  (chained, last)
```

**Scatter Example:**
```
Descriptor 0: src=0x8000, dst=0x1000, len=64 beats
Descriptor 1: src=0x8100, dst=0x3000, len=32 beats  (chained)
Descriptor 2: src=0x8180, dst=0x5000, len=16 beats  (chained, last)
```

---

### Multi-Channel Concurrent Transfers

**Description:** Execute multiple independent transfer operations simultaneously.

**Operation:**
- Up to 8 channels operate concurrently
- Each channel processes its own descriptor chain
- Shared resources (SRAM, AXI masters) arbitrated by priority

**Use Cases:**
- Parallel DMA for multi-stream applications
- Priority-based bandwidth allocation
- Independent channel error isolation

---

## Secondary Use Cases

### Buffer Management

**Description:** Move data between system memory and local buffers for processing pipelines.

**Pattern:**
```
System Memory → STREAM → Processing Buffer → STREAM → System Memory
```

### Memory Initialization

**Description:** Fill memory regions with pattern data using chained descriptors.

**Note:** Requires source buffer containing pattern data.

---

## Target Applications

| Application | Channel Usage | Typical Transfer Size |
|-------------|---------------|----------------------|
| Video Frame Copy | 1-2 channels | 1-8 MB per frame |
| Audio Buffer Management | 1 channel | 4-64 KB per buffer |
| Data Collection | 4-8 channels | Variable |
| Memory Test Patterns | 1-4 channels | System-dependent |

---

**Last Updated:** 2026-01-03
