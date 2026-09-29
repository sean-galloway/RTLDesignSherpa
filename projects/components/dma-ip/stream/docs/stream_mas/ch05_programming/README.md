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

# Chapter 5: Programming Models

This chapter provides software developer guidance for using the STREAM DMA engine.

## Contents

### 01_initialization.md
- Power-on initialization sequence
- Register configuration
- Channel setup
- Configuration presets (minimal, high-performance)

### 02_single_transfer.md
- Descriptor format (256-bit)
- Kick-off address map and write sequence
- Simple single-descriptor transfer
- C code examples with complete workflow

### 03_chained_transfers.md
- Multi-descriptor chains
- Descriptor linking via next_descriptor_ptr
- Chain termination methods
- Scatter-gather operations
- Prefetch mode for performance

### 04_multi_channel.md
- 8-channel concurrent operations
- Priority-based scheduling
- Resource sharing strategies
- Channel pooling and load balancing
- Performance considerations

### 05_error_handling.md
- Error types (AXI, timeout, internal)
- Error detection registers
- Recovery procedures
- Interrupt-based error handling
- Debug monitoring

## Planned (Future)

### 06_performance_tuning.md
- Burst size selection
- Priority tuning
- SRAM depth considerations
- Maximizing throughput

### 07_software_examples.md
- Complete working examples
- Linux driver skeleton
- Bare-metal usage
- Common use cases

---

**Status:** Core programming guides complete (01-05)

**Target Audience:**
- Software engineers integrating STREAM
- Driver developers
- System architects
- Application developers

---

**Last Updated:** 2025-12-01
