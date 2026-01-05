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

# 4. Acronyms and References

## Acronyms

| Acronym | Definition |
|---------|------------|
| AXIS | Advanced eXtensible Interface Stream (AXI Stream) |
| DDR | Double Data Rate (memory) |
| DELTA | Distributed Execution Layer for Tensor Acceleration |
| DMA | Direct Memory Access |
| HIVE | Hierarchical Intelligent Verification Engine |
| MM2S | Memory-Mapped to Stream |
| NI | Network Interface |
| NoC | Network-on-Chip |
| PKT | Packet |
| RAPIDS | Rapid AXI Programmable In-band Descriptor System |
| SERV | Simple Embedded RISC-V (monitor core) |
| S2MM | Stream to Memory-Mapped |
| TID | Transaction ID (AXIS sideband signal) |
| TDEST | Transaction Destination (AXIS sideband signal) |
| TUSER | Transaction User (AXIS sideband signal) |
| VC | Virtual Channel |
| XY | X-dimension then Y-dimension (routing algorithm) |

## References

### AMBA Specifications
- AXI4-Stream Protocol Specification v1.0 (ARM IHI 0051A)

### Related Components
- **RAPIDS DMA**: Rapid AXI Programmable In-band Descriptor System
  - See `projects/components/rapids/docs/rapids_spec/`
- **HIVE Control**: VexRiscv-based control plane
  - See `projects/components/hive/` (if available)

### Academic References
- Dally, W. J., & Towles, B. (2004). "Principles and Practices of Interconnection Networks"
- Duato, J., Yalamanchili, S., & Ni, L. (2002). "Interconnection Networks: An Engineering Approach"

---

**Back to:** [Index](../delta_index.md) | **Next Chapter:** [Block Overview](../ch02_blocks/00_block_overview.md)
