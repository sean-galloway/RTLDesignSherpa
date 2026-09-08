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

# Timing Characterization Micro-Architecture Specification Index

**Component:** Timing Characterization (Synthesis Benchmarking Harness)
**Version:** 1.0
**Date:** 2026-03-18
**Purpose:** Detailed micro-architecture specification for the Timing Characterization component

---

## Document Organization

This specification covers the detailed micro-architecture of `char_top` and its
nine Functional Unit Blocks (FUBs). It provides implementation-level detail for
each block, the shared LFSR anti-optimization engine, synthesis constraint
strategy, and verification infrastructure.

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction
- [Overview](ch01_introduction/01_overview.md)

### Chapter 2: FUB Block Descriptions
- [nand_chain -- NAND Gate Binary Tree](ch02_fub_blocks/01_nand_chain.md)
- [inverter_chain -- Linear Inverter Chain](ch02_fub_blocks/02_inverter_chain.md)
- [xor_tree -- XOR Gate Binary Tree](ch02_fub_blocks/03_xor_tree.md)
- [carry_chain -- Ripple-Carry Adder](ch02_fub_blocks/04_carry_chain.md)
- [multiplier_tree -- Multiplier Wrapper](ch02_fub_blocks/05_multiplier_tree.md)
- [mux_tree -- Binary Mux Tree](ch02_fub_blocks/06_mux_tree.md)
- [queue_depth -- FIFO Queue](ch02_fub_blocks/07_queue_depth.md)
- [clock_divider_chain -- Clock Divider Cascade](ch02_fub_blocks/08_clock_divider_chain.md)
- [gray_counter_chain -- Gray Counter](ch02_fub_blocks/09_gray_counter_chain.md)

### Chapter 3: LFSR Design
- [LFSR Architecture](ch03_lfsr_design/01_lfsr_architecture.md)
- [Data Distribution](ch03_lfsr_design/02_data_distribution.md)

### Chapter 4: Synthesis Strategy
- [SDC Architecture](ch04_synthesis/01_sdc_architecture.md)
- [Anti-Optimization Techniques](ch04_synthesis/02_anti_optimization.md)

### Chapter 5: Verification
- [Test Architecture](ch05_verification/01_test_architecture.md)
- [LFSR Reference Model](ch05_verification/02_lfsr_reference_model.md)

---

## Quick Navigation

### For New Users
1. Start with [Overview](ch01_introduction/01_overview.md)
2. Read [LFSR Architecture](ch03_lfsr_design/01_lfsr_architecture.md) -- the anti-optimization engine
3. Study a representative FUB: [carry_chain](ch02_fub_blocks/04_carry_chain.md)
4. Review [Anti-Optimization Techniques](ch04_synthesis/02_anti_optimization.md)

### For Adding New FUBs
1. Review any existing FUB for the structural pattern
2. Follow [LFSR Data Distribution](ch03_lfsr_design/02_data_distribution.md) for input wiring
3. Check [Anti-Optimization Techniques](ch04_synthesis/02_anti_optimization.md) for required attributes
4. Add test per [Test Architecture](ch05_verification/01_test_architecture.md)

---

## Related Documentation

- **[Timing Characterization HAS](../timing_char_has/timing_char_has_index.md)** -- Hardware Architecture Specification (system-level)
- **[PRD.md](../../PRD.md)** -- Product requirements
- **[SYNTHESIS_GUIDE.md](../../rtl/syn/SYNTHESIS_GUIDE.md)** -- Detailed synthesis workflow

---

**Last Updated:** 2026-03-18
**Maintained By:** RTL Design Sherpa Project
