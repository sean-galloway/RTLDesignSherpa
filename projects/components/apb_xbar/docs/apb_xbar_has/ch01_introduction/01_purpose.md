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

# Purpose and Scope

## Document Purpose

This Hardware Architecture Specification (HAS) describes the APB Crossbar component at a system integration level. It provides sufficient detail for:

- **System architects** to evaluate the component for SoC integration
- **Hardware engineers** to plan interconnect topology and address mapping
- **Software engineers** to understand register access paths and address spaces
- **Verification engineers** to develop system-level test plans

## Component Overview

The APB Crossbar is a parametric MxN interconnect fabric that connects multiple APB masters to multiple APB slaves. It provides:

- **Automatic address-based routing** to appropriate slave
- **Fair round-robin arbitration** when multiple masters access the same slave
- **Zero-bubble throughput** for back-to-back transactions
- **Scalable configuration** from 1x1 to 16x16

## Document Scope

### In Scope

- System-level architecture and block organization
- External interface specifications (all APB signals)
- Address mapping and routing strategy
- Arbitration policy and fairness guarantees
- Performance characteristics (latency, throughput)
- Integration requirements and parameters

### Out of Scope

- Internal RTL implementation details (see MAS)
- Detailed timing diagrams for internal signals
- Synthesis and implementation guidance
- Test infrastructure details

## Specification Level

This HAS represents a **black-box** view of the APB Crossbar:

| Aspect | HAS Coverage | MAS Coverage |
|--------|--------------|--------------|
| External ports | Complete | Complete |
| Functional behavior | Complete | Complete |
| Internal architecture | Overview only | Detailed |
| FSM states | - | Complete |
| Timing paths | Interface only | All paths |
| RTL structure | - | Complete |

: HAS vs MAS Coverage Comparison

---

**Next:** [Document Conventions](02_conventions.md)
