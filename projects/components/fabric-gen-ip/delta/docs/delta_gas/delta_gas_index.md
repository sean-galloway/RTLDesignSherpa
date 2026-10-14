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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Delta Generator Architecture Specification Index

## Overview

**Version:** 1.0
**Date:** 2026-10-12
**Purpose:** Detailed documentation of the Delta AXI-Stream fabric generator — flat mode is implemented, mesh mode is planned per the 2026-10-13 design spec, and tree mode is retired — covering how to invoke it, how to configure it, how it emits RTL, and how to extend it safely.

---

## Related Modules

- **[Delta HAS](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/delta/docs/delta_has/delta_has_index.md)** - Hardware Architecture Specification
- **[Delta MAS](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/delta/docs/delta_mas/delta_mas_index.md)** - Micro-Architecture Specification
- **[PRD.md](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/PRD.md)** - Product requirements
- **[CLAUDE.md](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/CLAUDE.md)** - AI development guide

---

## Navigation

**Note:** Every chapter below is one source file; the document build assembles the spec from these links.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [What the Generator Produces](ch01_overview/01_what_the_generator_produces.md)
- [When to Regenerate](ch01_overview/02_when_to_regenerate.md)
- [Generator Entry Points](ch01_overview/03_generator_entry_points.md)

### Chapter 2: Configuration

- [CLI and Programmatic API](ch02_configuration/01_cli_and_programmatic_api.md)
- [Parameter Semantics](ch02_configuration/02_parameter_semantics.md)
- [AMBA 5, TSTRB, and Parity Options](ch02_configuration/03_amba5_tstrb_and_parity.md)
- [Validation Rules](ch02_configuration/04_validation_rules.md)

### Chapter 3: Generation Pipeline

- [Pipeline Overview](ch03_generation_pipeline/01_pipeline_overview.md)
- [Request Decode](ch03_generation_pipeline/02_request_decode.md)
- [Arbitration and Routing](ch03_generation_pipeline/03_arbitration_and_routing.md)
- [Boundary Module Instantiation](ch03_generation_pipeline/04_boundary_module_instantiation.md)

### Chapter 4: Emitted Artifacts

- [Directory Layout](ch04_emitted_artifacts/01_directory_layout.md)
- [Module Header and Parameters](ch04_emitted_artifacts/02_module_header_and_parameters.md)
- [Flat Crossbar](ch04_emitted_artifacts/03_flat_crossbar.md)
- [Tree Primitives](ch04_emitted_artifacts/04_tree_primitives.md)

### Chapter 5: Verification and Regeneration Discipline

- [Full Regeneration Rule](ch05_verification_and_regeneration_discipline/01_full_regeneration_rule.md)
- [Pre-Generated Fixtures](ch05_verification_and_regeneration_discipline/02_pre_generated_fixtures.md)
- [DV Suite](ch05_verification_and_regeneration_discipline/03_dv_suite.md)
- [Lint Checks](ch05_verification_and_regeneration_discipline/04_lint_checks.md)

### Chapter 6: Extension Guide

- [Adding a New Topology](ch06_extension_guide/01_adding_a_new_topology.md)
- [Adding a New Generator Option](ch06_extension_guide/02_adding_a_new_generator_option.md)
- [Adding AMBA 5 Sidebands](ch06_extension_guide/03_adding_amba5_sidebands.md)
- [Testing an Extension](ch06_extension_guide/04_testing_an_extension.md)

---

**Last Updated:** 2026-10-14
**Maintained By:** RTL Design Sherpa Project
