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

# Bridge Generator Architecture Specification Index

## Overview

**Version:** 0.9
**Date:** 2026-10-18
**Purpose:** Detailed documentation of the Bridge AXI4/AXI5 crossbar code generator — how to invoke it, how to configure it, how it emits RTL, and how to extend it safely.

---

## Related Modules

- **[Bridge HAS](https://github.com/seang-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/bridge/docs/bridge_has/bridge_has_index.md)** - Hardware Architecture Specification
- **[Bridge MAS](https://github.com/seang-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/bridge/docs/bridge_mas/bridge_mas_index.md)** - Micro-Architecture Specification
- **[PRD.md](https://github.com/seang-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/bridge/PRD.md)** - Product requirements
- **[CLAUDE.md](https://github.com/seang-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/bridge/CLAUDE.md)** - AI development guide

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

- [Bridge-Level TOML Keys](ch02_configuration/01_bridge_level_keys.md)
- [Port Specification Schema](ch02_configuration/02_port_specification_schema.md)
- [Interface Wrapper Configuration](ch02_configuration/03_interface_wrapper_configuration.md)
- [Monitor and CFG Subsystem Keys](ch02_configuration/04_monitor_and_cfg_keys.md)
- [Validation Rules](ch02_configuration/05_validation_rules.md)

### Chapter 3: Generation Pipeline

- [Pipeline Overview](ch03_generation_pipeline/01_pipeline_overview.md)
- [Configuration Loading](ch03_generation_pipeline/02_configuration_loading.md)
- [Validation](ch03_generation_pipeline/03_validation.md)
- [Adapter and Crossbar Emission](ch03_generation_pipeline/04_adapter_and_crossbar_emission.md)
- [Filelist and Test Generation](ch03_generation_pipeline/05_filelist_and_test_generation.md)

### Chapter 4: Emitted Artifacts

- [Directory Layout](ch04_emitted_artifacts/01_directory_layout.md)
- [Package File](ch04_emitted_artifacts/02_package_file.md)
- [Top Module](ch04_emitted_artifacts/03_top_module.md)
- [Adapters and Crossbar](ch04_emitted_artifacts/04_adapters_and_crossbar.md)
- [Filelist](ch04_emitted_artifacts/05_filelist.md)
- [Generated Tests](ch04_emitted_artifacts/06_generated_tests.md)

### Chapter 5: Verification and Regeneration Discipline

- [Full Regeneration Rule](ch05_verification_and_regeneration_discipline/01_full_regeneration_rule.md)
- [Generated Examples](ch05_verification_and_regeneration_discipline/02_generated_examples.md)
- [DV Suite](ch05_verification_and_regeneration_discipline/03_dv_suite.md)
- [Lint and Synthesis Checks](ch05_verification_and_regeneration_discipline/04_lint_and_synthesis_checks.md)

### Chapter 6: Extension Guide

- [Adding a Protocol](ch06_extension_guide/01_adding_a_protocol.md)
- [Adding a Bridge-Level Option](ch06_extension_guide/02_adding_a_bridge_level_option.md)
- [Adding a Port-Level Option](ch06_extension_guide/03_adding_a_port_level_option.md)
- [Testing an Extension](ch06_extension_guide/04_testing_an_extension.md)

---

**Last Updated:** 2026-10-15
**Maintained By:** RTL Design Sherpa Project
