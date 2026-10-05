# Binary BCH Codec Hardware Architecture Specification Index

## Overview

**Version:** 0.1 (draft)
**Date:** 2026-10-03
**Purpose:** High-level hardware architecture specification for the Binary BCH codec component (`projects/components/ecc-ip/bch/`)

---

## Related Modules

Listed as paths, not links: the document build inlines every Markdown link in
this index, and these are companions, not chapters.

- **PRD** - `projects/components/ecc-ip/bch/PRD.md` - product requirements: the decision table and candidate profiles
- **References** - `projects/components/ecc-ip/bch/References/README.md` - standards and papers, with source and licence
- **CLAUDE.md** - `projects/components/ecc-ip/bch/CLAUDE.md` - area facts for a session working here

---

## Navigation

**Note:** Every chapter below is one source file; the document build assembles the spec from these links.

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction
- [Purpose and Scope](ch01_introduction/01_purpose.md)
- [Document Conventions](ch01_introduction/02_conventions.md)
- [Definitions and Acronyms](ch01_introduction/03_definitions.md)

### Chapter 2: System Overview
- [Use Cases](ch02_system_overview/01_use_cases.md)
- [Key Features](ch02_system_overview/02_key_features.md)
- [System Context](ch02_system_overview/03_system_context.md)

### Chapter 3: Architecture
- [Block Diagram](ch03_architecture/01_block_diagram.md)
- [Data Flow](ch03_architecture/02_data_flow.md)
- [Solver Options](ch03_architecture/03_solver_options.md)

### Chapter 4: Interfaces
- [Core Interface](ch04_interfaces/01_core_interface.md)
- [AXI-Stream Adapter](ch04_interfaces/02_axis_adapter.md)
- [AXI4 Job Adapter](ch04_interfaces/03_axi4_job_adapter.md)
- [Register Block](ch04_interfaces/04_registers.md)
- [Clock and Reset](ch04_interfaces/05_clock_reset.md)

### Chapter 5: Performance
- [Throughput](ch05_performance/01_throughput.md)
- [Latency](ch05_performance/02_latency.md)
- [Resources](ch05_performance/03_resources.md)

### Chapter 6: Integration
- [System Requirements](ch06_integration/01_system_requirements.md)
- [Parameter Configuration](ch06_integration/02_parameters.md)
- [Candidate Profiles](ch06_integration/03_profiles.md)
- [Verification Strategy](ch06_integration/04_verification.md)
- [Synthesis and Implementation](ch06_integration/05_synthesis.md)

### Chapter 7: Understanding the Math
- [Fields and Polynomials](ch07_understanding_the_math/01_fields_and_polynomials.md)
- [From Field to Code](ch07_understanding_the_math/02_the_code.md)
- [Syndromes, the Key Equation, and Correction](ch07_understanding_the_math/03_decoding.md)

---
