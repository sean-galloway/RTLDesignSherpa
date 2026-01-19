# Document Information

**Document Title:** RAPIDS Beats Hardware Architecture Specification (HAS)
**Document Number:** RAPIDS-HAS-001
**Version:** 1.0
**Date:** 2026-01-17
**Status:** Released

---

## Purpose

This Hardware Architecture Specification (HAS) defines the external interfaces, system integration requirements, and high-level architecture of the RAPIDS Beats accelerator. It is intended for system architects and integration engineers who need to understand RAPIDS Beats from an external perspective without requiring knowledge of internal implementation details.

## Scope

This document covers:

- External interface specifications (AXI4, AXIS, APB, MonBus)
- System-level block diagrams and data flows
- Programming model and descriptor format
- Use cases and operational sequences
- Performance characteristics and constraints

This document does NOT cover:

- Internal module architecture (see MAS)
- RTL implementation details (see MAS)
- Verification test plans
- Physical design constraints

## Audience

| Role | Relevance |
|------|-----------|
| System Architect | Primary - system integration |
| Hardware Integration Engineer | Primary - interface connection |
| Software Engineer | Primary - driver development |
| Verification Engineer | Reference - interface protocols |
| RTL Designer | Reference - external constraints |

: Target Audience

## Document Conventions

### Requirement Levels

| Term | Meaning |
|------|---------|
| **SHALL** | Mandatory requirement |
| **SHOULD** | Recommended but not mandatory |
| **MAY** | Optional feature |

### Signal Directions

- **Input:** Signal driven by external logic into RAPIDS
- **Output:** Signal driven by RAPIDS to external logic
- **Bidirectional:** Signal can be driven by either side (rare)

### Timing Diagrams

All timing diagrams use WaveDrom format with the following conventions:

- `p` = Positive clock edge
- `n` = Negative clock edge
- `0/1` = Logic low/high
- `x` = Unknown/don't care
- `=` = Data value (with label)
- `.` = Previous value continues

---

## References

| Document | Description |
|----------|-------------|
| RAPIDS Beats MAS | Module Architecture Specification |
| ARM AMBA AXI4 Specification | AXI4 protocol reference |
| ARM AMBA AXI-Stream Specification | AXIS protocol reference |
| RAPIDS PRD | Product Requirements Document |

: Reference Documents
