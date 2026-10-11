# DFX Hardware Architecture Specification (HAS) — Index

**Version:** 0.1 (started 2026-10-11)
**Status:** Draft — access-model chapter landed, interfaces/planes pending
**Scope:** The house-wide debug port: JTAG transport, config poke plane,
core override plane, and their relationship to the existing monlite
observation plane. Test plane (scan/BIST) is reserved future scope.

## Chapters

| Chapter | Title | Status |
|---|---|---|
| [ch00](ch00_front_matter/00_document_info.md) | Front Matter / Document Info | Draft |
| [ch01](ch01_overview/01_purpose_and_scope.md) | Purpose, Scope, and Relationship to monlite | Draft |
| [ch02](ch02_architecture/01_access_model.md) | The Access Model — config plane vs override plane | Draft |
| ch03 | Component Architecture (jtag-tap, jtag-axil-agent, riscv-debug) | Reserved |
| ch04 | Interfaces — JTAG pins, BSCANE2, DMI, AXIL4, core debug | Reserved |
| ch05 | Clocking and CDC — the TCK domain | Reserved |
| ch06 | Safety and Security Posture | Reserved |
| ch07 | Verification Approach | Reserved |
| ch08 | Test Plane (scan / BIST) — future | Reserved |

## Reading order

ch01 → ch02 gives the whole design in two short reads. Everything else is
chapter-per-block detail as RTL lands.
