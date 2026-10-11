# Document Info

**Document:** DFX-IP Hardware Architecture Specification (dfx_has)
**Version:** 0.1
**Status:** Draft — scaffold; access-model chapter is the authoritative
seed, remaining chapters reserved
**Date:** 2026-10-11
**Owner:** sean galloway
**Applies to:** `projects/components/dfx-ip/` and every component that
mounts the house debug port

## Revision history

| Version | Date | Change |
|---|---|---|
| 0.1 | 2026-10-11 | Area scaffolded; access model recorded per owner ruling: "riscv needs override control deep down. most other IP only need access to their configs." |

## Conventions

- **Plane** — an independent access path (observation / config poke /
  core override). Planes compose but never share state.
- Components are named per the family README; RTL module names are
  snake_case per house rule.
- The monlite observation fabric is specified elsewhere (per-component
  HAS/MAS chapters); this document only references it.
