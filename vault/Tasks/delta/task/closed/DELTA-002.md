# DELTA-002: author the delta HAS and MAS books

**Status:** CLOSED 2026-10-12 (commit in the fabric-gen-ip docs batch). Delta
was re-homed and un-retired (tooling TASK-031) and gained generator richness
(DELTA-001) with no architecture books; the owner asked for the HAS/MAS to be
"updated" like the other fabric IPs — which meant authoring them from
scratch.
**Priority:** P3
**Filed from:** owner doc batch ("please update the bridge/delta has/mas").

## What changed

- New `docs/delta_has/` — system-level spec: configuration (all parameters
  incl. the 2026-10-12 STRB_WIDTH/PW_WIDTH conditional ports + generator CLI),
  base + rich interface signal tables, routing/atomicity/backpressure
  behavior, integration, verification status (no dv/ suite yet — stated).
- New `docs/delta_mas/` — microarchitecture: request decode, per-slave RR
  arbiter with packet-atomic grant, crossbar mux, TREADY steering, AMBA5
  wakeup steering, counters, assertions, cycle-level examples.
- House naming (`delta_has/delta_has_index.md`, `generate_has_pdf.sh`, …),
  house-style graphviz whole-unit diagram per book, v1.0 renders built and
  delivered to the owner's Kindle.
