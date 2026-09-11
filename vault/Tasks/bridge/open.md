<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# bridge — open

## BRIDGE-017 — Legacy backlog carried over from projects/components/bridge/TASKS.md
**Status:** open 2026-09-10 (created when the pre-migration file was folded in)
**Priority:** P3. Aspirational items from the 2025 task list that nobody has
asked for since; triage, do, or drop each with a reason.

The retired file's completed and superseded items are in the ledger at the
end of [closed](closed.md) and two are in [dropped](dropped.md). These were
still "Planned" and describe real engineering that has not happened:

- **Performance characterization** (legacy TASK-005): latency and throughput
  numbers for the generated fabrics under saturating traffic, the way STREAM
  and pumice have them. Nothing in the bridge suite measures a cycle count.
- **Synthesis and implementation guide** (TASK-010): the HAS integration
  chapter covers requirements, not a worked Vivado flow with utilization and
  timing for a reference config.
- **Async clock-domain crossing** (TASK-016): every generated fabric is a
  single clock domain; a CDC slave port would use the `axi4_*_cdc` family.
- **QoS with aging** (TASK-017): AxQOS is passed through and ignored by the
  arbiter.
- **Pipeline stages in the crossbar** (TASK-019): the xbar is combinational
  end to end; a registered variant for high-fanout configs.

## BRIDGE-018 — A native-AXI5 fabric
**Status:** open 2026-09-11 (split out of BRIDGE-014 when its master-protocol
half closed)
**Priority:** P3. No feature anyone has asked for needs it.

The crossbar is AXI4-shaped inside, with the AXI5 sideband riding alongside
in the channel structs (BRIDGE-002 A5-2). That covers every AMBA5 feature
delivered so far -- interop sideband, native sideband, atomics of every
class, poison, the Lite and APB5 ports on both sides (BRIDGE-014). What it
cannot express is a feature whose semantics change the fabric's own rules:
read-data chunking (per-beat ordering inside a burst), MTE tags with their
own ordering, or anything that needs the crossbar to reason about AXI5
transaction attributes rather than carry them. If one of those becomes a
requirement, this is where it goes: the structs, the crossbar mux, both
adapters' tracking paths and the response mux all change together.

Not owed until a consumer appears. Related: [[BRIDGE-002]], [[BRIDGE-014]]
(both closed).
