<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# bridge — open

## BRIDGE-014 — AXI5-Lite and APB5 as MASTER protocols; a native-AXI5 fabric
**Status:** open 2026-09-10 (filed at Sean's request when BRIDGE-002 closed)
**Priority:** P3. No in-tree consumer today.

BRIDGE-002 delivered AXI5 masters and slaves, native sideband through the
fabric structs, atomics of every class, and APB5 / AXI5-Lite as SLAVE
protocols. Two things it named and did not do:

1. **AXI5-Lite and APB5 as master protocols.** Both shipped slave-only by
   decision; a Lite or APB5 requester into the fabric is a different piece
   of work (an `axil5_to_axi4` / `apb5_to_axi4` front end, the master
   adapter's protocol switch, the validator's master whitelist, and a
   fixture with its BFMs). Start from how `protocol = "axil"` masters are
   handled today.
2. **A native-AXI5 fabric.** The original BRIDGE-002 goal called this the
   follow-on. The sideband-in-structs design made it unnecessary for every
   feature anyone has asked for, so the fabric is still AXI4-shaped inside
   with AXI5 fields riding alongside. If a feature ever needs the fabric
   itself to be AXI5 (per-beat chunking, MTE tags with their own ordering
   rules), this is where it goes.

Neither is owed until a consumer appears. Related: [[BRIDGE-002]] (closed).

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
