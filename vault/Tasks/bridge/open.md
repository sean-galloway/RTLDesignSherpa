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

## BRIDGE-015 — Out-of-order slave tracking (enable_ooo) could not elaborate
**Status:** open 2026-09-10, in work the same day (Sean: "it worked fine a few
months ago").
**Priority:** P1. A configuration knob that silently produced RTL no tool
could build.

`enable_ooo = true` on a slave selects `bridge_cam` for its response
tracking. BRIDGE-011 (c64660f47) added not-full gating to the FIFO paths and
bound `wr_trk_full` / `rd_trk_full` / `w_sub_*ready` in the wrapper override
for BOTH modes, but declared them only on the FIFO side, so a CAM-mode
adapter referenced nets that did not exist. No fixture used the mode, so
nothing noticed. Repair: the CAM paths declare the nets and drive the full
flags from the CAM's own `tags_full`; the A5-3b return tracker sits beside
the CAM as it does beside the FIFO; new fixture `bridge_2x2_ooo` with both
slaves reordering (the TB now builds `enable_ooo` slaves' BFMs with
`enable_ooo=True`), and a hand-written test that drives interleaved reads
from two masters through a reordering slave.

## BRIDGE-016 — Master-unique transaction IDs: prepend the master index
**Status:** open 2026-09-10, in work the same day (Sean: "there is supposed
to be a unique id for every master, that gets prepended").
**Priority:** P1.

Inside the fabric every transaction ID becomes `{master index, master id}`:
the widest master's id_width plus `$clog2(NUM_MASTERS)` bits, zero for a
single master. Eight-bit masters behind a 16-master bridge give 12-bit IDs
at the slaves. The master adapter forms the prefixed ID on every fabric arm
(direct, width converter, Lite aligner); responses return with the prefix
and the adapter's existing low-bit select strips it. The package exports
`MASTER_ID_WIDTH` / `ID_PREFIX_WIDTH` / `XBAR_ID_WIDTH`; every other site
sizes from `width_utils.xbar_id_width`. The validator requires each AXI
slave's declared `id_width` to be at least the widened width and names the
number. The `bridge_id` routing sideband stays; the prefix is what makes
per-ID tracking sound across masters, which BRIDGE-015 needs.

**Downstream:** the FPGA-system bridges (`bridge_ddr2_char_{rd,wr}`, 2
masters; `bridge_stream_{char,mon}_axil`, 3 and 4 masters) will now fail
validation on their next PREBUILD regeneration until their slave `id_width`
is raised and whatever the slave ports connect to is sized to match. That
is deliberate: a loud validation error rather than a silently truncated ID.

