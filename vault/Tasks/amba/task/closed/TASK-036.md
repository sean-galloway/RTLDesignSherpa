# TASK-036: Write Monitor System Whitepaper

> Migrated 2026-09-27 from `vault/Tasks/amba/open.md` as **TASK-024** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P3
**Status:** CLOSED 2026-09-28 -- v1.0 draft in the tree; Sean edits in place as author
**Owner:** Sean (author) / Claude (assist)
**Deliverable:** `docs/markdown/rtl-amba/monitor_system_whitepaper.md`
> Note (2026-07-22): the 2026-05-29 stub is not present in the current tree; recreate it when this task starts.

**Description:**
2-3 page whitepaper that frames the monitor system as a *design surface*
for SoC integrators -- not a status snapshot of what is in place, but a
guide to which knobs the integrator owns and how to spend them. Different
from `docs/markdown/rtl-amba/overview.md` (which describes the as-built
implementation) and from the per-module specs under `shared/` (which
describe specific blocks). This paper sits one level up: "here is the
spine, here are the axes, here are the tweaks."

**Section outline** (stub already in place):

1. **Identity space allocation** -- UNIT_ID / AGENT_ID / CHANNEL_ID as
   designer-owned. Includes the worked example of allocating UNIT_ID one
   level down so each unit gets up to 16 internal sub-busses to track.
2. **Where to insert monitoring** -- per-port (current default), mid-fabric
   (for localizing fabric-internal violations), root-of-tree (aggregate
   only, trades resolution for area).
3. **Timestamp policy** -- current locked to the monbus_group family's local
   counter. Future direction: hybrid `{global_us[47:0], local_cyc[15:0]}`
   so cross-subsystem correlation and per-wrapper resolution share the
   same 64-bit field. Also a note on PTP / external time-source variant.
4. **Drain path selection** -- err FIFO (IRQ) vs. write FIFO (bulk
   trace), per-packet-type routing via `cfg_*_err_select`.
5. **Packet-type filtering** -- masking strategy, the
   completion+performance congestion pitfall, runtime-reconfigurable
   masks via control APB.
6. **Aggregation topology** -- tree-of-arbiters default, WRR variant for
   skewed traffic, protocol-partitioned groups.

**Out of scope** for the whitepaper (covered elsewhere):
- Packet bit-layout (in `docs/markdown/rtl-amba/includes/monitor_package_spec.md`)
- Per-module port lists / timing (in `docs/markdown/rtl-amba/monitor/{module}.md`)
- Specific test recipes (in the relevant test source).

**Completion checklist** (already mirrored at the bottom of the stub):
- [x] Deployment numbers: the bridge fixture's measured table (full vs lite, both parts) in "What it costs", and the per-variant characterization page linked from it (TASK-034). The Nexys A7 stream_char figures were not used: that board carries no monbus group.
- [x] One diagram per section, as-built beside the tweak (seven mermaid sources under `docs/markdown/assets/mermaid/monitor_wp_*.mmd`, rendered to `assets/rtl-amba/`).
- [x] Each section links its module page (`monitor/monbus_group.md`, `monitor/axi_monitor_lite.md`, `includes/monitor_package_spec.md`, the observer, the arbiters).
- [ ] Expand the timestamp section into an appendix once the hybrid-global scheme is prototyped -- still future; the section states the recommendation and that neither variant is prototyped.
- [x] Verification section added. The named error-injection test is not in the tree; it points at the block-ready suite, the lite soak's accounting identity and the group-core formal harness instead, and says so.


---

---

## CLOSED 2026-09-28

`docs/markdown/rtl-amba/monitor_system_whitepaper.md`, v1.0, about 1,500
words plus seven diagrams, following the six-section outline above: the
spine, then identity allocation (with the unit_id nibble-split worked
example), insertion points (per port / mid-fabric observer / root of tree,
with the area trade in numbers), timestamp policy (the group's local counter
today; the hybrid `{global_us[47:0], local_cyc[15:0]}` and the external-source
variant as the two open directions), drain selection (error FIFO with
interrupt versus the write FIFO ring, steered by `err_select`), packet-type
filtering (enables, type mask, event mask, the completion+performance
congestion rule, the lite's drop-and-report), aggregation topology (RR tree,
weighted PWM arbiter, protocol-partitioned groups), what it costs, and how to
validate a tweak. Linked from `rtl-amba/index.md` and `overview.md`. The
owner line stands: Sean is the author and edits in place; this is the
assist's draft, written so every number is cited to a page or report.
