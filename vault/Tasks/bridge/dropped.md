<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# bridge — dropped

## WB4 in the bridge is best effort -- the two known gaps stay open by decision
**Dropped 2026-09-13** (owner: "treat wb4 as best effort, nothing is ideal").
Wishbone B4 ports work on both sides of the fabric (BRIDGE-019, HAS 4.6):
one Wishbone transfer becomes one single-beat AXI4 transaction on the way
in, and AXI bursts are decomposed to single classic/linear Wishbone
transfers on the way out. Two things a fuller port would do are NOT owed
and should not be re-proposed without a consumer asking for them:

- **Wishbone burst formation** -- forming CTI/BTE pipelined bursts from an
  AXI burst in `axi4_to_wb4`, and recognising incoming bursts in
  `wb4_to_axi4`. Today the hints are carried, not acted on.
- **A WB4 slave in its own clock domain** -- `cdc = true` is AXI4-only;
  a Wishbone crossing would need its own block.

Both are correctness-neutral: the port is spec-legal as it stands, just not
the fastest Wishbone possible. That is the accepted state.

## Legacy TASK-012 — AXI burst optimization
**Dropped 2026-09-10** while folding in the pre-migration TASKS.md. The item
named no measurement, no target and no consumer; bursts already pass through
unmodified and the width converters do their own re-framing. If a specific
inefficiency is measured (see [[BRIDGE-017]] performance characterization),
file it against that number.

## Legacy TASK-014 — APB3 to APB4 bridge
**Dropped 2026-09-10** while folding in the pre-migration TASKS.md. Nothing
in the tree speaks APB3, and the APB path already covers APB4 and APB5.
