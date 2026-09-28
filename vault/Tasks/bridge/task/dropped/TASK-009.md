# TASK-009: WB4 in the bridge is best effort -- the two known gaps stay open by decision

> Migrated 2026-09-27 from `vault/Tasks/bridge/dropped.md` (tooling TOOL-001). The source heading carried no ID -- it read "WB4 in the bridge is best effort -- the two known gaps sta" -- so this item is identified for the first time here. Body preserved as written.
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
