<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# bridge — dropped

## Legacy TASK-012 — AXI burst optimization
**Dropped 2026-09-10** while folding in the pre-migration TASKS.md. The item
named no measurement, no target and no consumer; bursts already pass through
unmodified and the width converters do their own re-framing. If a specific
inefficiency is measured (see [[BRIDGE-017]] performance characterization),
file it against that number.

## Legacy TASK-014 — APB3 to APB4 bridge
**Dropped 2026-09-10** while folding in the pre-migration TASKS.md. Nothing
in the tree speaks APB3, and the APB path already covers APB4 and APB5.
