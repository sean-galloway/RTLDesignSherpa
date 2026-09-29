# TASK-013: BCH and Reed-Solomon ECC

> Migrated 2026-09-27 from `vault/Tasks/common/dropped.md` as **COMMON-009** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** DROPPED 2026-08-09 (Sean's call; was "deferred, P3")

Library ECC is Hamming SECDED only; BCH and Reed-Solomon were deferred as
niche (NAND flash, deep-space comms). A docs-only `projects/components/bch/`
placeholder was deleted 2026-07-23, leaving this task as the only place BCH
was tracked — and it now ends here: this is not rtl/common library work.

**If Reed-Solomon happens, it happens as `projects/components/ecc-ip/reed-solomon/`**
— a component project with its own PRD/DV/tasks area, not a common-library
primitive. Tracked as **RS-001** in
[vault/Tasks/projects/components/ecc-ip/reed-solomon/](../../../projects/components/ecc-ip/reed-solomon/INDEX.md).
