<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, not started)

---


## COMMON-007 — Additional arbiter types
**Status:** open — deferred pending user requests, P3

Token bucket, deficit round-robin, hierarchical arbitration. Current arbiters
cover ~95% of use cases and complex arbiters tend to be application-specific.

## COMMON-008 — Multi-byte CRC support
**Status:** open — deferred pending performance requirements, P3

`dataint_crc.sv` processes one byte per cycle. A 2/4/8/16-byte-per-cycle option
would serve high-throughput consumers, at an area cost.

