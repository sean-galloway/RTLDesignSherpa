<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, not started)

---

## COMMON-003 — Create integration examples
**Status:** open — not started (migrated from rtl/common/TASKS.md, P2)

Standalone integration examples showing common usage patterns that combine
multiple common modules. Location: `rtl/integ_amba/examples/`.

Proposed:
- Example 1: state machine with timeout (counter + FSM)
- Example 2: multi-master system (arbiter + counters)
- Example 3: CRC-checked packet buffer (CRC + FIFO)
- Example 4: CDC data transfer (sync + handshake + FIFO)
- Example 5: simple PWM generator (counter + comparator)

Deliverables: 5 standalone designs, a test for each, documentation explaining
the design choices, and a README index. Success = all compile cleanly, all
tests pass, docs complete.


## COMMON-007 — Additional arbiter types
**Status:** open — deferred pending user requests, P3

Token bucket, deficit round-robin, hierarchical arbitration. Current arbiters
cover ~95% of use cases and complex arbiters tend to be application-specific.

## COMMON-008 — Multi-byte CRC support
**Status:** open — deferred pending performance requirements, P3

`dataint_crc.sv` processes one byte per cycle. A 2/4/8/16-byte-per-cycle option
would serve high-throughput consumers, at an area cost.

