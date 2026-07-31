<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, not started)

---

## COMMON-010 — Every module MUST have a filelist and a registry entry
**Status:** open 2026-07-23

**The rule** (authority: [[filelists]]): every module in `rtl/common/` has a
filelist in `rtl/common/filelists/`, and the area is registered in
`bin/filelists.toml`. A new module lands with its `.f` **in the same commit** —
not "before the test lands". A module with no filelist has no consumers and is
indistinguishable from dead code the next time someone audits.

**Current state is good but unenforced.** `bin/filelist_registry.py --check`
reports common at 57 modules / 55 covered / 0 uncovered. The 2-module gap is
the `[exempt]` ledger, not a hole:

- `fifo_sync_multi` — multi-instance wrapper; no consumer yet
- `fifo_sync_multi_sigmap` — multi-instance wrapper; no consumer yet

**Work:**
1. Resolve the two exemptions: give each a filelist and a consumer, or drop the
   module. "No consumer yet" is a debt entry, not a permanent state.
2. Wire `--check` into a gate. **Nothing runs it today** — not the pre-commit
   hook, not CI (the only workflow is `track-clones.yml`), not a Makefile
   target. A MUST that nothing enforces is a wish. Shared with AMBA TASK-026;
   do the gate once for both.
3. When reading `--check` output, read all three numbers. It prints `PASS` when
   `declared - covered - exempt` is empty, so "55 covered" alongside "0
   uncovered" on a 57-module area is expected and still worth checking.

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

## COMMON-011 — ISSUE-001: counter.sv tick not gated during reset
**Status:** open — known issue, P3 (edge case only). Discovered 2025-10-23.

`rtl/common/counter.sv` assigns `tick` combinationally without suppressing it
under reset:

    assign tick = (r_count == MAX[$clog2(MAX+1)-1:0]);

If reset asserts on the exact cycle where `r_count == MAX`, `tick` asserts for
one cycle while the module is in reset.

Impact is low and the workaround is for consumers to qualify `tick` with
`!rst_n`. The reason it stays on the list is the test debt: the edge-case test
in `val/common/test_counter.py` (~line 335) is **disabled with `if False:`** and
a TODO referencing this issue. A disabled test is a silent one.

Repro: `cd val/common && REG_LEVEL=FULL pytest test_counter.py::test_counter[32-full] -v`

Proposed fix — either gate the output combinationally:

    assign tick = (!rst_n) ? 1'b0 : (r_count == MAX[$clog2(MAX+1)-1:0]);

or register it (adds a cycle of latency). Re-enable the test with the fix.

## COMMON-014 — fifo_control default parameters contradict its own constraint
**Status:** open 2026-07-31 — surfaced by qc round_2 (common part_03), P3 latent

`rtl/common/fifo_control.sv` declares `ADDR_WIDTH = 3` and `DEPTH = 16` as
defaults, while its own header states "DEPTH must equal 2^ADDR_WIDTH (power of
2 depths only)". 2^3 = 8, so the defaults violate the documented contract:

- pointers are 4 bits, addressing 8 slots;
- `(AW+1)'(D)` = `4'(16)` = 0 — the exact truncation the module's comments warn
  about;
- `AFT = DEPTH - ALMOST_WR_MARGIN = 15` is unreachable at max occupancy 8, so
  `wr_almost_full` can never assert.

Latent, not live: both parents override consistently (`fifo_sync` passes
`AW = $clog2(DEPTH)`, and `rtl/cdc/fifo_async` likewise). A standalone
default instantiation silently degrades to depth-8 with dead almost-full logic.

Second, smaller point from the same finding: the header constraint is stricter
than the logic. Via `counter_bin`'s MAX wrap the control equations hold for any
`DEPTH <= 2^ADDR_WIDTH`, which is how `fifo_sync` supports non-power-of-2
depths — so the constraint text overstates the restriction it needs.

Decide: make the defaults self-consistent (e.g. `DEPTH = 8`, or derive
`ADDR_WIDTH = $clog2(DEPTH)`), and relax the header constraint to
`DEPTH <= 2^ADDR_WIDTH`. Owner call — changing a default is visible to any
direct instantiator.

## COMMON-015 — shifter_beat_pack: runtime cfg wider than COUNT_BITS corrupts occupancy
**Status:** open 2026-07-31 — surfaced by qc round_2 (common part_04), P3 misuse corner

`rtl/common/shifter_beat_pack.sv` casts the runtime beat width down to the
occupancy width in two places:

    assign pop_valid = (r_count >= COUNT_BITS'(w_beat_bits)) && (r_count != '0);
    v_count = v_count - COUNT_BITS'(w_beat_bits);

`w_beat_bits` is `BEAT_BITS_W` (CFG_BITS+4) bits; `COUNT_BITS` is
`$clog2(STORAGE_BITS+1)`. At the defaults (STORAGE_BITS=256, COUNT_BITS=9,
CFG_BITS=8) a runtime `cfg_beat_bytes_m1 >= 63` encodes a beat >= 512 bits,
which truncates to **0**: `pop_valid` degenerates to `(r_count != 0)`, the pop
shifts `v_data >> 512` (zeroing the data) and subtracts 0 from the count, so
the packer asserts `pop_valid` forever against corrupted accounting. Values
between `STORAGE_BITS` and `2^COUNT_BITS - 1` (e.g. a 264-bit beat) instead
stall `pop_valid` permanently.

The elaboration guard only checks the STATIC `MAX_BEAT_BITS < STORAGE_BITS`;
nothing checks the runtime value. Misuse-only — the docs do tell callers that
any runtime beat width must fit the storage — but the failure mode is silent
data corruption rather than a clean stall, so a saturating compare or a runtime
assertion is worth the gate.

## COMMON-006 — Configurable-width adders/multipliers
**Status:** open — deferred pending user feedback, P3

Complex adders/multipliers are generated by Python in `bin/rtl_generators/`.
Parameterized SystemVerilog versions in the library were considered. Current
generation works well and parameterized versions may synthesise less optimally;
this is an educational-value vs practicality trade-off. Kept as open rather
than dropped because the decision was "not now", not "no".

## COMMON-007 — Additional arbiter types
**Status:** open — deferred pending user requests, P3

Token bucket, deficit round-robin, hierarchical arbitration. Current arbiters
cover ~95% of use cases and complex arbiters tend to be application-specific.

## COMMON-008 — Multi-byte CRC support
**Status:** open — deferred pending performance requirements, P3

`dataint_crc.sv` processes one byte per cycle. A 2/4/8/16-byte-per-cycle option
would serve high-throughput consumers, at an area cost.

## COMMON-009 — BCH and Reed-Solomon ECC
**Status:** open — deferred, P3. **Re-check before starting.**

Library ECC is Hamming SECDED only; BCH and Reed-Solomon were deferred as niche
(NAND flash, deep-space comms). A `projects/components/bch/` component once
existed as a docs-only placeholder (PRD/README/TASKS, no RTL and no tests) and
was **deleted 2026-07-23**, so this task is NOT superseded — it is the only
place BCH is tracked.
