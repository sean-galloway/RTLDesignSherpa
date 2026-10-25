# TASK-020: make the read-return-atomic tracker depth a per-slave TOML key, and report it

**Date:** 2026-10-19
**Priority:** P3
**Status:** CLOSED 2026-10-24 (per-slave `atomic_rr_depth`, reported in the package and the sizing report; the stall measured at 2 and at 8)
**Owner:** unassigned
**Where:** `bin/bridge_pkg/generators/slave_adapter_generator.py` (`_atom_tracker_lines`), `config_loader.py`, `config_validator.py`

## Why

Each atomic slave port tracks its read-return atomics (AtomicLoad / Swap /
Compare) in an `axi5_atomic_rr_tracker` built with a hard-coded
`DEPTH(8)`. That is a real limit -- eight read-return atomics in flight per
slave port; the ninth AW stalls -- and until 2026-10-19 no document stated
the number (the MAS said only that the AW is held while the tracker is
full). Owner's rule: a limit built into the fabric must be communicated.

There is no limit on the NUMBER of atomic masters: every fabric ID carries
its master's index, so atomics from different masters never alias at a
slave.

## Work

1. Slave key `atomic_rr_depth` (power of two, 2..64, default 8). The
   validator rejects other values, and rejects the key on a slave that
   is not an atomic `rw` AXI5 port.
2. The generator prints each atomic slave's depth in its build log, and the
   generated `<bridge>_pkg.sv` carries it as a localparam.
3. Docs: MAS 2.10, HAS 4.4 and the TOML key table name the key and default.
4. Regenerate every bridge (`make regen`) and run the bridge suite; the
   default keeps every existing bridge byte-identical.

## Done when

- A bridge built with `atomic_rr_depth = 2` stalls the third read-return
  atomic in sim (a test, red against a depth-8 build).
- The limit is stated where a user reads the TOML keys.

## Done (2026-10-24)

- Slave key `atomic_rr_depth`, power of two 2..64, default 8; the loader
  rejects it on a master and on any slave that is not an `axi5` rw port
  with `atomic` in its features. `slave_adapter_generator._atom_tracker_lines`
  builds `axi5_atomic_rr_tracker` to it; `<bridge>_pkg.sv` carries
  `<SLAVE>_ATOMIC_RR_DEPTH`; `<bridge>_sizing.json` reports it beside the
  other depths (pinned or default -- there is no loop model for it). The
  default keeps every existing bridge byte-identical apart from the two
  comment lines and the package constants.
- Fixture `bridge_1x2_rw_axi5a_rr2` (both slaves at 2) and
  `test_bridge_1x2_rw_axi5a_rr_depth.py`: with the master's RREADY held
  (the driver's stall policy) sixteen read-return atomics go out; the
  adapter's own `atom_full` rises exactly at the depth -- 8 on the default
  fixture, 2 on rr2 -- its `aw_rr_blocked` then holds the next atomic AW for
  tens of cycles, and once RREADY is released every atomic returns the
  word's prior value. The hold is inside the adapter, upstream of the slave
  port's pins, which is why it is measured on the adapter's crossbar-side
  nets. Generated tests of the fixture 9/9 at FULL.
- Docs: MAS 2.10, HAS 4.4, HAS 6.2 slave row, GENERATOR_ARCHITECTURE,
  bridge CLAUDE.md, the stress model's PRD limit row.
