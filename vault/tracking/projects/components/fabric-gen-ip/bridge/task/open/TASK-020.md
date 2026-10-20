# TASK-020: make the read-return-atomic tracker depth a per-slave TOML key, and report it

**Date:** 2026-10-19
**Priority:** P3
**Status:** OPEN
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
