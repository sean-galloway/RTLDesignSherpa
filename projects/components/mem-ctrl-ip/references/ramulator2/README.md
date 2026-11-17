# Ramulator 2 for the mem-ctrl-ip models

Method and the comparability rules: `vault/handbook/dv/dram-cycle-model.md`.
Work items: memory-controllers MC-012 (the model), MC-013 / MC-016 (policies), MC-018 (the SKU).

- `fetch.sh` -- clone + pin `vendor/ramulator2` (gitignored), apply the overlay, build; `--test` runs the suites.
- `overlay/` -- the DDR2 / DDR2_BL8 device classes, the `TimedLoadStoreTrace` frontend, the
  `BankFIFO-RR` scheduler (per-bank FIFOs with a rotor: granite's store shape, MC-013 item 4; `peek_depth` lets a
  bank's row-conflict head yield to a younger row hit within its first N entries, MC-016), the `GraniteSKU`
  controller (`src/ramulator/controller/impl/granite_sku_controller.cpp`: the granite FPGA SKU as a controller --
  bank-FIFO store with `BANK_CAP_MIXED` checked at every push, a four-cycle admission pipeline from
  the AXI beat to a schedulable head, the pick core's bank-timed request with the rank-level timers
  holding the fire, its select and direction register, the row lane, close-on-drain, one command slot
  per MC cycle; every knob a one-term variant, MC-018 / ISSUE-004), the
  `DDR2_GRANITE_SKU100` timing preset (the host's MC-cycle derivation in CK, with the PHY-window `nRTW`),
  their tests (copied verbatim into the clone by `fetch.sh`; the build's codegen writes the Python wrappers).
- `vendor-registration.patch` -- the four upstream files that list sources (three CMake lists, the smoke table).
- `bin/char_model.py` -- replay the board's characterization families through the model (`run`), or a
  request stream captured from a cocotb sim's AXI port (`run-trace`; the exporter is
  `ddr2_char_framework/dv/tests/perf_axi_trace.py`); `board-compare` puts the SKU configs beside a board CSV
  set cell by cell with a per-family tolerance; `sweep` runs configs x patterns into one CSV and the
  pattern x variant table; `--help` for flags and `run --config` for the config names (`granite_sku100`,
  its `_bi` / `_close` board presets, the `sku_*` one-term variants). `GRANITE_SKU_DEBUG=<from_ck>:<to_ck>`
  prints the SKU controller's slot state, picks, lane loads and holds in that window and every direction
  flip of the run. `run-trace --split` re-stamps each direction's ticks with its own beat order (a captured
  port's ticks describe the shared port, not the two channels).
- `tests/` -- the stream builder checked against the board host's stride table, the policy configs, the
  trace contract both ends enforce.
