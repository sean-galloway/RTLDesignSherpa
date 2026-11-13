# Ramulator 2 for the mem-ctrl-ip models

Method and the comparability rules: `vault/handbook/dv/dram-cycle-model.md`.
Work item: memory-controllers MC-012.

- `fetch.sh` -- clone + pin `vendor/ramulator2` (gitignored), apply the overlay, build; `--test` runs the suites.
- `overlay/` -- the DDR2 / DDR2_BL8 device classes, the `TimedLoadStoreTrace` frontend, the
  `BankFIFO-RR` scheduler (per-bank FIFOs with a rotor: granite's store shape, MC-013 item 4), their tests
  (copied verbatim into the clone by `fetch.sh`; the build's codegen writes the Python wrappers).
- `vendor-registration.patch` -- the four upstream files that list sources (three CMake lists, the smoke table).
- `bin/char_model.py` -- replay the board's characterization families through the model (`run`), or a
  request stream captured from a cocotb sim's AXI port (`run-trace`; the exporter is
  `ddr2_char_framework/dv/tests/perf_axi_trace.py`); `--help` for flags.
- `tests/` -- the stream builder checked against the board host's stride table, the policy configs, the
  trace contract both ends enforce.
