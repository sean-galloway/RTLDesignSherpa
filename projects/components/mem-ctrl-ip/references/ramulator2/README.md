# Ramulator 2 for the mem-ctrl-ip models

Method and the comparability rules: `vault/handbook/dv/dram-cycle-model.md`.
Work item: memory-controllers MC-012.

- `fetch.sh` -- clone + pin `vendor/ramulator2` (gitignored), apply the overlay, build; `--test` runs the suites.
- `overlay/` -- the DDR2 / DDR2_BL8 device classes, the `TimedLoadStoreTrace` frontend, their tests
  (copied verbatim into the clone by `fetch.sh`).
- `vendor-registration.patch` -- the three upstream files that list sources (two CMake lists, the smoke table).
- `bin/char_model.py` -- replay the board's characterization families through the model; `--help` for flags.
- `tests/` -- the stream builder checked against the board host's stride table.
