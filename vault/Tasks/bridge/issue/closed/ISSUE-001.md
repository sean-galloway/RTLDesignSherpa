# ISSUE-001: bridge_stream_char_axil.toml stopped generating on 2026-09-11 and nothing noticed for two weeks

**Priority:** P2
**Status:** closed 2026-09-26 (opened 2026-09-26)
**Owner:** seang

## What was observed

`bridge_generator.py --ports .../bridge_stream_char_axil.toml --connectivity
.../bridge_stream_char_axil_connectivity.csv` exits 1 with

    bridge_pkg.config_validator.ValidationError: AXI-Lite master 'host' must
    have id_width=0 (AXI4-Lite/AXI5-Lite have no transaction IDs). Got id_width=8

Reported 2026-09-26 as "you broke the bridge generator flow", attributed to
the bridge-wide monitor-lite swap of the day before (`e92a5ae2d`).

## Diagnosis

Not that change. The same command at detached scratch worktrees of
`e92a5ae2d^` and `74bad59f1^` (before any monitor-lite work) fails with the
identical message. The rule is bridge TASK-004's (was BRIDGE-014; `9baaa9d65`, 2026-09-11): an
AXI-Lite MASTER carries no boundary ID ports, so `id_width` must be 0; the
check is master-only. `d83c33971` (2026-09-19) applied it to
`bridge_stream_mon_axil.toml` because the Genesys builds regenerate that
bridge and died before Vivado started. It left the char config alone on
purpose: "referenced only in stream_harness.sv comments, is not instantiated,
and no build regenerates it". So the char config sat un-generatable for two
weeks, and every agent who tried it concluded the generator was broken.

The gap is structural: the generator's own suite validates only
`bridge_batch.csv`, and a board flow regenerates only the bridge it builds.
A consumer config that no build touches is checked by nothing.

## Resolution

- `host` and `monbus_wr` in `bridge_stream_char_axil.toml` -> `id_width = 0`,
  comment rewritten to say why. Slaves keep their widths (8 on the AXI-Lite
  slaves, 10 on desc_ram per bridge TASK-005, was BRIDGE-016). Same shape as `d83c33971`.
- Regenerated through `projects/fpga-systems/Genesys2/stream/bin/regen_bridges.sh
  bridge_stream_char_axil`. The plain bridge's top module is byte-identical
  (only `host_adapter.sv` / `monbus_wr_adapter.sv` pick up the placeholder-ID
  comment); the `_mon` variant picks up the `_monlite` wrappers like every
  other bridge. Both lint clean under verilator. The area's hand-maintained
  DV for the char bridge passes from a clean build.
- Gate: `projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py::
  test_every_consumer_config_loads_and_validates` loads and validates every
  hand-written bridge config under `projects/fpga-systems/**/rtl/bridges/configs/`
  and the non-batch `test_configs/` fixtures; a companion test asserts the
  glob reached both board areas. Mutation-checked: it rejects the HEAD
  config with the message above. Handbook:
  `vault/handbook/design/generated-rtl-discipline.md`, "A config outside the
  batch is an ungated config".

## Found on the way: the monitor-test generator sniffed the name

`generate_monitor_tests` set `is_regblock = 'regblock' in bridge_name`. True
of one batch fixture, false of every consumer bridge: both Genesys 2 stream
bridges set `use_cfg_regblock = true`, so their `_mon` tops have no `cfg_*`
pins and a `s_cfg_axil_*` port, yet their monitor tests were emitted (and
hand-copied) with `IS_REGBLOCK = False` -- the pin-driven stress flow, whose
cfg helpers no-op against absent pins. The regmap path was also hard-wired to
`projects/components/fabric-gen-ip/bridge/rtl/generated/`. Both now derive from the config
and the output directory. Batch output is byte-identical (the one regblock
fixture already had the name); the two Genesys hand-maintained monitor tests
now say `IS_REGBLOCK = True`, name their `*_cfg_regmap.py`, and carry
`BLOCK_READY_PATH = ""` for the lite.

## Not done here

The `_mon` variant's Genesys DV (`test_bridge_stream_char_axil_mon_monitor.py`)
is hand-maintained and predates the lite regblock; its result is recorded in
the fixing commit. Rebuilding bitstreams against the regenerated bridge is
the board owner's call; the plain bridge's boundary did not move.
