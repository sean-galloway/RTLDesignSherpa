---
title: STREAM char host tools
summary: Inventory of the flows-stream-bridge/host runner suite (sim + silicon).
---

# STREAM characterization host tools

The host-side runner suite for the STREAM characterization flows lives in
`projects/NexysA7/stream_characterization/flows-stream-bridge/host/`. Every tool
drives harness CSRs over the UART byte protocol and runs unchanged against the
cocotb sim transport or the real serial port -- the method is [[uart-harness]];
all register access is [[registers-by-name]] (never hardcoded offsets). The
monitor coverage flow ([[monitor-board-coverage]]) reuses these same modules and
adds only its profile-CAM load + dense-bin sweep on top.

## Address maps (single source of truth, by name)
- `harness_addrs.py` -- `H("KICK_GO")` etc.; harness CSR block @ 0x0001_0000,
  resolved from `harness_csr_regmap.py`.
- `stream_addrs.py` -- `A("SCHED_CONFIG")` etc.; STREAM APB registers incl. the
  MON regfile @ 0x1000, resolved from `stream_regmap.py`.

## DMA / descriptor programming
- `stream_device.py` -- the core host API: `build_stream_bus(bridge)` composes
  `stream` (a `Stream` Device with `load_chain`/`load_ext`/`kick`/`run`) and
  `harness` onto one injected bridge. This is what a new campaign builds on.
- `descriptor_builder.py` -- build legacy chains and extended (dma_address_gen)
  descriptors.
- `harness_kick.py` -- the KICK_GO burst fast path (one write pulses many
  channels; note the 0xC0 KICK_GO split, see [[registers-by-name]]).

## Monitor configuration
- `mon_configs.py` -- named monitor-cone presets applied via `.apply(write)`:
  `perf-mon`, `debug-basic`, `debug-compl`, `debug-all`, `debug-core`. Enabling a
  cone = set its ENABLE bit AND clear its PKT_MASK drop bit (the classic gotcha).
  Address-range (AddrMatch, type 0x8) match windows are the RDMON/WRMON
  `ADDR_RANGEn_LOW/HIGH` + `ADDR_RANGE_CTRL` MON CSRs.

## Campaign runners
- `run_characterization.py` -- the STREAM DMA characterization runner (perf matrix).
- `stream_ext_char.py` / `stream_ext_suite.py` -- extended-addressing (row/col x
  row/col) campaigns; `stream_ext_char_report.py` renders the Markdown report.
- `characterize.py`, `probe_multichannel.py` -- driver + quick post-run per-channel
  CRC/beat probe.

## Monbus + trace readout
- `dump_monbus.py` / `dump_monbus_sram.py` -- decode the monbus trace SRAM into
  packets (agent/protocol/type/event). The way to discover the real on-silicon
  packet mix before building a profile legal set.
- `capture_raw_trace.py` -- drain the debug_sram to a raw file.
- `per_source_capture.py` -- per-source trace capture.

## Perf / status readout
- `read_bus_meters.py`, `read_rw_perf.py`, `read_desc_perf.py` -- perf-window and
  per-channel bucket counters.
- `dump_status.py` -- quick status dump for a hung run.
- `hb_measure.py` / `monbus_halfbeat_model.py` -- on-board half-beat (32-bit slot)
  packing measurement.

## Descriptor verify
- `verify_descriptors.py`, `desc_ram_check.py`, `dump_descriptors.py` -- desc_ram
  round-trip / readback.

## Board-less guards (pytest, no hardware)
- `test_stream_device.py`, `test_harness_regmap.py`, `test_mon_configs.py`,
  `test_dump_monbus*.py` -- prove each regmap composes as its own Device and the
  by-name access holds, without a board.
