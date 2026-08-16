---
title: Genesys 2 / stream
summary: The STREAM component on the Genesys 2 - two builds (monitor validation, characterization) over one shared component layer.
---

# Genesys 2 -- stream

`projects/fpga-systems/Genesys2/stream/` -- STREAM on the Kintex-7 XC7K325T,
in the [[area-structure]] layout. One component, two builds over a shared
component layer:

```
Genesys2/stream/
  conftest.py   pytest config for EVERY build (ancestor of both build dirs)
  bin/          stream_env.py + the host libraries BOTH builds import
                (harness_addrs, stream_addrs, stream_device,
                 characterization, descriptor_builder, harness_kick,
                 mon_configs, bus_meters, rw_perf, desc_perf,
                 stream_ext_suite, stream_ext_report)
                + regen_bridges.sh, gen_harness_regmap.py
  rtl/          stream_harness.sv, stream_genesys2_top.sv, harness_csr,
                axi_response_delay, led_status_driver, seven_seg_4digit,
                sram_chan_tracker + bridges/ (generated)
  dv/tbclasses/ StreamHarnessTB -- the UART transport, shared by both builds
  build-mon/    monitors ON,  4 channels  -> stream_genesys2_top
  build-perf/   monitors OFF, 8 channels  -> stream_genesys2_top
```

ONE `stream_harness.sv` and ONE `stream_genesys2_top.sv`, at component level.
The two builds are the same design at different parameters -- they do not have
separate RTL, separate tcl, separate constraints or separate tops. A build
directory holds only what is genuinely its own: a Makefile of variables, its
host programs, its tests.

Everything under `bin/` and `rtl/` used to be `stream_char_framework/`, owned by
neither flow and reached by both through a sibling-directory path walk. As a
component layer it has one owner and no walk.

## Running a build

The uniform targets ([[build-flows]]); nothing here is stream-specific:

```sh
cd projects/fpga-systems/Genesys2/stream/build-mon
make targets                 # what exists on disk: tcl, host programs, sequences
make lint                    # verilator, whole harness -- seconds
make sim                     # cocotb harness sim, no board
make bitstream               # synth/impl/bitgen + reports
make program                 # JTAG (see [[boards]] for the target trap)
make host-mon_matrix         # a host program, by name
make host-mon_matrix ARGS="--only basic"
```

`make host-<name>` comes from globbing `host/host_*.py` -- see [[flow-layout]]
for why the prefix, and why a library must not carry it.

## build-mon: two bitstreams, and why the name matters

The datapath monitors cannot fit every packet-class cone at once, so the build
comes in two flavors selected by `MON_ERROR_FLAVOR`:

| Flavor | Cones built | Covers |
|---|---|---|
| `0` (default) | everything EXCEPT error | completion, timeout, threshold, perf, debug, AddrMatch |
| `1` | error only | ADDR_RANGE allowlist-miss errors |

The flavor is encoded in the artifact name --
`stream_mon_all_except_error.bit` / `stream_mon_error.bit` -- because a single
fixed name meant `make bitstream MON_ERROR_FLAVOR=1` silently overwrote the
other, leaving no way to tell from disk which was on the board. A missing cone
then presents as "the monitor did not catch the fault", which is a long way to
travel to find a filename problem. The Makefile owns the name and exports it as
`FPGA_BITSTREAM`; the tcl never re-derives it.

Coverage itself -- what the tally counts and why it is shaped that way -- is
[[monitor-board-coverage]], and the board campaign is [[testplan]].

## build-perf

The characterization flavor: `USE_AXI_MONITORS=0`, 8 channels. Its host runner
suite is [[host-tools]]; the object-by-object catalogue is [[host-objects]].

**What "monitors off" does and does not turn off.** The heavy in-core monitor
cones are gone -- which is what lets the design fit a smaller part and run all
8 channels -- but the inline `axi4_intf_master_observer` is instantiated OUTSIDE that
gate and keeps metering the bus. That separation is the whole reason a perf
build is useful, and it regressed once: `USE_AXI_MONITORS=0` over-gated the
cheap always-on bus meters too, and the build reported zeros that looked like
"the DMA did nothing" rather than "the counters were compiled out". The
consequence for host tools is a hard split:

| Tool | Needs | Reads |
|---|---|---|
| `host-bus_meters` | nothing -- works on both flavors | external observer buckets |
| `host-rw_perf` | `USE_AXI_MONITORS=1` | in-core RDMON/WRMON windows |
| `host-desc_perf` | `USE_AXI_MONITORS=1` | in-core descriptor-fetch window |

On the perf flavor the last two read zero. That is correct behaviour, not a
measurement -- run them against build-mon to cross-check the external observer
against the in-core view of the same traffic.

`csv/` holds INPUT sweep matrices (config columns only) for
`make host-characterize ARGS="--csv csv/<name>.csv"`. They were derived from
the pre-migration RESULT files by dropping the measured columns: those numbers
came off a NexysA7 at 100 MHz, and carrying them into a Genesys 2 tree would
read as data measured here.

A Nexys A7 characterization build is a sibling component under `NexysA7/`
([[area-structure]]), not a `BOARD=` switch inside this one.

## Status

- **build-mon: migrated and verified end to end** -- lint, sim (3 tests),
  bitstream (WNS +1.435 ns vs a +1.426 ns pre-migration baseline), program, and
  the board coverage matrix at 5/6 emittable classes with `UNEXPECTED=0`.
- **build-perf: migrated.** 10 host programs, 39 collected tests, lint clean.
  The `TRANSITIONAL` hook is gone: `stream_char_tb` was the shared UART
  transport all along, so it is now `dv/tbclasses/stream_harness_tb.py` at
  COMPONENT level as `StreamHarnessTB`, imported normally by both builds. No
  file in this area names the pre-migration tree any more.
- **Not yet on silicon.** No bitstream has been built from the restructured
  tree, for either flavor.
- The pre-migration tree still exists and still works; nothing is deleted until
  every flow is green ([[flow-migration]]).

## Host objects

What each object in `bin/` and `build-*/host/` IS, which RTL block it drives and
which layer it belongs to: [[host-objects]]. Read it before adding a host tool
-- the two mistakes it records (hand-rolled read-modify-write, and a runnable
library named `run_*`) were both made here first.

## Related

- [[host-objects]] - the host object catalogue for this area
- [[area-structure]] - board / component / build, and where shared things go
- [[flow-migration]] - how this got here, and the traps
- [[monitor-board-coverage]] - the dense-tally coverage design
- [[testplan]] - the board sequences
- [[host-tools]] - the perf-side runner suite
- [[registers-by-name]] - compose ENABLE by field, never by remembered bit
