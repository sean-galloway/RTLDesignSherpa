# What Is In It

## RTL blocks

Every path is relative to `projects/fpga-systems/Genesys2/reed-solomon/`
unless it lives in a shared area.

| Module | File | Role |
|---|---|---|
| `uart_axil_bridge` | `projects/components/utility-ip/converters/rtl/uart_to_axil4/uart_axil_bridge.sv` | UART 115200 8N1 to AXI4-Lite master. |
| `bridge_rs_loop_axil` | `rtl/bridges/generated/bridge_rs_loop_axil/bridge_rs_loop_axil.sv` | Generated 1-master x 3-slave AXI4-Lite/APB fabric. |
| `rs_loop_genesys2_top` / `rs_loop_top` | `build-loop/rtl/rs_loop_genesys2_top.sv` / `build-loop/rtl/rs_loop_top.sv` | Board top: Genesys 2 MMCM wrapper, or Nexys A7 100 MHz direct clock. |
| `rs_loop_harness` | `build-loop/rtl/rs_loop_harness.sv` | Codec loop, register decode, bandwidth meters, observers, verdict tallies. |
| `rs_loop_cfg_pkg` | `build-loop/rtl/rs_loop_cfg_pkg.sv` | Single source of geometry: RS(252,236), 4 symbols/beat, shortened so n and k are multiples of the beat. |
| `rs_loop_regs` | Generated from `build-loop/rtl/rs_loop_regs.rdl` via the shared `apb4_to_peakrdl` shim | Host-visible register block: BUILD_ID RSLP, SCRATCH, PROFILE, TOPOLOGY, INJ_CFG, INJ_SEED, etc. |
| `axis4_master_pattern_gen` | `rtl/amba/shared/axis4_master_pattern_gen.sv` | LFSR data source plus expected CRC-32, one packet per block. |
| `axis4_slave_pattern_check` | `rtl/amba/shared/axis4_slave_pattern_check.sv` | Regenerates the same LFSR pattern and compares beats per decoder. |
| `rs_encoder_core` | `projects/components/ecc-ip/reed-solomon/rtl/macro/rs_encoder_core.sv` | RS(252,236) encoder. |
| `error_injector` | `projects/components/utility-ip/misc/rtl/error_injector.sv` | Post-encoder corruption: modes 0 none, 1 exact count, 2 burst, 3 rate, 4 clusters, 5 localized, 6 badblock, 7 debug. |
| `rs_decoder_core` | `projects/components/ecc-ip/reed-solomon/rtl/macro/rs_decoder_core.sv` | Decoder with selectable KES_ALGO and erasure path. |
| `rs_erasure_unit` | `projects/components/ecc-ip/reed-solomon/rtl/fub/rs_erasure_unit.sv` | Erasure locator / transform used when ERASURE_SUPPORT=1. |
| `rs_axi4_pipeline` | `build-loop/rtl/rs_axi4_pipeline.sv` | Memory-to-memory job chain for the AXI4 flavor. |
| `axis4_intf_observer` | `projects/components/utility-ip/misc/rtl/axis4_intf_observer.sv` | Four AXIS seam observer on window 0x20000. |
| `axi4_intf_master_observer` | `projects/components/utility-ip/misc/rtl/axi4_intf_master_observer.sv` | Four codec AXI4 master-port observer on window 0x10000. |

## Host scripts

The host side is layered so the same programs run in cocotb simulation and on
the board.

| Script | File | Role |
|---|---|---|
| `rs_env` | `bin/rs_env.py` | One place this area learns the repo root and puts shared `projects/fpga-systems/bin` plus `build-loop/host` on `sys.path`. |
| `run_smoke.py` | `bin/run_smoke.py` | Campaign runner: resolves sequences, opens the UART, and runs them through `SequenceRunner`. |
| `init` | `bin/seq_init.py` | Proves the link and bitstream: BUILD_ID, SCRATCH round-trip, PROFILE, TOPOLOGY. |
| `smoke` | `bin/seq_smoke.py` | Bypass, clean run, e = t, e = t + 1, deterministic debug walk. |
| `sweep` | `bin/seq_sweep.py` | Exact-count table for e = 0 .. 2t + 2. |
| `random` | `bin/seq_random.py` | Fresh data/error seeds, mixed modes and counts. Also hosts the `clusters`, `localized`, and `badblock` campaign classes. |
| `soak` | `bin/seq_soak.py` | Million-block random soak, run by run, with replayable seeds. |
| `erasure` | `bin/seq_erasure.py` | Marked runs at f = t, 2t, 2t + 1. |
| `RsLoopDriver` | `build-loop/host/rs_loop.py` | By-name register access, status, bandwidth meters, observer readout. |
| `rs_loop_programs` | `build-loop/host/rs_loop_programs.py` | The authored-once programs shared by sim and board: `smoke`, `bypass`, `run`, `sweep`, `verdict`. |
| `host_rs_loop.py` | `build-loop/host/host_rs_loop.py` | CLI front-end: smoke, bypass, run, sweep, random, bw, obs, soak, erasure. |

## Build and validation flow

| Target / artifact | File | Role |
|---|---|---|
| Top-level dispatcher | `Makefile` | Delegates to `build-loop/Makefile` for `bitstream`, `lint`, `sim`, etc.; `make regmap` regenerates CSRs. |
| Per-build flow | `build-loop/Makefile` | Vivado project, constraints, and report handling; consumes `make/fpga_flow.mk`. |
| Four-image matrix | `bin/build_image_matrix.sh` | Builds `{axis,axi4}` x `{riBM,Euclid}` with one solver per bitstream. |
| Bandwidth matrix | `bin/measure_image_matrix.sh` | Programs and measures each image in turn. |
| Genesys 2 constraints | `build-loop/fpga/constraints/rs_loop_genesys2.xdc` | 200 MHz LVDS input, MMCM, UART pins, LEDs. |
| Validation record | `stable/MANIFEST.md` | Timing slack, board campaigns, and known issues for the kept images. |
