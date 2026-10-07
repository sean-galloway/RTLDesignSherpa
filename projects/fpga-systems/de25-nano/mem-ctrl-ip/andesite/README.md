# andesite on the DE25-Nano (build area)

The DE25-Nano (Intel, LPDDR4) is the destination board for andesite. It is
not in hand yet, so this area's **initial build targets the Genesys 2**
(Kintex-7, Vivado): same controller, silicon-grade toolchain, real
placement-and-routed timing — the build and timing issues get worked out
early instead of on first silicon.

## The build (`build-andesite/`)

A skeleton by design, modelled on `Genesys2/scoria/build-scoria/`:

- `rtl/andesite_char_top.sv` — Genesys 2 clocks (200 MHz LVDS osc → MMCM →
  100 MHz), button reset, `andesite_core` with the DFI 4.0 pins terminating
  at an observability XOR tree, and an on-chip AXI exerciser
  (`rtl/andesite_exerciser.sv`) that starts after init and loops write/read
  bursts across the bank stride. **No PHY** — the K7 DDR3 PHY cannot serve
  a DDR4/LPDDR4 controller, and the real board's PHY strategy is
  EMIF-first (Intel), per the ruling in the andesite TASK-016 ledger. The
  XOR tree is the keep-alive net and the exerciser makes it toggle for
  real: an idle build const-folds the write-data/CDC/read-return cones
  down to the init/refresh command path only, and its timing report would
  describe a core that is not there.
- LED map: heartbeat · `init_done` · `init_err` · DFI keep-alive ·
  `zq_busy` · `dfi_reset_n` · `dfi_init_start` · exerciser busy.
- Timings programmed for the 100 MHz sys clock (prog = ceil(ns/10ns) − 1
  from the DDR4-1600J ns figures; same derivation discipline as
  `dv/tbclasses/andesite_dram_configs.py`). Whether the core closes at
  100 MHz on Kintex-7 **is** the experiment — scoria missed it by 1.26 ns
  and dropped to 80 (scoria BUG-003). Answer from the first build: it
  closes — WNS +3.22 ns, WHS +0.06 ns; ~3.2k LUTs / ~2.9k regs (0.7% of
  the K325T). Known constant-folds at this config (documented, not bugs):
  `page_policy` degenerates with OPEN policy tied, and `mode_register`
  folds with constant MR images and no runtime MRS traffic.

## Use

```
make bitstream        # Vivado synth/impl/bitgen, BOARD=genesys2
make lint             # Verilator, Xilinx stubs substituted
make program          # flash the Genesys 2
```

`BOARD` rides the shared registry (`projects/fpga-systems/bin/boards/`);
first silicon on the DE25-Nano is a `BOARD=` switch plus its constraints
and PHY work, not a new flow.

## Deliberately not here yet

Host UART/sequence scaffolding, the LiteDRAM-style yardstick, any DRAM
PHY, and constraints for the DE25-Nano itself. Each lands when there is
something for it to do.
