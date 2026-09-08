# Nexys A7 CDC counter display -- last stable build

**One slot. Overwrite it; do not accumulate versions.**

`make keep` in a build directory copies that build's bitstream to the HOLD dir
outside the repo (`$RDS_HOLD_DIR/<board>/<flow>/`) and its reports here. The
RTL is NOT copied: a bitstream whose source you cannot reconstruct is only
useful as "the last thing known to work on the board." When a new build
supersedes this, replace every file here in one go and rewrite this manifest.

This exists because `make clean-all` in a build directory deletes everything
under `fpga/bitstream` and `fpga/reports` -- correct behaviour for a build
directory, and why nothing worth keeping may live there. `stable/` is a
sibling of the build-* dirs, outside that blast radius.

## Current contents

- **Build:** build-demo (cdc_demo_top), kept 2026-09-08 from the fpga_flow.mk
  migration -- the first bitstream of the v3 MMCM/BUFGMUX top (4-mux tree,
  cascade-route overrides, display pins false-pathed).
- **HOLD file:** `/mnt/data/fpga-hold/nexys_a7_100t/cdc_demo/cdc_demo.bit`
- **Timing:** MET, WNS +3.223 ns, 0 failing endpoints (reports/ beside this file).
- **Board validation (Nexys A7 210292BFA3EE):** smoke (BUILD_ID + SCRATCH +
  defaults), press 50x exact, cfg-load, cdc-mode round-trip, watch-fail sweep
  5.96 Hz - 50 MHz, and all four MMCM mux inputs measured at 72.96 / 27.73 /
  11.99 / 6.27 MHz via CTR_CLK_TICKS.
