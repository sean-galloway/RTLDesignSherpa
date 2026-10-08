# TASK-007: BCH Nexys A7 board loop bring-up

**Status:** closed 2026-10-08 — bring-up complete and recorded. The
`projects/fpga-systems/Genesys2/ecc-ip/bch/` tree mirrors the RS area
(bin/sequences, generated 1x3 AXIL fabric with PREBUILD drift check,
PeakRDL `bch_loop_regs`, AXIS loop + AXI4 job chain, host driver +
programs, UART cosim running the same programs unmodified); Genesys 2
images were built and validated on the board 2026-10-04 (full battery on
both images, `stable/MANIFEST.md`); the A7 small images were built and
re-run post-#89 (battery 7/7 + 62,528-block soak). Re-verified at close-out:
PREBUILD drift check green (2026-10-08), full 14-test UART harness suite
small profile re-run 2026-10-08 (both IFACE values; suite result recorded
in the closing commit).
**Priority:** P3
**Owner:** TBD

With the wrappers landed (TASK-006), this task builds the board harness that
mirrors `projects/fpga-systems/NexysA7/reed-solomon/`: generated 1x3 AXIL
fabric, `bch_loop_regs` (PeakRDL), AXIS stream loop plus AXI4
memory-to-memory pipeline, host driver + sequence programs, UART cosim
running the same programs unmodified, both bitstreams, and programmed-board
evidence in `stable/MANIFEST.md`. Board profile: BCH(4224,4120) t=8 m=13
b=1, BITS_PER_BEAT=32 (n whole 32-bit beats; k byte-aligned partial beat).

## Scope

- `projects/fpga-systems/Genesys2/ecc-ip/bch/` tree mirroring the RS area:
  `bin/` (sequences, regen_bridges.sh, build_image_matrix.sh, run_smoke.py),
  `rtl/bridges/` (generated fabric + PREBUILD drift check),
  `build-loop/` (cfg pkg, RDL, harness, AXI4 pipeline, top, host driver +
  programs, cosim dv, fpga constraints), `stable/MANIFEST.md`.
- Register map mirrors `rs_loop_regs.rdl` with BCH names/fields
  (BUILD_ID "BCHP", injector stats in BITS, single-decoder counters,
  AXI4 status); by-name access only, no hardcoded offsets outside the
  generated regmap.
- Cosim: real `uart_axil_bridge` + harness, host programs unmodified,
  tests mirroring RS (bypass/clean/correct e=t/over_t e=t+1/throttle/skew/
  sequences/random/soak/AXI4 variants).
- Both bitstreams (AXIS, AXI4) with WNS > 0; program the attached Nexys A7;
  smoke/sweep/soak per image; MANIFEST matrix.

## Definition of done

- `make sim` green (both IFACE values); `make bitstream` green for both
  images; PREBUILD drift check passes.
- Board runs: correction at e=0..8, flagging at e>8, soak counts, block
  rate, WNS/LUT/BRAM recorded in `stable/MANIFEST.md`.
- `bin/filelists.toml` registers the board area; task checks pass;
  `bch/CLAUDE.md` carries the board facts.

## Log

**2026-10-03 -- filed**, as TASK-006 was activated.

**2026-10-08 -- closed.** Every definition-of-done item holds: both bitstreams
timing-clean (G2 matrix in `stable/MANIFEST.md`; A7 small images rebuilt
post-#89), board runs recorded (G2 2026-10-04 full battery; A7 battery 7/7 +
soak), `bin/filelists.toml` registers the area, `bch/CLAUDE.md` carries the
board facts, PREBUILD drift check green, and the 14-test UART harness suite
(small profile, both IFACE values) re-run at close-out.
