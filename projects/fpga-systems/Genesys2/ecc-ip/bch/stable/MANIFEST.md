# Nexys A7 BCH loop harness -- last stable build

**One slot. Overwrite it; do not accumulate versions.**

`make keep` in a build directory copies that build's bitstream to the HOLD dir
outside the repo (`$RDS_HOLD_DIR/<board>/<flow>/`) and its reports here. The
RTL is NOT copied: a bitstream whose source you cannot reconstruct is only
useful as "the last thing known to work on the board." `stable/` is a sibling
of the build-* dirs, outside the blast radius of `make clean-all`.

## Current contents

**Genesys 2 images, built and validated on the board 2026-10-04.**
`BCH_TARGET=genesys2 ./bin/build_image_matrix.sh`; both images timing-clean
(zero failing endpoints at 100 MHz on the k325t-2):

| image | WNS (ns) | LUTs | board validation |
|---|---|---|---|
| genesys2_axis | +0.586 | 39,953 | full battery green |
| genesys2_axi4 | +0.493 | 47,490 | full battery green |

**Board validation (Genesys 2, 2026-10-04):** init, smoke (bypass / clean /
e=t / e=t+1 / deterministic DEBUG walk, 16 blocks with exactly 1 error
each), sweep (19/19 counts: exact correction counts e <= 8, all
uncorrectable e = 9..18, byte CRCs clean), random (64 runs x 16 blocks, 0
failures), and the three application campaigns — clusters, localized,
badblock — all PASS on BOTH images.

Bugs the board paces found and fixed (all in the shared
`utility-ip/misc` `error_injector` or the harness wiring): the AXI4
pipeline's 2-bit `inj_mode` port truncated modes 4-7 to mode 3 (the
3-bit mode field from the regenerated register block was silently
dropped); the draw's fixed-count default (`cnt_min == cnt_max` fell
through to N = table size — no sim exercised equal ranges); the mode-5
window start consumed the cluster-gated table width instead of the
ungated `r_loc_wid`; plus the campaign `data_err` expectation corrected
(residual-only signal).

One harness fact the soak surfaced: the AXI4 flavour **refuses runs whose
GEN_BLOCKS exceed its job memories** (16-block runs are fine; 64 is
already refused -- it declines rather than let the regions wrap). Long
soaks belong on the AXIS image, which streams and accepted 4096-block
runs; the default-time soak passed 12,288 mixed-mode blocks there with
zero silent mis-decodes.

The A7 images below remain for the small board; they are NOT timing-clean
(see the integration history) and the A7 is no longer the target for
harness-class work:

| image | datapath | decoder | notes |
|---|---|---|---|
| axis | AXIS | RIBM | stream pipe, 100 MHz |
| axi4 | AXI4 | RIBM | memory-to-memory job chain |

Both images share a single RIBM decoder and carry no comparator. The host reads
TOPOLOGY to discover the datapath; the solver field reads RIBM (kes_a = 0).

When `bin/build_image_matrix.sh` is run, per-image reports and bitstreams land
in `reports/<image>/` and `reports/matrix_summary.txt` carries the summary to
paste into this file.

**Board target switch.** Set `BCH_TARGET=genesys2` to build for the Digilent
Genesys 2 (xc7k325tffg900-2) instead of the default Nexys A7-100T; the wrapper
derives 100 MHz from the 200 MHz LVDS system clock and everything downstream
is unchanged. The default `nexys_a7_100t` keeps the original image names and
report layout byte-identical.
