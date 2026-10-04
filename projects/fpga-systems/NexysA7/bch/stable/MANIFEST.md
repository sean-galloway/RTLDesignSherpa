# Nexys A7 BCH loop harness -- last stable build

**One slot. Overwrite it; do not accumulate versions.**

`make keep` in a build directory copies that build's bitstream to the HOLD dir
outside the repo (`$RDS_HOLD_DIR/<board>/<flow>/`) and its reports here. The
RTL is NOT copied: a bitstream whose source you cannot reconstruct is only
useful as "the last thing known to work on the board." `stable/` is a sibling
of the build-* dirs, outside the blast radius of `make clean-all`.

## Current contents

**No stable build yet.** The harness RTL is complete and the cosim smoke test
passes; the two planned images are:

| image | datapath | decoder | notes |
|---|---|---|---|
| axis | AXIS | RIBM | stream pipe, 100 MHz |
| axi4 | AXI4 | RIBM | memory-to-memory job chain |

Both images share a single RIBM decoder and carry no comparator. The host reads
TOPOLOGY to discover the datapath; the solver field reads RIBM (kes_a = 0).

When `bin/build_image_matrix.sh` is run, per-image reports and bitstreams land
in `reports/<image>/` and `reports/matrix_summary.txt` carries the summary to
paste into this file.
