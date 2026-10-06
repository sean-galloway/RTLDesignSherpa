# Testing Choices

## Injector modes mapped to failure mechanisms

The shared `error_injector` operates on 8-bit symbols. Mode 1 exact-count
places exactly e errors per block at uniformly random distinct positions,
which is what makes the e = t / e = t + 1 boundary sharp. Mode 2 burst and
mode 3 rate model raw channel bit-error behaviour. Modes 4 clusters and 5
localized model spatially correlated faults. Mode 6 badblock models the tail
of NAND retention. Mode 7 debug is the deterministic bring-up walk.

## Post-encoder injection protects parity symbols

Errors are injected after the encoder, not in the generator. An error in the
generator's data would be encoded faithfully and would be invisible to the code.
Placing the injector on the coded stream means parity symbols are corrupted
too, which is the workload the decoder actually has to handle.

## UART and the safety pair

The harness uses a plain UART instead of a proprietary debug core, so the host
side is just pyserial and Python scripts. Board safety is a pair:
`board_lock.sh` serializes programming flows by JTAG serial, and
`fpga_board.py` reads the JTAG chain before programming to confirm the expected
Genesys 2 serial (`200300B818A0`) is present with a device behind it.

## Genesys 2 vs Nexys A7

The Kintex-7 XC7K325T-2 was chosen because it has room for the full harness
plus observers and still closes timing with positive slack. The Nexys A7-100T
flow is kept as a target option (`RS_TARGET=nexys_a7_100t`) but the Genesys 2
is the primary target for harness-class work.

## AXIS and AXI4 flavors cover both integration styles

The AXIS flavor is a single streaming pipe; the AXI4 flavor replaces the
middle with `rs_axi4_pipeline`, a memory-to-memory job chain over block RAM.
Both use the same generator, checker, CSRs, and verdict logic, so a run reports
itself identically whichever middle is built. Running the same deterministic
campaign on both flavours is a free sanity check. The AXI4 flavor refuses a
`GEN_BLOCKS` value that would exceed the job memories.

## Deliberately not board-tested

The dual-decoder comparator with `ENABLE_COMPARE=1` is the sim/DV domain. The
soak campaign has a default time budget and is scheduled separately. The
component DV matrix exercises the codec in ways the board harness does not
replicate. The erasure `f = 2t` boundary is a known open issue, detailed in the
next section.
