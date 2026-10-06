# The FPGA-Testing Choices, And Why

## Deterministic campaigns

Every board campaign is deterministic: the default `gen_seed` and `inj_seed`
are 1, and the sequences in `bin/seq_*.py` produce the same bit-exact runs in
cocotb simulation and on the board. That matters because a failure you can
replay is a failure you can fix; a non-deterministic board-only failure is
just a scary story. `seq_random.py` still varies its draws, but those draws
come from a host-side `random.Random(seed)` seeded by the caller, so the
variation is reproducible when you need it.

## Injector modes mapped to real failure mechanisms

The shared `error_injector` exposes eight modes, and each one answers a
different physical question. Exact-count mode proves the correction boundary:
at `e <= t` every block must correct with exactly `e` bits flipped, and at
`e > t` the decoder must flag uncorrectable. Burst and rate modes model raw
bit-error behaviour on a noisy channel. Clusters and localized mode stand in
for spatially correlated faults — a bad DRAM row, a disturbed NAND page, a
half-plane failure — because real errors are rarely uniform. Badblock mode
models retention tails and worn blocks: most of the stream stays clean while
a hard minority runs at a much higher error rate. Debug mode is the bring-up
helper, a deterministic walking pattern that closes by inspection.

## Post-encoder injection protecting parity bits too

The injector sits after the encoder, not inside the generator. That is not an
accident: an error in the generator data would be encoded faithfully and the
code would never see it. By corrupting the codeword, the parity bits are
exposed to the same errors as the data, which is what happens when a real
packet is stored, transmitted, or read back from memory. The
`bch_loop_harness.sv` header comment calls this out explicitly, and the
layout follows from it.

## Recheck + flip-only verdict as the on-chip oracle

The BCH decoder uses riBM with odd-syndrome computation and even syndromes by
squaring. It runs a second-syndrome recheck (`ENABLE_RECHECK`) and performs
flip-only correction — there is no Forney, because binary values are always
1. The checker independently regenerates the expected stream and reports
`data_err` on any mismatched beat. Together they form the on-chip oracle: the
decoder decides whether it thinks it corrected the block, and the checker
decides whether the recovered bytes actually match the reference.

## UART over a debug core, plus the safety pair

The host link is a plain UART at 115200 baud, driven by `uart_axil_bridge`.
That choice keeps the harness scriptable from Python without a debug core
licence and without vendor-specific probes. But scriptable does not mean
careless. Two pieces of shared tooling guard the board:
`projects/fpga-systems/bin/board_lock.sh` serializes programming flows by
JTAG serial, and `projects/fpga-systems/bin/fpga_board.py` refuses to program
until a JTAG readback confirms the expected Genesys 2 serial `200300B818A0`
on the chain with a device behind it. The readback also bounces `hw_server`
and retries up to five times on the deviceless-enumeration race that otherwise
refused roughly half of programming attempts when a second Digilent board
shared the chain.

## AXIS vs AXI4 flavours covering both integration styles

Two bitstreams are built and both are exercised. The AXIS flavour is a single
streaming pipe; the AXI4 flavour is a memory-to-memory job chain. The AXI4
flavour refuses runs whose `GEN_BLOCKS` exceed the job-memory capacity rather
than letting regions wrap, so long soaks belong on the AXIS image. The host
reads `TOPOLOGY` to discover which datapath is loaded, so the same campaign
scripts drive both without a command-line flag.
