# The FPGA-Testing Choices, And Why

## The dual-solver loop as mutual oracle

The AXIS datapath feeds the same corrupted blocks to two `rs_decoder_core`
instances, one with `KES_ALGO=RIBM` and one with `KES_ALGO=EUCLID`. Each
decoder's output is compared beat-by-beat against the generator's regenerated
LFSR pattern in its own `axis4_slave_pattern_check`, so a correction is
judged by a reference that never saw the errors — not by the other decoder. A
separate comparator then requires the two decoders to agree on every beat and
on every block's verdict. That makes a solver bug visible as a disagreement
even when both decoders "correct." On the board images this comparator is
present only in simulation (`ENABLE_COMPARE=1`); the production board matrix
carries one solver per bitstream to save area and keep the handshake clean
for the bandwidth meters. The cross-solver check then happens by running the
identical deterministic campaign on the riBM and Euclid images and requiring
matching numbers.

## Determinism makes the riBM and Euclid images cross-oracles

The host-side RNG seed defaults to 1. With that default, the random, soak,
clusters, localized, and badblock campaigns are fully deterministic: the riBM
and Euclid images run bit-identical workloads. On the 2026-10-05 Genesys 2
battery all four single-decoder images passed 7/7 campaigns, and the matching
verdict counts between riBM and Euclid are themselves the cross-check. You do
not need the on-chip comparator to know the two solvers agree — the campaigns
prove it.

## Injector modes map to real failure mechanisms

The shared `error_injector` operates on 8-bit symbols, because that is RS's
natural unit. Mode 1 exact-count places exactly e errors per block at
uniformly random distinct positions, which is what makes the e = t /
e = t + 1 boundary sharp. Mode 2 burst and mode 3 rate model raw channel
bit-error behavior. Modes 4 clusters and 5 localized model spatially
correlated faults — a bad DRAM row, a disturbed NAND page, or a failed symbol
column. Mode 6 badblock models the tail of NAND retention: most blocks clean,
a hard minority very bad. Mode 7 debug is the deterministic bring-up walk.
When `INJ_CFG.mark` is set, the injector's hit mask rides the decoder
`in_erasure` sideband, turning any of these placement modes into an erasure
run where the decoder is told which symbols were corrupted.

## Post-encoder injection protects parity symbols

Errors are injected after the encoder, not in the generator. An error in the
generator's data would be encoded faithfully and would be invisible to the
code. Placing the injector on the coded stream means parity symbols are
corrupted too, which is the workload the decoder actually has to handle. That
is why the generator has no error-injection mode and the injector is a
separate block.

## UART over a debug core, with a lock/readback safety pair

The harness uses a plain UART instead of a proprietary debug core, so the
host side is just pyserial and Python scripts. Board safety is a pair:
`board_lock.sh` serializes programming flows by the board's JTAG serial, and
`fpga_board.py` reads the JTAG chain through `jtag_readback.tcl` before
programming to confirm the expected Genesys 2 serial (`200300B818A0`) is
present with a device behind it. A lock prevents collisions; a readback
detects misattribution. When the hw_server deviceless-enumeration race
refused about half of programming attempts, the readback path was changed to
bounce hw_server and retry, bounded at five. The verdict is recorded beside
the bitstream sha256 so a result file cannot be mistaken for verified if the
identity check was inconclusive.

## Genesys 2 over Nexys A7

The Kintex-7 XC7K325T-2 was chosen because it has room for the full harness
plus observers and still closes timing with positive slack. The four Genesys
2 images routed with WNS from +0.875 ns to +1.822 ns. The Nexys A7-100T flow
is kept as a target option (`RS_TARGET=nexys_a7_100t`) and the original image
names and report layout stay byte-identical, but the Genesys 2 is the primary
target for harness-class work.

## AXIS and AXI4 flavors cover both integration styles

The AXIS flavor is a single streaming pipe: generator, encoder, injector,
decoder, checker. The AXI4 flavor replaces the middle with `rs_axi4_pipeline`,
a memory-to-memory job chain over block RAM. Both use the same generator,
checker, CSRs, and verdict logic, so a run reports itself identically
whichever middle is built. The AXI4 flavor refuses a `GEN_BLOCKS` value that
would exceed the job memories — it declines rather than clamps, because
clamping would answer a question the host did not ask. Running the same
deterministic campaign on both flavors is a free sanity check: at e = 8 the
AXI4 flavor takes 381.0 cycles/block against 199.2 on AXIS. The two numbers
must be consistent for the same workload, and they are. The million-block
soak ran on `axi4_ribm`; an earlier plan to prefer AXIS for soaks proved
unnecessary.
