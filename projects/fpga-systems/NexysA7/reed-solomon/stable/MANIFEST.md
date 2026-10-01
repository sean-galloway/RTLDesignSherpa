# Nexys A7 Reed-Solomon loop harness -- last stable build

**One slot. Overwrite it; do not accumulate versions.**

`make keep` in a build directory copies that build's bitstream to the HOLD dir
outside the repo (`$RDS_HOLD_DIR/<board>/<flow>/`) and its reports here. The
RTL is NOT copied: a bitstream whose source you cannot reconstruct is only
useful as "the last thing known to work on the board." `stable/` is a sibling
of the build-* dirs, outside the blast radius of `make clean-all`.

## Current contents

**FOUR images now, from one harness RTL** -- datapath x solver, built by
`bin/build_image_matrix.sh` on 2026-10-01. One solver per bitstream, never
both: two solvers double the key-equation area and the comparator changes the
very handshake the meters measure. All four close with ZERO failing endpoints.

| | axis_ribm | axis_euclid | axi4_ribm | axi4_euclid |
|---|---|---|---|---|
| Routed WNS | +0.011 ns | +0.090 ns | +0.198 ns | +0.272 ns |
| Failing endpoints | 0 | 0 | 0 | 0 |
| Slice LUTs | 10,713 | 13,066 | 12,522 | 14,681 |
| Block RAM tiles | 0 | 0 | 16 | 16 |
| Critical path in | error injector | Euclid degree reg | AXI4 R channel | Euclid degree reg |

Per-image reports and bitstreams are in `reports/<image>/`, with
`reports/matrix_summary.txt` carrying the table above.

**axis_ribm's +0.011 ns is thin, and it is NOT the codec.** Its critical path
is the error injector's DSP48E1 into a 7-deep CARRY4 chain -- test fixture,
not Reed-Solomon. The decoder and solver appear twice in the whole timing
summary and in none of the top paths. The other three images all IMPROVED over
the previous round (+0.085 -> +0.090, +0.155 -> +0.198, +0.234 -> +0.272) on
the same RTL change, which is the evidence that the change is timing-neutral:
a new critical path would have hit all four, in the decoder.

## Measured throughput (axis_ribm, RS(252,236) S=4)

The profile is 59 message beats and 4 parity beats per block -- the encoder
starts parity on a FRESH beat -- so a codeword is 63 beats and 63 cycles/block
is line rate.

**The board runs at exactly line rate: ZERO dead cycles per block.** Measured
at four block counts, the total is a straight line with a constant intercept:

| blocks | cycles | cycles - 63*blocks | single-point cycles/block |
|---|---|---|---|
| 16 | 1,144 | 136 | 71.5 |
| 32 | 2,152 | 136 | 67.2 |
| 64 | 4,168 | 136 | 65.1 |
| 128 | 8,200 | 136 | 64.1 |
| 256 | 16,264 | 136 | 63.5 |

Every adjacent pair gives a slope of **63.00 cycles/block**, and the whole
excess is one fixed 136-cycle pipeline fill and drain. The meters say the same
thing independently: STARVATION -- actual dead time -- is a constant 140
cycles at 64, 128 and 256 blocks, while BACKPRESSURE scales at 3.98/block.
That backpressure is the n/k expansion doing its job, holding the message side
off while the codeword side runs full: 59 productive + 3.98 held off = 63.

**DIVIDE THE TOTAL BY THE BLOCK COUNT AND YOU GET A NUMBER THAT IS NOT A
RATE.** The "single-point cycles/block" column above is `63 + 136/blocks`; it
reads 71.5 at 16 blocks and 63.5 at 256 for the SAME hardware behaving
identically. An earlier revision of this file reported the 64-block value,
65.1, as "2.1 dead cycles per block" and went looking for them in the
encoder, the beat packer and the injector. There were none to find: the
fixtures were never at fault, which the stream project hitting line rate on
the same shared generator, checker and meter should have said immediately.
Take a slope over two block counts. See
vault/handbook/design/block-boundary-dead-cycles.md, which says exactly this
and was written before the mistake was made.

**The utilisation PERCENTAGE still cannot reach 100% at these tap points, and
that part is real.** Both meters sit on MESSAGE beats (59 per block) while the
cycles are set by CODEWORD beats (63), so the arithmetic ceiling is
59/63 = 93.7%. Measured: 90.6% at 64 blocks, 92.1% at 128, 92.9% at 256 --
converging on the ceiling exactly as a fixed fill amortises away. To get a
figure that can legitimately read 100%, the taps have to move to the codeword
side (encoder output and decoder input).

## Build notes

- **All four images are built with `RS_IMPL_EFFORT=explore`.** At default
  effort the stream flavour was -0.303 ns with 2 failing endpoints; the
  binding path is route-dominated, so effort is what closes it, not logic.

- **`set_property strategy` is accepted WITHOUT a warning and silently does
  not stick** -- the project still recorded "Vivado Implementation Defaults"
  and the result was bit-identical. The build sets the STEP DIRECTIVES
  explicitly and reads them back as an `IMPL CHECK:` line, which is the only
  reason the explore setting can be trusted. Check for that line in the log.

## Board validation

- **Stream flavour (Nexys A7 210292BFA3EE, /dev/ttyUSB5):**
  init / smoke / sweep all pass over e = 0 .. 2t+2; the random campaign 64 of
  64; and the soak **1,003,520 blocks in 137 s (7,315 blk/s), 0 failing runs**
  -- 102,542 clean / 760,540 corrected / 140,438 uncorrectable, 3,242,499
  symbols corrected, and **59,207,680 beats compared riBM vs Euclid with zero
  mismatches**. Beyond the correction limit, 2 of 77,824 blocks were accepted
  and silently mis-decoded, 1 in 38,912, against the model's ~1 in 20,000.

- **AXI4 flavour:** init / smoke / sweep pass, the random
  campaign 64 of 64, and a soak of **100,032 blocks in 875 s, 0 failing runs**
  (12,343 clean / 75,426 corrected / 12,263 uncorrectable, 307,676 symbols
  corrected). Clean runs read 16/16 ok, e = t reads 16 corrected, e = t+1 reads
  16 uncorrectable. The comparator is absent by construction, so the beats-
  compared figure is 0 and the B-side counters read 0 by design -- the host
  learns that from TOPOLOGY rather than being told.

- **Why the AXI4 soak is 100k and not a million.** Throughput is 114 blk/s
  against the stream path's 7,315, because the AXI4 datapath is five
  sequential jobs per kick and each memory holds only
  `CFG_AXI4_MEM_DEPTH / CFG_N_BEATS` = 65 blocks, so the per-kick UART cost
  dominates. A million blocks would be ~15,400 kicks and about two hours.
  Raising `CFG_AXI4_MEM_DEPTH` fourfold lifts the cap to 260 blocks and costs
  64 block RAM tiles of 135, which would bring a million blocks to roughly half
  an hour. Not done, because it invalidates the bitstream above.

- **Revalidated on the pipelined RTL (2026-10-01, axis_ribm):** init passes,
  and the random campaign is 64 of 64 runs x 4 blocks with **0 failing runs**
  -- 24 clean / 125 corrected / 107 uncorrectable. The soak figures above
  predate the pipelining change and have not been re-run at a million blocks.

- **Caveat (both flavours):** the shared checker's CRC is over its regenerated
  words, so `crc_ok` is a delivery check; `data_err` is the data evidence.
