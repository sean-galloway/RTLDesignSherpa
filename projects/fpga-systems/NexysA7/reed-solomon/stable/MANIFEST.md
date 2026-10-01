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

| | cycles/block | dead vs 63 |
|---|---|---|
| bypass (fixture floor) | 59.0 | n/a -- no codec in the path |
| codec, before the pipelining fix | 69.1 | 6.1 |
| codec, now | **65.1** | **2.1** |

The decoder core itself is at ZERO dead cycles, proven in sim across all 8
profiles (slope test, `run_no_dead_cycles`). The 2.1 cycles/block that remain
are therefore OUTSIDE the core -- encoder, beat packer, injector, or the AXIS
wrapper handshakes -- and that is where the next pass goes.

**The utilisation figure cannot read 100% at these tap points, and that is a
measurement bug, not a design one.** Both meters sit on MESSAGE beats (59 per
block) while the codec's internal rate is set by CODEWORD beats (63), so the
arithmetic ceiling is 59/63 = 93.7%. Measured is 90.6%, up from 85.4%. The
input meter's 3.9 cycles/block of backpressure is the n/k expansion itself --
the message side MUST be held off ~4 beats per block while the codeword side
runs full -- and is correct, not a stall. To get a figure that can legitimately
reach 100%, the taps have to move to the codeword side (encoder output and
decoder input); until then read the cycles/block column, not the percentage.

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
