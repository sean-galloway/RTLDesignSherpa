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
| Routed WNS | +0.251 ns | +0.064 ns | +0.322 ns | +0.301 ns |
| Failing endpoints | 0 | 0 | 0 | 0 |
| Slice LUTs | 11,128 | 13,429 | 12,991 | 15,137 |
| Block RAM tiles | 0 | 0 | 16 | 16 |

All four carry FOUR bandwidth meters (the two codeword-seam ones added +415
LUTs on axis_ribm). The earlier round's axis_ribm read +0.011 ns with the
error injector as its critical path; the same RTL plus two meters now reads
+0.251 ns, which settles that as placement variance rather than a real path.

Per-image reports and bitstreams are in `reports/<image>/`, with
`reports/matrix_summary.txt` carrying the table above.

## Measured throughput (axis_ribm, RS(252,236) S=4)

59 message beats and 4 parity beats per block -- the encoder starts parity on
a FRESH beat -- so a codeword is 63 beats and 63 cycles/block is line rate.

**The codeword seams run at 100.0%.** Measured as a slope over 64 -> 256
blocks, which cancels the pipeline fill:

| seam | beats / cycles | utilisation | cyc/block | ideal |
|---|---|---|---|---|
| codeword out of encoder | 12,096 / 12,096 | **100.0%** | 63.00 | 63 |
| codeword into decoder | 12,096 / 12,096 | **100.0%** | 63.00 | 63 |
| message in | 11,328 / 12,096 | 93.7% | 63.00 | 59 |
| message out | 11,328 / 12,096 | 93.7% | 63.00 | 59 |

Zero backpressure and zero starvation on both codeword seams in the
differenced window: not one dead cycle. `host_rs_loop.py bw --blocks 256
--slope` reproduces it.

**The message side's 93.7% is the CODE RATE, not a stall.** k/n = 236/252 =
93.651%, and the measurement is 11328/12096 = 93.651%. It agrees to the digit
because the message side carries k beats per block while the cycles are set by
the codeword's n. There is nothing to recover there: the shortfall IS the
parity. If RS sits in a memory path, host-side bandwidth is k/n of the
media-side bandwidth, and that is the cost of the ECC rather than a limit the
implementation imposes.

This is why the codeword meters were added. The message-side taps were the
only ones present before, so the best reading the harness could produce was
93.7%, which looks like a 6% shortfall and is not one.

**Read a SLOPE, never a total divided by a block count.** Single-run totals
on this same hardware:

| blocks | cycles | cycles - 63*blocks | total/blocks |
|---|---|---|---|
| 16 | 1,144 | 136 | 71.5 |
| 32 | 2,152 | 136 | 67.2 |
| 64 | 4,168 | 136 | 65.1 |
| 128 | 8,200 | 136 | 64.1 |
| 256 | 16,264 | 136 | 63.5 |

Every adjacent pair gives 63.00 cycles/block; the excess is one fixed
136-cycle fill, and the codeword meters report exactly that as 136 cycles of
starvation in an absolute window. An earlier revision of this file read the
64-block value, 65.1, as "2.1 dead cycles per block" and went looking for them
in the encoder, beat packer and injector. There were none: the shared
generator, checker and bus meter were never at fault, which the stream project
saturating those same blocks should have said immediately. See
vault/handbook/design/block-boundary-dead-cycles.md.

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
