# Nexys A7 Reed-Solomon loop harness -- last stable build

**One slot. Overwrite it; do not accumulate versions.**

`make keep` in a build directory copies that build's bitstream to the HOLD dir
outside the repo (`$RDS_HOLD_DIR/<board>/<flow>/`) and its reports here. The
RTL is NOT copied: a bitstream whose source you cannot reconstruct is only
useful as "the last thing known to work on the board." `stable/` is a sibling
of the build-* dirs, outside the blast radius of `make clean-all`.

## Current contents

**TWO flavours now, from one harness RTL.** `IFACE` selects the datapath and
`RS_IMPL_EFFORT` / `RS_ENABLE_COMPARE` the rest; both were built and validated
on 2026-09-30 and both close timing with zero failing endpoints.

| | stream (`IFACE=AXIS`) | AXI4 (`IFACE=AXI4`) |
|---|---|---|
| Routed WNS | +0.288 ns | +0.577 ns |
| Failing endpoints | 0 | 0 |
| Slice LUTs | 18,753 (29.6%) | 12,046 (19.0%) |
| Block RAM tiles | 0 | 16 (11.9%) |
| Decoders | riBM + Euclid, comparator on | riBM only |
| Build command | `RS_IMPL_EFFORT=explore make bitstream` | `RS_IFACE=AXI4 RS_ENABLE_COMPARE=0 make bitstream` |

- **HOLD file:** `/mnt/data/fpga-hold/nexys_a7_100t/rs_loop/rs_loop.bit` holds
  whichever flavour `make keep` last ran on. The reports beside this file
  likewise describe one build, so check the WNS against the table above to see
  which.

- **The stream flavour needs `RS_IMPL_EFFORT=explore`.** At default effort it
  is **-0.303 ns with 2 failing endpoints**. The critical path is the Euclid
  solver's degree register into the descriptor broadcast: 10 logic levels, 78%
  of its delay in routing, and it had only 2.7% margin before. Putting the
  component's AXIS wrappers in the harness added 495 LUTs of skid buffers, and
  at 29.6% occupancy that congestion alone was enough. The path did not get
  longer; it got routed worse. If that dependency is unwanted, dropping decoder
  B returns 7,163 LUTs and the solver-equivalence question it answers has been
  settled by a million blocks.

  A trap worth knowing: `set_property strategy` was accepted WITHOUT a warning
  and silently did not stick -- the project still recorded "Vivado
  Implementation Defaults" and the result was bit-identical. The build now sets
  the STEP DIRECTIVES explicitly and reads them back into the log.

- **Board validation, stream flavour (Nexys A7 210292BFA3EE, /dev/ttyUSB5):**
  init / smoke / sweep all pass over e = 0 .. 2t+2; the random campaign 64 of
  64; and the soak **1,003,520 blocks in 137 s (7,315 blk/s), 0 failing runs**
  -- 102,542 clean / 760,540 corrected / 140,438 uncorrectable, 3,242,499
  symbols corrected, and **59,207,680 beats compared riBM vs Euclid with zero
  mismatches**. Beyond the correction limit, 2 of 77,824 blocks were accepted
  and silently mis-decoded, 1 in 38,912, against the model's ~1 in 20,000.

- **Board validation, AXI4 flavour:** init / smoke / sweep pass, the random
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

- **Caveat (both flavours):** the shared checker's CRC is over its regenerated
  words, so `crc_ok` is a delivery check; `data_err` is the data evidence.
