# Nexys A7 Reed-Solomon loop harness -- last stable build

**One slot. Overwrite it; do not accumulate versions.**

`make keep` in a build directory copies that build's bitstream to the HOLD dir
outside the repo (`$RDS_HOLD_DIR/<board>/<flow>/`) and its reports here. The
RTL is NOT copied: a bitstream whose source you cannot reconstruct is only
useful as "the last thing known to work on the board." `stable/` is a sibling
of the build-* dirs, outside the blast radius of `make clean-all`.

## Current contents

- **Build:** build-loop (rs_loop_top), kept 2026-09-30, the fabric version
  with the dedicated GO kick register and the comparator backpressure fix:
  `uart_axil_bridge` -> generated 1x3 `bridge_rs_loop_axil` -> the loop's
  register block on the APB window through `apb4_to_peakrdl`, with the
  rs_regs and observer windows reserved and tied off. RS(252,236) over
  GF(2^8), t = 8, 4 symbols per beat; decoder A riBM, decoder B Euclid.
- **HOLD file:** `/mnt/data/fpga-hold/nexys_a7_100t/rs_loop/rs_loop.bit`
- **Timing:** MET after place and route at 100 MHz, WNS +0.269 ns, WHS
  +0.017 ns, 0 failing endpoints of 30193. The critical path is the Euclid
  solver's output un-shift into the solve-to-correct descriptor, 10 logic
  levels.
- **Utilization (impl):** 18258 LUTs, 8163 flops, 6 DSPs, 0 BRAM. Full report
  in reports/utilization_impl.txt beside this file.
- **What changed from the previous slot.** Two harness bugs, both found by
  randomizing the two checkers' ready throttles INDEPENDENTLY, which no
  earlier test did:
  1. The comparator's two FIFOs ignored their write ready, so a skewed drain
     overflowed one, beats were dropped, and the comparator then compared
     misaligned streams -- reporting ~690 of 700 beats as riBM-vs-Euclid
     mismatches between decoders that agreed completely. 30 of 64 random runs
     failed this way. The FIFO ready is now part of the decoder's drain
     condition, and a sticky STATUS.cmp_misaligned flag invalidates the
     mismatch counts if the two streams ever fail to run out together.
  2. Gating only the decoder's ready let each checker complete its own
     handshake while the decoder was held back, so it consumed the same beat
     twice -- 6 packets counted for 4 blocks. The checker's TVALID is now
     gated on the comparator's ready as well.
- **Board validation (Nexys A7 210292BFA3EE, /dev/ttyUSB5):**
  - `host_rs_loop.py random`: 64 runs, each a fresh data seed, error seed,
    injection mode, error count and independently drawn per-checker
    throttle. ALL PASS. These are the same seeds that failed 30 of 64 before
    the two fixes.
  - `host_rs_loop.py soak`: **1,003,520 blocks** in 137 s (7,315 blocks/s),
    245 runs of 4096 blocks each with its own seed pair, 0 failing runs.
    102,542 clean / 760,540 corrected / 140,438 uncorrectable; 3,242,499
    symbols corrected; **59,207,680 beats compared riBM vs Euclid with zero
    mismatches.**
  - `bin/run_smoke.py --sequences init smoke sweep --blocks 64` ALL PASS:
    e = 0..8 every block corrected with exactly e symbols and no mismatching
    beat on either decoder; riBM == Euclid on every beat and verdict.
  - Fabric windows probed on hardware: 0x0 reads the loop block's BUILD_ID,
    the reserved 0x10000 and 0x20000 read 0 and complete.
- **Beyond the correction limit, blocks are NOT all flagged.** An earlier
  version of this manifest claimed e = 9..18 gives "every block
  uncorrectable". That is wrong. A received word carrying more than t symbol
  errors can land within distance t of a DIFFERENT valid codeword, and the
  decoder then corrects it to the wrong message and reports success; the
  re-computed syndromes really are zero because the result really is a
  codeword, so no post-correction check can catch it. Measured across the
  soak: 2 of 77,824 blocks beyond the limit were accepted, 1 in 38,912. The
  Python reference model accepts about 1 in 20,000 on this profile at
  e = t + 1, and both hardware solvers agree on the wrong answer -- which is
  what tells you it is the code's behaviour and not a solver bug.
- **Throughput:** 69.3 cycles per 63-beat block back to back, 122.0 under
  random ready, 59.0 in bypass. The 69 is n/S + 6: the verdict stage is one
  entry deep, so a block's successor cannot enter the correct stage until its
  verdict has been written.
- **Caveat:** the shared checker's CRC is over its regenerated words, so
  `crc_ok` is a delivery check; `data_err` is the data evidence.
