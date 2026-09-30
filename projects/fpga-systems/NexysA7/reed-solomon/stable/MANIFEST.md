# Nexys A7 Reed-Solomon loop harness -- last stable build

**One slot. Overwrite it; do not accumulate versions.**

`make keep` in a build directory copies that build's bitstream to the HOLD dir
outside the repo (`$RDS_HOLD_DIR/<board>/<flow>/`) and its reports here. The
RTL is NOT copied: a bitstream whose source you cannot reconstruct is only
useful as "the last thing known to work on the board." `stable/` is a sibling
of the build-* dirs, outside the blast radius of `make clean-all`.

## Current contents

- **Build:** build-loop (rs_loop_top), kept 2026-09-30, the fabric version:
  `uart_axil_bridge` -> generated 1x3 `bridge_rs_loop_axil` -> the loop's
  register block on the APB window through `apb4_to_peakrdl`, with the
  rs_regs and observer windows reserved and tied off. RS(252,236) over
  GF(2^8), t = 8, 4 symbols per beat; decoder A riBM, decoder B Euclid.
- **HOLD file:** `/mnt/data/fpga-hold/nexys_a7_100t/rs_loop/rs_loop.bit`
- **Timing:** MET after place and route at 100 MHz, WNS +0.157 ns, 0 failing
  endpoints. The critical path is the Euclid solver's output un-shift into the
  solve-to-correct descriptor, 10 logic levels.
- **Utilization (impl):** 18248 LUTs (28.8%), 8160 flops (6.4%), 6 DSPs, 0 BRAM.
- **Board validation (Nexys A7 210292BFA3EE, /dev/ttyUSB5):**
  `bin/run_smoke.py --sequences init smoke sweep --blocks 64` ALL PASS:
  e = 0..8 every block corrected with exactly e symbols and no mismatching
  beat on either decoder; e = 9..18 every block uncorrectable on both with
  mismatches seen; riBM == Euclid on every beat and every verdict at every e.
  Also passed: the same at e = 0/4/8/9/12 with random ready on both checkers,
  burst mode e = 8, rate mode 1% over 256 blocks (652 symbols, 234 blocks
  corrected, 22 clean). Fabric windows probed on hardware: 0x0 reads the
  loop block's BUILD_ID, the reserved 0x10000 and 0x20000 read 0 and
  complete.
- **Throughput:** 69.3 cycles per 63-beat block back to back, 122.0 under
  random ready, 59.0 in bypass. The 69 is n/S + 6: the verdict stage is one
  entry deep, so a block's successor cannot enter the correct stage until its
  verdict has been written.
- **Caveat:** the shared checker's CRC is over its regenerated words, so
  `crc_ok` is a delivery check; `data_err` is the data evidence.
