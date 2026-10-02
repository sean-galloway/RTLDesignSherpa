# Nexys A7 Reed-Solomon loop harness -- last stable build

**One slot. Overwrite it; do not accumulate versions.**

`make keep` in a build directory copies that build's bitstream to the HOLD dir
outside the repo (`$RDS_HOLD_DIR/<board>/<flow>/`) and its reports here. The
RTL is NOT copied: a bitstream whose source you cannot reconstruct is only
useful as "the last thing known to work on the board." `stable/` is a sibling
of the build-* dirs, outside the blast radius of `make clean-all`.

## Current contents

**FOUR images now, from one harness RTL** -- datapath x solver. The AXIS pair
was built by `bin/build_image_matrix.sh` on 2026-10-01 (second round: with the
interface observers); the AXI4 pair was rebuilt 2026-10-02 with the sdpram_core
burst-queue fix (amba 71d48b6f7 -- the burst boundary is free, see "The cost
was the MEMORY SLAVE" below). One solver per bitstream, never
both: two solvers double the key-equation area and the comparator changes the
very handshake the meters measure. All four close with ZERO failing endpoints.

| | axis_ribm | axis_euclid | axi4_ribm | axi4_euclid |
|---|---|---|---|---|
| Routed WNS | +0.462 ns | +0.249 ns | +0.203 ns | +0.261 ns |
| Failing endpoints | 0 | 0 | 0 | 0 |
| Slice LUTs | 15,787 | 17,973 | 24,203 | 26,358 |
| Block RAM tiles | 0 | 0 | 12 | 12 |

All four carry the four bandwidth meters AND two interface observers on the
fabric's expansion windows: an `axis4_intf_observer` on the four AXIS seams
(0x20000, live on every image) and an `axi4_intf_master_observer` on the
codec's own ports (0x10000, live on the AXI4 flavours, a read-0 stub on AXIS).
The observers cost +4.6k LUTs on the AXIS images and +11.2k on AXI4 (the
master observer's per-port latency histograms are the difference) against the
first round's 11,130 / 13,418 / 12,486 / 14,654 -- and moved the measured
datapath not at all: every bandwidth figure below re-measured digit-identical
with the observers in the images.

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

## Bandwidth, all four images (AXI4 pair re-measured 2026-10-02)

Programmed and measured in turn by `bin/measure_image_matrix.sh`; raw output
in `reports/bandwidth.txt`. Every image passed its random campaign (64 runs,
0 failures) before its bandwidth was taken. Slopes: AXIS 64 -> 256 blocks,
AXI4 16 -> 64 (its per-kick cap is CFG_AXI4_MAX_BLOCKS = 4096/63 = 65 and the
harness refuses a larger run rather than clamping it). The AXIS pair
re-measured 2026-10-02 digit-identical to 2026-10-01; the AXI4 pair below is
the FIXED slave, on images rebuilt with amba 71d48b6f7.

| image | end-to-end cyc/block | codeword out | codeword in | message |
|---|---|---|---|---|
| axis_ribm | 63.00 | **100.0%** | **100.0%** | 93.7% |
| axis_euclid | 63.00 | **100.0%** | **100.0%** | 93.7% |
| axi4_ribm | 244.00 | **100.0%** | **100.0%** | 24.2% |
| axi4_euclid | 244.00 | **100.0%** | **100.0%** | 24.2% |

**The solver is throughput-neutral.** riBM and Euclid are identical to the
cycle in both datapaths -- 16,264 cycles for 256 AXIS blocks either way. The
key-equation stage costs iterations+1 and Euclid's extra iteration is still far
inside the 63-beat budget, so the choice is an area and timing decision only
(17,973 vs 15,787 LUTs on AXIS). The host reads the solver name from TOPOLOGY,
so the pair being identical is not a stale bitstream.

### The codeword meters are gated to the stage that owns them

On AXIS the codec runs for the whole run and both windows are just `busy`. On
AXI4 the five stages are SEQUENTIAL, so a whole-run window reports the pass
structure rather than the codec: before gating, the encoder's W channel logged
17,251 starved cycles of 21,784 and read 18.7%, purely because four fifths of
the run was not the encode pass. `obs_enc_active` / `obs_dec_active` now gate
each meter to its own stage.

With that, the AXI4 codec's own cost is visible and it is NOT the fixture.
After the slave fix (below), the codec seams read at LINE RATE on the board,
slope over 16 -> 64 blocks, both solvers identical:

| seam | cycles in window | beats | utilisation |
|---|---|---|---|
| codeword out (encode pass) | 3,024 | 3,024 | **100.0%** |
| codeword in (decode pass) | 3,024 | 3,024 | **100.0%** |

**The cost WAS the MEMORY SLAVE, not the engines -- and it is FIXED.** Before
the fix, with the window gated, the encoder's W channel showed 501 cycles of
BACKPRESSURE against 11 of starvation -- it was producing fine and the slave
was refusing -- and the decoder's R channel showed 394 of starvation against
zero backpressure, the slave failing to deliver. Both divided evenly by the
burst count (~2.0 and ~1.6 cycles per burst), so it was burst-start cost in
the slave: sdpram_core serialised bursts, refusing the next command until the
active burst's response had fully retired (amba ISSUE-004, originally closed
no-action with that behaviour documented as the contract).

Sean overruled that close on 2026-10-02: the documented behaviour was the bug.
sdpram_core now queues burst commands two deep per direction and reloads its
tracker the cycle the active burst completes, so a burst boundary is FREE
(amba 71d48b6f7; ISSUE-004 amended to fixed). The seams above are the board
reading after the fix; the pre-fix board reading was 97.0% out / 98.5% in.

`CFG_AXI4_BURST_LEN` went 16 -> 64 before the fix, quartering the burst count,
which was the fixture-side mitigation while the slave was left alone. The
config stays: fewer bursts is fewer command round trips regardless. 64 beats
is 256 bytes and MUST be a power of two: the
engines issue bursts back to back from the job base, so each is aligned to its
own size, and a size dividing 4096 cannot cross AXI4's 4 KB boundary. One
burst per codeword is NOT available -- 63 beats is 252 bytes, which would
eventually straddle it.

### Where the AXI4 end-to-end number comes from

| | cyc/block |
|---|---|
| five-pass, burst 16 (original) | 337.75 |
| five-pass, burst 64 | 314.60 |
| four-pass, burst 64 (pre-fix slave) | 249.65 |
| **four-pass, burst 64, fixed slave (now)** | **244.00** |
| four-pass floor (4 x 63) | 252.00 |

**The inject pass is gone.** The injector moved onto the DECODER'S READ
CHANNEL: the decoder reads M2 and what comes back has been corrupted in
flight, so there is no read/corrupt/write hop through a third memory any more.
That removed one sequential pass (-64.95 cyc/block, almost exactly the 63-beat
codeword) and a whole memory (16 -> 12 block RAMs, and 504 LUTs on riBM), and
cost the codec seams nothing -- they read 97.0% and 98.5% either way at the
time, and 100.0% both ways on the fixed slave now.

It is also closer to the original intent than the memory hop was. The thing
doing the corrupting is the CHANNEL, not either codec; a separate hop honoured
that only because a job engine cannot corrupt inline, and sitting in the R
channel says it directly while staying outside both codecs.

What it needs to be correct: rs_error_injector is a three-stage elastic
pipeline, strictly one beat in to one beat out and in order, so the R
channel's sideband -- rlast, rid, rresp -- rides a FIFO pushed on the input
handshake and popped on the output one. The alignment holds for exactly that
reason and would not survive a block that dropped or duplicated a beat. And
in_last must be the CODEWORD boundary, not rlast: a 64-beat burst and a
63-beat codeword do not coincide, so a beat counter generates it.

STATUS.axi4_stage bit 2 now reads 0 permanently -- there is no inject stage --
so a complete chain is 0x1B, not 0x1F. The field kept its five-bit width so
the register map did not move; the host's expectation moved instead.

Remaining: the naive four-pass floor is 4 x 63 = 252 against a measured
244.00, so the passes already overlap by 8 cyc/block -- the burst boundary
itself is free since the slave fix, and what separates the measurement from
the naive floor is pipeline overlap between stages that the serial-pass model
does not credit. Dropping drain -- the checker observing the decoder's write
channel -- would reach about 189, but nothing else reads M4, so that one
trades UNIQUE coverage. The inject pass did not: its engines duplicated
coverage the other passes already provide, which is why it went first.

## Interface observers (board-proven 2026-10-01, second-round images)

The fabric's two expansion windows are no longer reserved: each answers with
an `obs_regs` interface observer, read by NAME through the same regmap on both
(`host_rs_loop.py obs`; `--hist` adds the AXI4 latency histograms).

- **0x20000, `axis4_intf_observer`** -- the four AXIS seams in codeword order
  (msg_in, cw_out, cw_in, msg_out): per-port cycle buckets plus exact
  bytes/beats/packets. Live on every image; on AXI4 flavours the two codec
  seams are tied and the outer two stay live as a cross-check.
- **0x10000, `axi4_intf_master_observer`** -- the codec's four AXI4 master
  ports (enc_rd, dec_rd, enc_wr, dec_wr): cycle buckets, timed-transaction
  totals and log2 latency histograms (AR->first-R, AR->RLAST, AW->B). AXI4
  flavours only; a read-0 stub on AXIS, which OBS_CAPS reports as rd_ports=0
  rather than the host assuming.

Board-proven on both flavours: the per-port beat counts are the exact run
arithmetic (B blocks x 59 message / 63 codeword beats; 16-block AXIS and AXI4
runs read 944/1008 on the nose, 64-block 3776/4032), they stay exact at
e = t = 8, the meters clear with each run, and every histogram's bins sum to
its timed-transaction total. The same expectations are asserted in cosim by
`uart_observers` / `uart_axi4_observers`; the CLI prints the arithmetic as a
WANT column so a dropped or duplicated beat flags itself.

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
  learns that from TOPOLOGY rather than being told. The soak figures predate
  the sdpram slave fix; the 2026-10-02 rebuilt images (both solvers) re-passed
  the random campaign 64 of 64 before their bandwidth was taken.

- **Why the AXI4 soak is 100k and not a million.** Throughput is 114 blk/s
  against the stream path's 7,315, because the AXI4 datapath is five
  sequential jobs per kick and each memory holds only
  `CFG_AXI4_MEM_DEPTH / CFG_N_BEATS` = 65 blocks, so the per-kick UART cost
  dominates. A million blocks would be ~15,400 kicks and about two hours.
  Raising `CFG_AXI4_MEM_DEPTH` fourfold lifts the cap to 260 blocks and costs
  64 block RAM tiles of 135, which would bring a million blocks to roughly half
  an hour. Not done, because it invalidates the bitstream above.

- **Revalidated end to end on the final RTL (2026-10-01, axis_ribm).** The
  random campaign is 64 of 64 runs x 4 blocks with 0 failing runs, and the
  **soak was re-run at a million blocks: 1,003,520 in 137 s (7,315 blk/s), 0
  failing runs** -- 102,542 clean / 760,540 corrected / 140,438 uncorrectable,
  3,242,499 symbols corrected. Beyond the correction limit, 2 of 77,824 blocks
  were accepted and silently mis-decoded (1 in 38,912) against the model's
  ~1 in 20,000. Every one of those figures matches the pre-pipelining soak
  digit for digit, which is the point: the decoder got faster and its verdicts
  did not move. The beats-compared figure is 0 because this image carries one
  solver and no comparator, by construction.

  The soak rate is HOST-BOUND, not datapath-bound, and it is a useful canary.
  It first came back at 5,020 blk/s -- a 31% drop -- because `collect()` read
  the four bandwidth windows on every run, sixteen register reads over a
  115200-baud UART that a soak never looks at. `run(meters=False)` restored it
  to exactly 7,315. If this number moves again, suspect the host's per-run
  register traffic before suspecting the hardware.

- **Caveat (both flavours):** the shared checker's CRC is over its regenerated
  words, so `crc_ok` is a delivery check; `data_err` is the data evidence.
