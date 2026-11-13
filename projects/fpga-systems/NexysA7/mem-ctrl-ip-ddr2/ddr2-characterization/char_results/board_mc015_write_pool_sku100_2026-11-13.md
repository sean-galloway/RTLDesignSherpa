# Granite with a 16-entry store pool on the Nexys A7 at 100 MHz (memory-controllers MC-015 board half, 2026-11-13)

The sim half (`sim_mc015_write_pool_2026-11-13.md`) found granite's write
ceiling in the FIFO store's eight-entry pool (eight slots, a nine-cycle slot
turnaround, 8/9 of a command per cycle) and showed the writes level with the
reads at pool 16. This is the board half: the sys100 FPGA SKU built with the
row lane (MC-014) and `GRANITE_NUM_ENTRIES=16`, timing under the 0.2 ns
clock-uncertainty budget the board XDCs carry (MC-011), then the char `every`
+ `windows` suites with the lane on (`TEST_DUAL_ISSUE=1`) against the MC-014
design point's cells of 2026-11-12 (pool 8, lane on, the same RTL), and
`every` with the lane off on the same bitstream. The RTL is unchanged by this
task; the pool is a top-level parameter the board build takes from the
environment, and the SKU default stays 8 until the owner moves it.

## Timing and area

| build | pool | LUT | FF | WNS (ns, under the 0.2 ns budget) | failing endpoints | worst path |
|---|---|---|---|---|---|---|
| MC-014 design point (2026-11-12) | 8 | 36 345 | 32 255 | +0.059 | 0 | main pick `r_req` -> `r_win_cls` |
| this build | 16 | 37 258 | 32 922 | **+0.034** | **0** | the same path, +0.034 / +0.066 on its two bits |

+913 LUT (+2.5 percent) and +667 flops for the second eight entries of both
pools (the write-data buffer, the fill order, the drain queue, the free-slot
scan, the bank queues and the read side's twin). The worst path did not move
to the store: it is still the main pick's class select, inside the placement
spread of the design point's +0.059. Reports:
`targets/granite/fpga/reports_sys100_mc015_n16_2026-11-13`; bitstream
`fpga/bitstream/ddr2_char_granite_sku100_n16_2026-11-13.bit` (untracked).

## Smoke

`init write_read memtest`, lane off and lane on, both ALL PASS on the new
bitstream (init 324 s, memtest 15 s, as on 2026-11-12).

## The cells (lane on; wr / rd MB/s; the 2026-11-12 column is pool 8 on the same RTL)

`every`, the `defaults` and `open_page` presets (every other cell of the 73 is
identical to 2026-11-12 to the MB/s; 0 mismatched beats, every cell ok):

| scenario | preset | pool 8, 2026-11-12 | pool 16 |
|---|---|---|---|
| col_major_interleaved_bl8 | defaults | 688 / 774 | **768 / 768** |
| col_major_interleaved_bl8 | open_page | 688 / 774 | **770 / 770** |
| col_major_interleaved_bl4 | defaults / open_page | 688 / 770, 688 / 774 | 765 / 763, 768 / 768 |
| col_major_interleaved_bl16 | defaults / open_page | 729 / 776 | 772 / 770, 772 / 774 |
| col_major_interleaved_bl8_multiid | defaults / open_page | 688 / 774 | 768 / 768, 770 / 770 |
| incremental_bl4/8/16 | both | 772 / 776-778 | 775 / 776-778 |
| row_major_bl4/8/16 | both | 775 / 778 | 775 / 778 |
| col_major_bl4/8/16 | both | 283 / 389, 416 / 520, 541 / 623 | unchanged |
| col_major_bl8_gap | both | 376 / 400 | unchanged |

`windows` (four threads):

| scenario | preset | pool 8, 2026-11-12 | pool 16 |
|---|---|---|---|
| row_thrash_bl8 | defaults / open_page | 688 / 774 | **770 / 770** |
| random_bl8 | defaults | 629 / 723 | **718 / 740** |
| random_bl8 | open_page | 635 / 729 | **726 / 746** |
| mixed_bl8 | defaults | 487 / 300 | 318 / 649 |
| mixed_bl8 | open_page | 334 / 649 | 473 / 286 |
| mixed_bl8 | close_page | 69 / 115 | 69 / 115 |
| row_thrash_bl8 | close_page | 170 / 229 | 213 / 197 |
| random_bl8 | close_page | 149 / 184 | 188 / 207 |

What the board says, in order:

- **The write ceiling is gone where the sim said it would be.** The three
  bank-parallel families' writes go from 688 / 688 / 629-635 to 765-772 /
  770 / 718-726, level with their reads, within 2 percent of the model's
  refresh-limited 781 on the pure streams. Sim and board agree to 2 MB/s.
- **Reads give back 4-6 MB/s on the pure column streams** (774 -> 768-770 on
  `col_major_interleaved` and `row_thrash`), and gain 17 on `random` (723 ->
  740, 729 -> 746: more entries in flight, more banks open at once). The read
  pool doubled with the write pool, so the read pick sees twice the
  candidates; which of its terms costs the 0.6 percent is a trace question
  this task does not open.
- **`mixed` swapped shapes between the presets** (defaults 487 / 300 -> 318 /
  649, open_page 334 / 649 -> 473 / 286) with 0 mismatches either way. The
  two-direction window is bimodal -- whichever direction holds the batch first
  finishes first -- and the sim's bank-cap sweep at pool 16 was non-monotonic
  (120 / 120, 277 / 513, 473 / 267, 221 / 219 at caps 3 / 4 / 6 / 8). The sum
  moves 787 -> 967 on defaults and 983 -> 759 on open_page. This is the mixed
  window's scheduling question and it is filed there (MC-016); nothing in it
  is a correctness fault.
- `close_page` moves the way more entries should move it (more bank-parallel
  misses in flight) and stays the irrelevant preset it was.

## The lane-off control (`every`, same bitstream)

Against the 2026-11-12 lane-off cells (pool 8): 26 of the 34 `defaults` /
`open_page` cells identical to 2 MB/s; the eight `col_major_interleaved`
cells lose 4-6 MB/s in both directions (bl8 684 / 686 -> 680 / 680 and 688 /
688 -> 683 / 682; bl4 617 / 618 -> 606 / 602; bl16 within 4). With the lane
off the command slot is the ceiling on that family and the pool is not, so
this is the same 0.6-percent give-back the lane-on reads showed, now on both
directions: a cost of the deeper pool on the pure column stream that is not
the pool being full. Small, real, and left as a note for whoever moves the
SKU default; 0 mismatches, every cell ok.

## Recipe

    cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite
    GRANITE_SYS_100=1 GRANITE_DUAL_ISSUE=1 GRANITE_NUM_ENTRIES=16 make bitstream
    make program BITSTREAM=fpga/bitstream/ddr2_char_granite_sku100_n16_2026-11-13.bit
    make run SEQUENCES="init write_read memtest" RUN_ARGS="--controller granite"                       # smoke, lane off
    TEST_DUAL_ISSUE=1 make run SEQUENCES="init write_read memtest" RUN_ARGS="--controller granite"     # smoke, lane on
    TEST_DUAL_ISSUE=1 make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile every   --txn-scale 4000 --char-csv <char_results>/char_granite_sku100n16_every_2026-11-13.csv"
    TEST_DUAL_ISSUE=1 make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile windows --txn-scale 4000 --char-csv <char_results>/char_granite_sku100n16_windows_2026-11-13.csv"
    make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile every --txn-scale 4000 --char-csv <char_results>/char_granite_sku100n16off_every_2026-11-13.csv"

CSV tags: `sku100n16` (lane on) and `sku100n16off` (lane off, the control
against `sku100dual5off` of 2026-11-12).
