# TASK-038: rapids-g loadable firmware memory (BRAM with a config-space write path; ROM once golden)

**Priority:** P2
**Status:** closed -- 2026-10-24; opened 2026-10-23
**Owner:** sean galloway

## Why

Owner 2026-10-23: "what if we had a write path to a BRAM from the config space. The FW could be
loaded/tweaked live. Once it is super golden, then use a ROM." Every firmware change today is a full
bitstream rebuild (~75 min): the image is baked into `r_rom` in `macro_g/rapids_seq_g.sv` from the
generated `sched_g_fw.svh`. The 8-channel gcompare board runs alone took six builds (g, gexe, gfin, gfp,
grf, g8h). The first live load is the two-slot poll fast path: the 16-channel board run (rapids TASK-036)
measured ~180 clocks per chained descriptor against ~44 at one slot per hart, because the two-slot poll in
`rtl/fw_g/sched_g.S` has no HEAD_SUM chain hook.

## What

1. `rapids_seq_g`: parameter `FW_WRITABLE` (0 = ROM, as today; 1 = the same 1024 x 32 array with a write
   port and a readback port, power-up contents the golden image, so an unloaded writable build runs
   exactly as the ROM build).
2. Registers (RDL, both the 8- and 16-channel maps, regenerated through `bin/peakrdl_generate.py`):
   `FW_CTRL` (hold the harts, half select src/snk/both, release through the existing `seq_restart`),
   `FW_ADDR` (auto-increment), `FW_DATA` (write / readback). Writes are refused unless the harts are held.
   A BUILD bit reports FW_WRITABLE.
3. Host: `run_characterization --fw <image>` holds, loads, reads back and compares, releases; every result
   JSON records the image hash (the bitstream no longer identifies the firmware).
4. Sim loads the same image over the same UART path, so sim == board holds.
5. Firmware: the two-slot poll gets the one-slot chain hook (both slots' HEAD_SUM first, fast-stage the
   common head), loaded live on the writable 16-channel build and measured against TASK-036's numbers.

## Done when

Load + readback + run is tested in sim (both halves, both maps, refused-while-running), the full rapids_g
gate passes from clean, a writable rapids-g-16ch bitstream takes a live image on the board with sim ==
board, the two-slot fast path is measured, and HAS/MAS document the registers and the ROM-once-golden flow.
Then STREAM gets the same (stream TASK-018).

## Closed 2026-10-24

Built as specified. `rapids_seq_g` takes `FW_WRITABLE` (0 = ROM, as before; 1 = the same 1024 x 32
block RAM with a host write port and a readback port, powered up with the golden image, so an
unloaded writable build runs exactly as the ROM build). `FW_CTRL` / `FW_ADDR` / `FW_DATA` /
`FW_RDATA` at 0x3A0-0x3AC in both maps (regenerated through `bin/peakrdl_generate.py`); a write with
the harts running is refused, `seq_restart` releases them, and the BUILD word reports the parameter.
`run_characterization.py --fw <image.S> --fw-selftest` (`host/rapids_fw_load.py`) holds, loads both
halves, reads back, runs the self-test (an unheld write refused, a halting image takes every
channel to CH_ERROR, the addressing probe, restore) and records the image hash in every result;
the simulation loads the same image over the same UART path.

Trap found on the way (handbook, generated-rtl-discipline): the FW_ADDR auto-increment first
advanced on the `swmod` / `swacc` LEVEL and counted every cycle, so each access stored the word
twice and advanced by two; the readback walked the same counter and passed below word 512.
Edge-detect the strobe, and probe the address directly.

The first live load was the two-slot poll's chain hook (`rtl/fw_g/sched_g.S`, committed as the
image): on rapids-g-16ch, chain_ch1_b64_d16 went from 1,122 MB/s (184 clocks a descriptor) to
2,008 MB/s (103; rapids-16ch 2,232 at 93), one-beat chains from 19 to 36 MB/s, and the catch-up
size for chains came back to 512 B per descriptor, as at 8 channels (MAS Tables 5.5.4, 5.5.9-11;
HAS 6.4.8-9). On the schedulers-alone bench, whose descriptors are independent, the same poll costs
about 10% on the short rows (MAS 5.5.6).

Bitstreams on the Genesys 2: rapids-g-16ch `FW_WRITABLE` 152,813 LUTs (75.0%) at +0.034 ns; sim ==
board on all 109 gcompare windows with the image loaded live (ROM build: 151,472 LUTs, +0.148 ns).

Gate from `make clean-all`, no reruns: rapids fub_g 192, macro_g 270, top_g 183 (their benches now
drive `seq_restart`, the register mailbox and the `fw_*` bus from Python, `dv/tbclasses/rapids_g_seq_ports.py`,
instead of leaving them undriven or tied inside the TB top; `hart_fault`'s wait scales with the hart
count, after SEED=1215 at 16 harts showed a hart handed a descriptor as the poison lands needs about
30 instructions, 480 clocks, to reach its next SUMMARY read); fub 1,740, fub_beats 1,302, macro 843,
macro_beats 774, top 183, top_beats 54; flows-rapids DV 77/77 at 8 channels on both DUTs (gcompare, gscale and the fw-load cells, writable and ROM) plus 51/51 rapids-g single-DUT cells. Books: MAS 0.84, HAS 0.94,
Beats HAS 0.17.

STREAM: stream TASK-018 stays deferred on the owner's answer to its open question (STREAM has no
firmware; a firmware-sequenced STREAM, or the loader as a shared block).
