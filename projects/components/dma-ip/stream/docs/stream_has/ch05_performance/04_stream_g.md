<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Choosing STREAM or stream-g

**Last Updated:** 2026-10-24

stream-g (STREAM MAS Chapter 7) is register-compatible with STREAM: the same descriptors, the same
map, the same engines, with the per-channel scheduler state machines replaced by firmware on one
gatling core. The choice between them is a hardware one, throughput for the descriptors the system
will issue against area. This chapter is the guide; the measurements it rests on, every point of them,
with the build, the method and the harness, are the Genesys 2 book, *STREAM on the Genesys 2 -- The
FPGA System*, Chapter 5 (`projects/fpga-systems/Genesys2/dma-ip/stream/docs/`). rapids HAS Chapter
6.4 is the same comparison for RAPIDS.

## Selection Guide

Measured on the Genesys 2, both designs from the same tree, 8 channels, 128-bit data (16 bytes a beat),
100 MHz, peak 1,600 MB/s:

| The system issues | Use | Why |
|---|---|---|
| Descriptors of 32 KB (2,048 beats) or more | either; stream-g saves the 64 DSPs | within 1 % of STREAM with every channel busy, within 5 % on a lone channel (within 1 % from 256 KB) |
| Chains of 512 B (32-beat) descriptors or longer, all channels busy | either | within 1 % |
| Chains on one channel | either from 2 KB a descriptor | within 5 % from 2 KB, 1 % from 8 KB; below 1 KB stream-g reaches 31-51 % of STREAM |
| Descriptors of 1 KB or less, a few channels busy | STREAM | stream-g reaches 45-80 % of STREAM: the firmware spends about 140 clocks per descriptor |
| Single-beat or very short descriptors | STREAM | stream-g reaches 17-36 % of STREAM |
| TYPE=EXT descriptors with short runs | STREAM | stream-g computes each run base in firmware: 94x slower at runs of 4, 125x per beat (Table 5.4.2) |
| TYPE=EXT descriptors with runs of 256 beats or more | STREAM, unless DSPs are short | stream-g is 2.4x slower at 256-beat runs |
| No DSPs to spare | stream-g | STREAM's EXT run-base multipliers are 64 DSPs at 8 channels (128 at 16); stream-g uses none |

: Table 5.4.1: Choosing a design

The rule underneath: stream-g pays a fixed firmware cost once per descriptor, about 140 clocks from
the kick to the first read on a single descriptor and a clock or two on each chained one after it, and
hides it behind the data in flight. A descriptor that takes longer than that to move costs nothing
extra; a shorter one pays the difference. At 16 bytes a beat and 100 MHz the break-even is near 256
beats (4 KB) with all channels busy and near 2,048 beats (32 KB) for a lone descriptor.

## Scheduler Limit

The board numbers include the harness and the AXI engines. To isolate the schedulers, the STREAM MAS
bench (Section 7.4, `dv/tests/fub_g`, the `perf` case) runs both designs with engines that never stall,
every channel at once, and counts cycles to finish. The 16-channel columns are the default eight
harts with two slots each:

| Scenario | STREAM 8ch | stream-g 8ch | STREAM 16ch | stream-g 16ch |
|---|---:|---:|---:|---:|
| 16 one-beat descriptors, one channel | 131 | 2,371 | 131 | 3,131 |
| 16 one-beat descriptors on each channel | 131 | 2,320 | 131 | 5,383 |
| 16 64-beat descriptors on each channel | 1,259 | 2,401 | 1,259 | 5,469 |
| 4 64 KB descriptors on each channel | 9,251 | 9,430 | 9,251 | 9,588 |
| 2 1 MB descriptors on each channel | 84,277 | 84,418 | 84,277 | 84,610 |
| EXT, runs of 4, 64 beats, 4 per channel | 419 | 39,473 | 419 | 77,998 |
| EXT, per beat, 64 beats, 4 per channel | 1,043 | 131,126 | 1,043 | 257,831 |
| EXT, runs of 256, 1 MB, 1 per channel | 29,796 | 71,127 | 29,796 | 139,686 |

: Table 5.4.2: Cycles to finish, schedulers alone, 256-bit bench, STREAM's own firmware (lower is better)

The schedulers and the window are rapids-g's block, and the firmware was its image until 2026-10-24, when
STREAM took its own (MAS 7.3) with the chain hook on both reads of the one-slot poll (stream TASK-021):
the 16-channel column, two slots per hart on the unchanged two-slot poll, is rapids HAS Table 6.4.6 to
the cycle, and the 8-channel column moved by the two instructions each pass now carries (the scenarios
above have no chained heads opening mid-pass, so none gains from them; the board profiles do).

## Where stream-g Catches STREAM

What a channel must move per descriptor for stream-g to be within 10 %, 5 % and 1 % of STREAM, from
the board's size sweeps of 2026-10-25 (the smallest size from which every larger size in the sweep stays
inside the bound; a chain row is bytes per descriptor in a 16-descriptor chain; Genesys 2 book Tables 5.5
and 5.6):

| Shape | Busy channels | Within 10 % | Within 5 % | Within 1 % |
|---|---:|---:|---:|---:|
| single descriptor | 1 of 8 | 32 KB | 64 KB | 256 KB |
| single descriptor | 8 of 8 | 4 KB | 8 KB | 32 KB |
| 16-descriptor chain | 1 of 8 | 2 KB | 2 KB | 8 KB |
| 16-descriptor chain | 8 of 8 | 256 B | 256 B | 512 B |

: Table 5.4.3: Bytes per descriptor for stream-g to be within 10 %, 5 % and 1 % of STREAM

With one channel busy a lone descriptor has nothing to hide the firmware behind, so the bounds sit
eight times higher than with every channel busy; a chain overlaps the next head with the running
descriptor (the read-ahead prefetch, which stream-g keeps in hardware for a head the firmware has
staged), so chains of 512 B descriptors are at parity with every channel busy. The first image's
lone-channel chains had a plateau from 32 to 80 beats (stream TASK-021): its poll loop took a head
opened mid-pass by the in-place advance down the slow path. stream-g's own firmware tests the chain
hook on both reads of a pass, and the rows above are measured on it (2026-10-25).

## Area

In the Genesys 2 harness, same tree and flow: STREAM 66,221 LUTs, 26 block RAM tiles, 64 DSPs at
+0.790 ns; stream-g 65,472 LUTs, 29 block RAM tiles, no DSPs at +0.668 ns. The DSPs are the EXT
run-base multipliers; the block RAMs are the firmware ROM and the harts' scratch. The cores out of
context in the board geometry: `stream_core` 32,025 LUTs and 64 DSPs at 8 channels, 61,106 and 128 at 16;
`stream_core_g` 32,164 LUTs and no DSPs at 8 channels, 59,386 at 16, both closing 100 MHz (Genesys 2
book Tables 5.1 and 5.2).

## Related

- STREAM MAS Chapter 7: stream-g, what changes and what stays the same; Section 7.4 the bench, the
  verification and the measurement record
- STREAM on the Genesys 2 -- The FPGA System, Chapter 5: the board side, every measured table
- rapids HAS Chapter 6.4: the same comparison for RAPIDS and rapids-g
