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

# Choosing RAPIDS or rapids-g

**Last Updated:** 2026-10-23

rapids-g (Section 2.3) is register-compatible with RAPIDS, so the choice between them is a hardware
one: throughput for the descriptors the system will issue, against area. This chapter gives the
measured numbers for both, side by side, and a guide for choosing. The designs are named by
channel count: rapids-8ch is RAPIDS with 8 channels and rapids-g-8ch is rapids-g with 8 channels.

## Selection Guide

| The system issues | Use | Why (tables below) |
|------------------------------|----------------|--------------------------------------------|
| Descriptors of 32 KB (1,024 beats) or more | either; rapids-g-8ch saves the 64 DSPs | rapids-g-8ch is within 2% of rapids-8ch at 8 channels, within 13% at one channel |
| Chains of 2 KB (64-beat) descriptors, all channels busy | either | rapids-g-8ch is within 2% (interleaved sink) and 2% (source) |
| Descriptors of 2 KB or less, a few channels busy | rapids-8ch | rapids-g-8ch is 20-75% slower: the firmware spends about 90 clocks per descriptor |
| Single-beat or very short descriptors | rapids-8ch | rapids-g-8ch reaches 26-57% of rapids-8ch |
| TYPE=EXT descriptors with short runs | rapids-8ch | rapids-g-8ch computes each run base in firmware: 96x slower at runs of 4, 125x per beat |
| TYPE=EXT descriptors with runs of 256 beats or more | rapids-8ch, unless DSPs are short | rapids-g-8ch is 2.4x slower at 256-beat runs |
| 16 channels | rapids-16ch; rapids-g-16ch when DSPs are short, or the descriptors are 512 B (16 beats) or more | in simulation that matches the board (Table 6.4.8): rapids-g-16ch chains are within 5% of rapids-16ch from 512 B per descriptor, as at 8 channels, and single descriptors from 8 KB (Table 6.4.9 has the 10%, 5% and 1% sizes); one- and two-beat chains reach 32-41% of it (49-52% at 8 channels). It saves 128 DSPs for about 12% more LUTs in the board harness |
| No DSPs to spare | rapids-g-8ch | RAPIDS uses 64 DSPs for the EXT run-base multipliers; rapids-g uses none |

: Table 6.4.1: Choosing a design

The rule underneath: rapids-g pays a fixed firmware cost per descriptor, about 90 clocks at 8
channels, and hides it behind the descriptor in flight. A descriptor that takes longer than that to
move costs nothing extra; a shorter one pays the difference. At 32 bytes a beat and 100 MHz, the
break-even is near 64 beats with all channels busy and near 1,024 beats for a chain on one channel.

## How the Numbers Were Measured

Both designs ran the same 45-point `gcompare` profile on the Genesys 2 harness: 8 channels, 256-bit
data (one beat is 32 bytes), 100 MHz, so the peak is **3,200 MB/s per direction**. Each figure is
the bytes moved over the hardware timer's cycle count from the first request to the last write,
so it includes descriptor fetch and launch. Every point is golden-checked, and every point passes on
both designs.

The simulation of the board build matches the board exactly: on both designs all 85 measured
windows are identical, cycle for cycle, so every figure below is both the board's and the
simulation's.

The point names read `<group>_ch<N>_b<B>[_d<D>][_il]`:

| Part | Meaning |
|---|---|
| `beat` / `chain` | one descriptor per channel / a chain of linked descriptors per channel |
| `ch<N>` | active channels |
| `b<B>` | beats per descriptor (32 bytes each): `b64` is 2 KB |
| `d<D>` | descriptors per channel in the chain; absent means one |
| `il` | interleaved sink: every channel's stream holds data at once |

: Table 6.4.2: Point names

Without `il`, the sink stream feeds the channels one after another, so only one channel holds data
at a time and an 8-channel sink figure behaves like a one-channel figure. The `il` points are the
8-channel sink case. The source side reads memory for every channel at once in every point.

## Single Descriptor per Channel

| Point | rapids-8ch sink | rapids-g-8ch sink | rapids-8ch source | rapids-g-8ch source |
|----------------------------------|-------------:|-------------:|-------------:|-------------:|
| beat_ch1_b1 | 54 | 14 | 50 | 14 |
| beat_ch1_b16 | 624 | 210 | 648 | 212 |
| beat_ch1_b64 | 1,575 | 701 | 1,613 | 709 |
| beat_ch1_b256 | 2,544 | 1,693 | 2,568 | 1,703 |
| beat_ch1_b1024 | 3,006 | 2,617 | 3,015 | 2,624 |
| beat_ch1_b4096 | 3,149 | 3,031 | 3,152 | 3,033 |
| beat_ch1_b32768 | 3,194 | 3,178 | 3,194 | 3,178 |
| beat_ch4_b16 | 1,056 | 589 | 1,095 | 621 |
| beat_ch4_b64 | 2,122 | 1,517 | 2,161 | 1,569 |
| beat_ch4_b256 | 2,840 | 2,505 | 2,857 | 2,540 |
| beat_ch8_b1 | 116 | 66 | 121 | 66 |
| beat_ch8_b4 | 425 | 252 | 436 | 250 |
| beat_ch8_b16 | 1,198 | 806 | 1,237 | 811 |
| beat_ch8_b64 | 2,257 | 1,837 | 2,291 | 1,843 |
| beat_ch8_b256 | 2,897 | 2,699 | 2,911 | 2,703 |
| beat_ch8_b1024 | 3,119 | 3,058 | 3,123 | 3,059 |
| beat_ch8_b4096 | 3,179 | 3,163 | 3,180 | 3,164 |

: Table 6.4.3: MB/s, one descriptor per channel (peak 3,200)

## Descriptor Chains

| Point | rapids-8ch sink | rapids-g-8ch sink | rapids-8ch source | rapids-g-8ch source |
|----------------------------------|-------------:|-------------:|-------------:|-------------:|
| chain_ch1_b1_d16 | 149 | 73 | 278 | 73 |
| chain_ch1_b64_d16 | 2,214 | 1,875 | 3,015 | 1,788 |
| chain_ch1_b1024_d16 | 3,113 | 3,103 | 3,188 | 3,177 |
| chain_ch1_b8192_d4 | 3,186 | 3,180 | 3,194 | 3,188 |
| chain_ch8_b1_d16 | 164 | 74 | 1,177 | 419 |
| chain_ch8_b64_d16 | 2,276 | 1,975 | 3,123 | 3,059 |
| chain_ch8_b1024_d16 | 3,121 | 3,117 | 3,195 | 3,191 |
| chain_ch8_b8192_d4 | 3,190 | 3,188 | 3,198 | 3,195 |

: Table 6.4.4: MB/s, descriptor chains (16 descriptors unless noted; peak 3,200)

## Interleaved Sink

| Point | rapids-8ch | rapids-g-8ch | rapids-g-8ch / rapids-8ch |
|----------------------------------|-------------:|-------------:|-------------:|
| beat_ch8_b16_il | 1,048 | 726 | 69% |
| beat_ch8_b64_il | 2,098 | 1,717 | 82% |
| chain_ch8_b1_d16_il | 822 | 418 | 51% |
| chain_ch8_b64_d16_il | 2,709 | 2,662 | 98% |
| chain_ch8_b1024_d16_il | 3,166 | 3,162 | 99.9% |

: Table 6.4.5: Sink MB/s with all 8 channels' streams interleaved (peak 3,200)

## Scheduler Limit

The board numbers include the harness and the AXI engines. To isolate the schedulers, the RAPIDS
MAS bench (Section 5.5) runs both designs with engines that never stall, both directions on every
channel at once, and counts cycles to finish:

| Scenario | rapids-8ch | rapids-g-8ch | rapids-16ch | rapids-g-16ch |
|----------------------------------|-------------:|-------------:|-------------:|-------------:|
| 16 one-beat descriptors, one channel | 131 | 2,371 | 131 | 3,131 |
| 16 64-beat descriptors on each channel | 1,255 | 2,389 | 1,255 | 5,469 |
| 4 64 KB descriptors on each channel | 9,248 | 9,412 | 9,248 | 9,585 |
| 2 1 MB descriptors on each channel | 84,277 | 84,443 | 84,277 | 84,612 |
| EXT, runs of 4, 64 beats, 4 per channel | 407 | 39,201 | 407 | 77,998 |
| EXT, per beat, 64 beats, 4 per channel | 1,043 | 130,086 | 1,043 | 257,831 |
| EXT, runs of 256, 1 MB, 1 per channel | 29,574 | 70,641 | 29,574 | 139,688 |

: Table 6.4.6: Cycles to finish, schedulers alone (lower is better)

The 16-channel columns are the default eight harts with two slots each, on the committed firmware
image; the MAS (Table 5.5.6) has the 16- and 4-hart alternatives and the cost of the chain hook on
this bench's independent descriptors.

## Sixteen Channels on the Board

rapids-16ch and rapids-g-16ch in the full Genesys 2 harness, 2026-10-23. On the board, the 57-point 16-channel gcompare profile matches simulation on every window; the size sweep below ran in that simulation (`make sim-gscale`). Each cell is rapids cycles / rapids-g cycles with every channel of the build busy (1.00 = parity; rows are beats per descriptor, 32 bytes each; 8-channel rows for comparison). `chains` are 16-descriptor interleaved-sink chains; `sink` and `source` a single descriptor per channel:

| Beats | chains 8ch | chains 16ch | sink 8ch | sink 16ch | source 8ch | source 16ch |
|------:|-----:|-----:|-----:|-----:|-----:|-----:|
| 1 | 0.52 | 0.32 | 0.57 | 0.53 | 0.55 | 0.49 |
| 2 | 0.49 | 0.41 | 0.57 | 0.53 | 0.56 | 0.51 |
| 4 | 0.60 | 0.68 | 0.59 | 0.56 | 0.57 | 0.54 |
| 8 | 0.90 | 0.93 | 0.63 | 0.62 | 0.61 | 0.60 |
| 16 | 0.95 | 0.97 | 0.67 | 0.72 | 0.66 | 0.70 |
| 32 | 0.97 | 0.98 | 0.74 | 0.82 | 0.73 | 0.82 |
| 64 | 0.98 | 0.99 | 0.81 | 0.88 | 0.80 | 0.88 |
| 128 | 0.99 | 0.99 | 0.88 | 0.92 | 0.88 | 0.92 |
| 256 | 0.99 | 1.00 | 0.93 | 0.96 | 0.93 | 0.96 |
| 512 | 1.00 | 1.00 | 0.96 | 0.98 | 0.96 | 0.98 |
| 1024 | 1.00 | 1.00 | 0.98 | 0.99 | 0.98 | 0.99 |
| 2048 | -- | -- | 0.99 | 0.99 | 0.99 | 0.99 |
| 4096 | -- | -- | 0.99 | 1.00 | 0.99 | 1.00 |

: Table 6.4.8: rapids / rapids-g cycles, every channel busy

What a channel must move per descriptor for rapids-g to be within 10%, 5% and 1% of rapids (32 bytes
a beat; the smallest size from which every larger size in the sweep stays inside the bound; a chain
row is bytes per descriptor in a 16-descriptor chain), with every channel busy and with one channel
busy on each build:

| Shape | Busy channels | Within 10% | Within 5% | Within 1% |
|------------------------------------|-------------:|-----------:|----------:|----------:|
| single descriptor, sink | 1 of 8 | 64 KB | 128 KB | 512 KB |
| single descriptor, sink | 8 of 8 | 8 KB | 16 KB | 64 KB |
| single descriptor, sink | 1 of 16 | 64 KB | 128 KB | 1 MB |
| single descriptor, sink | 16 of 16 | 4 KB | 8 KB | 64 KB |
| single descriptor, source | 1 of 8 | 64 KB | 128 KB | 512 KB |
| single descriptor, source | 8 of 8 | 8 KB | 16 KB | 128 KB |
| single descriptor, source | 1 of 16 | 64 KB | 128 KB | 1 MB |
| single descriptor, source | 16 of 16 | 4 KB | 8 KB | 64 KB |
| single descriptor, interleaved sink | 8 of 8 | 8 KB | 16 KB | 64 KB |
| single descriptor, interleaved sink | 16 of 16 | 8 KB | 16 KB | 128 KB |
| 16-descriptor chain, sink | 1 of 8 | 4 KB | 4 KB | 16 KB |
| 16-descriptor chain, sink | 1 of 16 | 2 KB | 4 KB | 32 KB |
| 16-descriptor chain, source | 1 of 8 | 4 KB | 8 KB | 16 KB |
| 16-descriptor chain, source | 1 of 16 | 4 KB | 8 KB | 32 KB |
| 16-descriptor chain, interleaved sink | 8 of 8 | 512 B | 512 B | 4 KB |
| 16-descriptor chain, interleaved sink | 16 of 16 | 256 B | 512 B | 4 KB |

: Table 6.4.9: Bytes per descriptor for rapids-g to be within 10%, 5% and 1% of rapids

The one-channel rows come from the same sweep run with one channel busy (`make sim-gscale1
CHANNELS=8|16`, both directions, chains plain rather than interleaved), on each build:

| Beats | chain sink (8ch build) | chain sink (16ch build) | chain source (8ch build) | chain source (16ch build) | sink (8ch build) | sink (16ch build) | source (8ch build) | source (16ch build) |
|------:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|
| 1 | 0.49 | 0.22 | 0.26 | 0.12 | 0.27 | 0.26 | 0.28 | 0.27 |
| 2 | 0.53 | 0.24 | 0.26 | 0.12 | 0.27 | 0.26 | 0.29 | 0.27 |
| 4 | 0.62 | 0.28 | 0.26 | 0.12 | 0.29 | 0.27 | 0.29 | 0.28 |
| 8 | 0.56 | 0.36 | 0.27 | 0.12 | 0.31 | 0.29 | 0.30 | 0.29 |
| 16 | 0.48 | 0.45 | 0.44 | 0.20 | 0.34 | 0.32 | 0.33 | 0.31 |
| 32 | 0.54 | 0.60 | 0.78 | 0.36 | 0.38 | 0.35 | 0.37 | 0.35 |
| 64 | 0.85 | 0.90 | 0.59 | 0.66 | 0.45 | 0.42 | 0.44 | 0.41 |
| 128 | 0.96 | 0.96 | 0.92 | 0.95 | 0.54 | 0.51 | 0.54 | 0.51 |
| 256 | 0.99 | 0.98 | 0.99 | 0.98 | 0.67 | 0.63 | 0.66 | 0.63 |
| 512 | 0.99 | 0.99 | 0.99 | 0.99 | 0.78 | 0.75 | 0.78 | 0.75 |
| 1024 | 1.00 | 0.99 | 1.00 | 0.99 | 0.87 | 0.85 | 0.87 | 0.85 |
| 2048 | -- | -- | -- | -- | 0.93 | 0.92 | 0.93 | 0.92 |
| 4096 | -- | -- | -- | -- | 0.96 | 0.96 | 0.96 | 0.96 |
| 8192 | -- | -- | -- | -- | 0.98 | 0.98 | 0.98 | 0.98 |
| 16384 | -- | -- | -- | -- | 0.99 | 0.99 | 0.99 | 0.99 |
| 32768 | -- | -- | -- | -- | 1.00 | 0.99 | 1.00 | 0.99 |

: Table 6.4.10: rapids / rapids-g cycles, one channel busy (`--` = not in the sweep)


With one channel busy a lone descriptor has nothing to hide the firmware behind: against the FSM it
costs a fixed 162 clocks per single descriptor on the 8-channel build and 194 on the 16-channel one,
whose hart walks a second, idle slot each pass (the cycle gap is the same from 8 KB to 1 MB), so the
ratio is 1 - gap / beats: within 10% from 64 KB, 5% from 128 KB, and 1% from 512 KB (8 channels) or
1 MB (16).
A chain on one channel overlaps the next head with the running descriptor and is within 5% from 4-8 KB
and 1% from 16-32 KB; the 16-channel build is later on chains below 2 KB because its hart walks a second,
idle slot every pass. With every channel busy the other channels' data hides the cost, which is why
those rows close eight times earlier.


Chains are within 10% from 512 bytes a descriptor (the 8-channel chain reads 0.90 at 256 B in Table 6.4.8 but is 0.899) and within 1% from 4 KB on both builds. A single
descriptor per channel pays the firmware's whole per-descriptor cost with nothing to overlap it, so it
needs 8-16 KB to be within 5% and 64-128 KB to be within 1%; 1 MB descriptors are within 0.5% (Table 6.4.3).

At 16 channels each gatling hart serves two channels. That costs one- and two-beat chains (about 99 clocks per descriptor against 44 at 8 channels) and nothing from 16 beats up. The full harness build: rapids-16ch 135,389 LUTs (66.4%) at +0.192 ns, rapids-g-16ch 151,472 LUTs (74.3%) at +0.148 ns; MB/s tables are in the MAS (Section 5.5).

## Area and Timing

| `rapids_core`, out of context | rapids-8ch | rapids-g-8ch | rapids-16ch | rapids-g-16ch |
|---|---:|---:|---:|---:|
| LUTs | 69,184 | 77,975 (+12.7%) | 126,820 | 141,067 (+11.2%) |
| Registers | 56,105 | 58,837 | 101,808 | 104,738 |
| Block RAM tiles | 64 | 70 | 128 | 134 |
| DSPs | 64 | 0 | 128 | 0 |
| WNS at 100 MHz | +0.684 ns | +0.533 ns | +0.079 ns | +0.050 ns |

: Table 6.4.7: rapids_core and rapids_core_g on the xc7k325t-2 (256-bit, shared engines, no AXI monitors, EXT addressing built)

In the full Genesys 2 harness used for Tables 6.4.3 to 6.4.5, rapids-g-8ch takes 111,738 LUTs
(54.8%) and closes 100 MHz at +0.061 ns; rapids-8ch takes 100,007 LUTs at +0.357 ns. The board
tables are unchanged by the 2026-10-23 firmware: its board run is identical to them on every window.

## Related Chapters

- Section 2.3, rapids-g: what changes and what stays the same
- RAPIDS MAS Section 5.5: the measurement history, the bench, verification and the build details
