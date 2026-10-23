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

**Last Updated:** 2026-10-22

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
| 16 channels | rapids-16ch; rapids-g-16ch when DSPs are short or for large descriptors | rapids-g-16ch is within 0.4% at 1 MB and 3% at 64 KB, but its per-descriptor cost doubles at 16 channels (Table 6.4.6); it saves 128 DSPs for 11% more LUTs |
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
| 16 one-beat descriptors, one channel | 131 | 2,371 | 131 | 2,859 |
| 16 64-beat descriptors on each channel | 1,255 | 2,389 | 1,255 | 4,957 |
| 4 64 KB descriptors on each channel | 9,248 | 9,412 | 9,248 | 9,553 |
| 2 1 MB descriptors on each channel | 84,277 | 84,443 | 84,277 | 84,580 |
| EXT, runs of 4, 64 beats, 4 per channel | 407 | 39,201 | 407 | 76,862 |
| EXT, per beat, 64 beats, 4 per channel | 1,043 | 130,086 | 1,043 | 253,623 |
| EXT, runs of 256, 1 MB, 1 per channel | 29,574 | 70,641 | 29,574 | 137,624 |

: Table 6.4.6: Cycles to finish, schedulers alone (lower is better)

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
