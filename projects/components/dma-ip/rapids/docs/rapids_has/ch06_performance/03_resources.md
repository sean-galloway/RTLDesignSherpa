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

# Resource Estimates

The figures in this chapter are measured. They come from the placed and
routed board build of the byte-granular RAPIDS on the Genesys 2, not from
an estimate. The chapter states the configuration first because every number
depends on it.

## Build Configuration

| Item | Value |
|------|-------|
| Top level | `rapids_byte_genesys2_top` (RAPIDS plus the characterization harness) |
| Device | `xc7k325tffg900-2` (Kintex-7 325T) |
| Tool | Vivado 2025.1, design state Physopt postRoute |
| Clock | 100 MHz |
| Channels | 8, on both the sink and the source half |
| Data width | 256 bits (32-byte beats) |
| Buffer depth | 128 entries per channel, 4 KB per channel |
| Interface observers | On |
| AXI monitors | Off |

: Board Build Configuration

The measured design includes the characterization harness: the UART bridge,
the pattern generators, the byte checkers and the bus meters. The figures are
therefore an upper bound for RAPIDS alone. The harness is not separated in
the reports.

## FPGA Resource Summary

Source: `projects/fpga-systems/Genesys2/dma-ip/rapids/reports/perf/json/rapids_byte_build_bytecrc.json` and `rapids_byte_build_wordcrc.json`, extracted from the post-route reports by `reports/extract_build_metrics.py`.

The harness has two checker builds. `BYTE_CRC=1` is the standard bitstream:
the byte-wise CRC checkers take 9 cycles per 32-byte beat and verify every
byte and strobe. `BYTE_CRC=0` is a measurement bitstream with word-wide
checkers that take one beat per cycle, so the harness does not cap the
measured rate.

| Resource | Standard (BYTE_CRC=1) | Word-wide (BYTE_CRC=0) | Available |
|----------|-----------------------|------------------------|-----------|
| Slice LUTs | 92,874 (45.57 %) | 86,065 (42.23 %) | 203,800 |
| LUT as logic | 81,352 | 75,695 | 203,800 |
| LUT as distributed RAM | 11,522 | 10,370 | 64,000 |
| Slice registers | 82,379 (20.21 %) | 79,527 (19.51 %) | 407,600 |
| F7 muxes | 4,709 | 4,430 | 101,900 |
| F8 muxes | 106 | 107 | 50,950 |
| Block RAM tiles | 68 (15.28 %) | 52 (11.69 %) | 445 |
| DSP | 0 | 0 | 0 |

: Post-Route Utilization, 8 Channels, 256 Bits

All block RAM tiles are RAMB36E1. No RAMB18 is used, and no register is a
latch. DSP use is zero because RAPIDS moves data and performs no
multiply-accumulate. The 16 tiles and about 6,800 LUTs that the word-wide
build saves are the byte checkers' golden storage and CRC logic, which belong
to the harness and not to RAPIDS.

## Timing

Source: the same two build JSONs.

| Metric | Standard (BYTE_CRC=1) | Word-wide (BYTE_CRC=0) |
|--------|-----------------------|------------------------|
| Worst negative slack, setup | +0.301 ns | +0.077 ns |
| Total negative slack | 0.000 ns | 0.000 ns |
| Worst hold slack | +0.023 ns | +0.013 ns |
| Failing endpoints | 0 of 320,415 | 0 of 301,738 |

: Timing at 100 MHz

All user timing constraints are met in both builds. The slack is small and
positive; treat 100 MHz as the design point and not as a margin.

## Board Result

On the standard bitstream (sha256 `cfad34c3...`) the byte-wise campaign passes
117 of 117 points and the directed sequences 4 of 4. On the word-wide
bitstream (sha256 `48e1282c...`) the beat-aligned profile passes 28 of 28
points and reaches 3182 MB/s on the sink and 3199 MB/s on the source at 8
channels and 4096 beats, against a theoretical peak of 3200 MB/s (100 MHz x 32
bytes). The word-wide checker CRCs only slice 0 of each beat and ignores
strobes, so it is compared with the beats golden; byte-level integrity comes
from the byte-wise campaign. Both runs are in the throughput chapter and the
characterization report (`reports/perf/README.md`, v0.2).

## Comparison with the Beats Build

The RAPIDS Beats performance report lists the resources of its 256-bit build
in its version 2.0 text. Both builds run 8 channels at 100 MHz on the same
device with a buffer of 128 entries per channel.

| Item | RAPIDS Beats, 256-bit, v2.0 | RAPIDS, byte-granular (standard build) |
|------|-----------------------------|-----------------------|
| Slice LUTs | 75,679 | 92,874 |
| Block RAM tiles | 44 | 68 |
| Worst negative slack | +0.608 ns | +0.301 ns |

: Beats and Byte-Granular Builds

The columns are not a like-for-like comparison of the two designs. The two
bitstreams come from different versions of the RTL and the harness. The
byte checkers and the byte-wise golden logic are in the byte build and not
in the beats build. The beats build has since been rebuilt, and the v2.2 beats
report header gives a slack of +0.286 ns for it and no new resource counts.
Use the table as a size comparison of two board images, and not as the cost of
byte granularity.

## What Depends on What

The reports do not break the design down by block, and this chapter does not
invent a breakdown. The relationships that follow from the design are these.

| Change | Effect |
|--------|--------|
| Channels 8 to fewer | Scheduler, descriptor and buffer resources scale with channel count |
| Buffer depth | Block RAM scales with entries per channel, per direction, and with the entry width |
| Data width | Datapath logic and buffer width scale with it. The line rate scales with it. |
| Interface observers off | Removes the observer logic and its histograms |
| AXI monitors on | Adds monitor logic. They are off in this build. |

: Scaling Notes

The sink buffer entry is `DATA_WIDTH + DATA_WIDTH / 8` bits wide, because
each entry stores the byte enables beside the data. The source buffer entry
stays `DATA_WIDTH` bits. The byte-granular sink therefore stores a wider
entry than the beats sink for the same depth and width.

The byte-granular design adds per-channel state that the beats design lacks:
a packet-record queue four deep, a sink spill register, an ingress packet byte
counter and, on the source half, the re-pack hold register. The reports do not
isolate their cost.

---

## Related Chapters

- [Throughput](01_throughput.md): the measured campaign and the beats report.
- [Error Handling](../ch05_programming/04_error_handling.md): the reset
  behavior of the sticky flags.
