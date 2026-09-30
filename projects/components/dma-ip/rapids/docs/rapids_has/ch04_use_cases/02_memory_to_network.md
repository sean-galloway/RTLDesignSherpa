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

# Use Case: Memory-to-Network Transfer

## Scenario

RAPIDS reads `L` bytes from system memory starting at the byte address `A`
named by the channel's descriptor and emits them on the source AXI-Stream as
one packed packet. The read may start anywhere in a beat. The stream carries
only the requested bytes: the first stream beat starts at lane 0 with byte `A`,
and `TLAST` marks the descriptor's last byte.

The examples use a 256-bit data path (32 byte lanes, the Genesys 2
configuration).

## Sequence

| Step | Actor | Action |
|------|-------|--------|
| 1 | Software | Builds a descriptor: source byte address `A`, length `L` in bytes, the channel's source direction enabled ([Descriptor Format](../ch05_programming/01_descriptor_format.md)) |
| 2 | Software | Kicks the channel |
| 3 | Scheduler | Computes the beat count and hands the source data path a packet record: `{bytes = L, offset = A mod 32}` |
| 4 | Source AXI master | Reads whole aligned beats as AXI4 read bursts, never crossing 4 KB, into the channel's SRAM partition |
| 5 | Source egress | Pops beats from the SRAM and shifts them down by the offset. The first pop only primes the shifter |
| 6 | Source egress | Emits packed stream beats with `TID` = `TDEST` = channel; the last beat carries a contiguous `TSTRB` and `TLAST` |
| 7 | Scheduler | When the packet has left, completes the descriptor and reports it on the MonBus |

: Memory-to-Network Sequence

Unlike the sink, the source needs no ordering rule against the network: the
record is created before any read data is requested, so the egress always
knows the packet length.

## Worked Example 1: 77 Bytes at Offset 5

Source `A` = `base + 5` with `base` beat-aligned, `L` = 77.

| Quantity | Value |
|----------|-------|
| Offset | 5 |
| Memory beats read | (5 + 77 + 31) >> 5 = 3 |
| Stream beats | 3: 32, 32 and 13 bytes |
| Last stream beat `TSTRB` | `0x00001FFF` |

: Example 1 Quantities

The read master issues one burst of three beats at `base`. The egress then
works as follows:

| Memory beat popped | Output |
|--------------------|--------|
| M0 | None. Bytes 5 to 31 are held: 27 bytes |
| M1 | Stream beat 0: the 27 held bytes plus bytes 0 to 4 of M1, `TSTRB` = `0xFFFFFFFF` |
| M2 | Stream beat 1: bytes 5 to 31 of M1 plus bytes 0 to 4 of M2, `TSTRB` = `0xFFFFFFFF` |
| (flush) | Stream beat 2: the remaining 13 bytes, `TSTRB` = `0x00001FFF`, `TLAST` |

: Example 1 Egress Steps

The stream carries 32 + 32 + 13 = 77 bytes as one packet.

## Worked Example 2: 4035 Bytes Crossing a 4 KB Boundary

Source `A` = `0x0CB`, `L` = 4035.

| Quantity | Value |
|----------|-------|
| Offset | 11 |
| Memory beats read | 127 |
| Beats before the 4 KB boundary | 122 |
| Beats after the boundary | 5 |
| Stream beats | 127: 126 full beats and a last beat of 3 bytes |
| Last stream beat `TSTRB` | `0x00000007` |

: Example 2 Quantities

The read master splits at `0x1000`: one burst of up to 122 beats from `0x0C0`
and one of 5 beats from `0x1000`, further split if the configured read burst
limit (`RD_XFER_BEATS`) is smaller. The egress removes the 11 leading bytes
and delivers 4035 bytes as one packet with a single `TLAST`, however many
drain blocks and read bursts the transfer spanned. RAPIDS Beats asserted
`TLAST` at the end of every drain block; RAPIDS does not.

## Errors

| Condition | Result |
|-----------|--------|
| Read response is not OKAY | Channel's read error is reported ([Error Handling](../ch05_programming/04_error_handling.md)) |
| Zero-length descriptor | No record and no packet |

: Memory-to-Network Error Cases

## Related Chapters

- [Descriptor Chaining](../../rapids_beats_has/ch04_use_cases/03_descriptor_chaining.md), shared with RAPIDS Beats
- [Multi-Channel Operation](../../rapids_beats_has/ch04_use_cases/04_multi_channel.md), shared with RAPIDS Beats
