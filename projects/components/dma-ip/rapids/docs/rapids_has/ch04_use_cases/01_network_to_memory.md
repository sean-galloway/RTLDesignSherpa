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

# Use Case: Network-to-Memory Transfer

## Scenario

A network agent delivers a packet of `L` bytes on the sink AXI-Stream. RAPIDS
writes exactly those bytes to system memory starting at the byte address `A`
named by the channel's descriptor. The packet may start anywhere in a beat, and
the bytes before `A` and after `A + L - 1` in the boundary beats are left
untouched.

The examples use a 256-bit data path (32 byte lanes, `DATA_WIDTH` = 256, the
Genesys 2 configuration). Byte lanes are numbered 0 to 31.

## Sequence

| Step | Actor | Action |
|------|-------|--------|
| 1 | Software | Builds a descriptor: destination byte address `A`, length `L` in bytes, and the channel's sink direction enabled ([Descriptor Format](../ch05_programming/01_descriptor_format.md)) |
| 2 | Software | Kicks the channel so the descriptor engine fetches the descriptor |
| 3 | Scheduler | Computes the beat count and hands the sink data path a packet record: `{bytes = L, offset = A mod 32}` |
| 4 | Network agent | Streams the packet on `s_axis_*` with `TID` = channel. `TREADY` rises once the record exists |
| 5 | Sink ingress | Shifts each packed stream beat up by the offset and writes memory-aligned beats, with byte enables, into the channel's SRAM partition |
| 6 | Sink AXI master | Drains the SRAM as AXI4 write bursts, never crossing 4 KB, with `WSTRB` from the stored byte enables |
| 7 | Sink ingress | At `TLAST`, compares the packet's byte count with `L`; a mismatch sets the channel's sticky write-error flag |
| 8 | Scheduler | On the last write response, completes the descriptor and reports it on the MonBus |

: Network-to-Memory Sequence

### Ordering Rule

Issue the descriptor before the packet arrives, or stream one channel at a time.
`s_axis_tready` is one signal and it stays low for a beat whose channel has no
packet record yet. Until that record exists the whole stream is held, including
beats for other channels queued behind it. See
[AXIS Interface](../ch03_interfaces/03_axis_interface.md).

## Worked Example 1: 77 Bytes at Offset 5

Destination `A` = `base + 5`, where `base` is beat-aligned, and `L` = 77.

| Quantity | Value |
|----------|-------|
| Offset | 5 |
| Beats written | (5 + 77 + 31) >> 5 = 3 |
| Stream beats | 3: 32, 32 and 13 bytes |
| Last stream beat `TSTRB` | `0x00001FFF` |

: Example 1 Quantities

| Memory beat | Address | Lanes written | Bytes | `WSTRB` |
|-------------|---------|---------------|-------|---------|
| 0 | `base` | 5 to 31 | 27 | `0xFFFFFFE0` |
| 1 | `base + 32` | 0 to 31 | 32 | `0xFFFFFFFF` |
| 2 | `base + 64` | 0 to 17 | 18 | `0x0003FFFF` |

: Example 1 Write Beats

The three beats carry 27 + 32 + 18 = 77 bytes. Stream byte 0 lands in lane 5 of
the first memory beat. The five bytes that do not fit in that beat are held and
join the next one, so each memory beat is assembled from two neighboring stream
beats. The 13 bytes of the last stream beat plus the five held bytes fill lanes
0 to 17 of the last memory beat, so no extra flush beat is needed.

The write is one AXI4 burst of three beats at `base`. `AxADDR` is the aligned
address and `AxSIZE` is the full 32-byte beat.

## Worked Example 2: 4035 Bytes Crossing a 4 KB Boundary

Destination `A` = `0x0CB` (byte address within a 4 KB page), `L` = 4035.

| Quantity | Value |
|----------|-------|
| Offset | `0x0CB` mod 32 = 11 |
| Aligned start | `0x0C0` |
| Beats written | (11 + 4035 + 31) >> 5 = 127 |
| Beats before the 4 KB boundary | (`0x1000` - `0x0C0`) / 32 = 122 |
| Beats after the boundary | 5 |
| First beat `WSTRB` | lanes 11 to 31, `0xFFFFF800` |
| Last beat | at `0x1080`, lanes 0 to 13, `WSTRB` = `0x00003FFF` |

: Example 2 Quantities

The 127 beats hold 21 + 125 x 32 + 14 = 4035 bytes. The sink write master
cannot issue one 127-beat burst, because it would cross `0x1000`. It splits at
the boundary:

| Burst | `AWADDR` | Beats |
|-------|----------|-------|
| 1 | `0x0C0` | up to 122 |
| 2 | `0x1000` | 5 |

: Example 2 Write Bursts

If the configured write burst limit (`WR_XFER_BEATS`) is below 122, burst 1 is
itself split; the 4 KB cap and the configured limit are combined and the
smaller wins. After the first burst the address continues from the aligned
address plus the beats already written.

## Errors

| Condition | Result |
|-----------|--------|
| Packet byte count differs from `L` | Channel's sticky write-error flag is set and stays set until reset ([Error Handling](../ch05_programming/04_error_handling.md)) |
| Write response is not OKAY | AXI write error is reported through the same flag |
| Zero-length descriptor | No record, no packet expected, nothing written |

: Network-to-Memory Error Cases

## Related Chapters

- [Descriptor Chaining](../../rapids_beats_has/ch04_use_cases/03_descriptor_chaining.md), shared with RAPIDS Beats
- [Multi-Channel Operation](../../rapids_beats_has/ch04_use_cases/04_multi_channel.md), shared with RAPIDS Beats
