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

# Error Handling

## Overview

RAPIDS reports errors per channel and per direction. The error classes are
the ones RAPIDS Beats already has, and the byte-granular design adds one:
the packet on the sink stream does not carry the number of bytes the
descriptor asked for. This chapter lists every condition that stops a
channel, how software sees it, and how to recover. It also lists three
conditions that look like errors and are not.

Two facts shape the whole chapter:

1. **A fatal error parks the channel.** The scheduler enters its error
   state and stays there. Only a channel reset or a global reset leaves it.
2. **A channel reset recovers every class.** The scheduler, the descriptor
   and control engines, both data engines and both data paths all take the
   per-channel reset. No error class needs the hardware reset `aresetn`,
   and resetting one channel does not disturb the others.

---

## Error Classes

| Class | Detected by | Fatal to the channel | Sticky until |
|-------|-------------|----------------------|--------------|
| Invalid descriptor (`valid` = 0) | Scheduler, on `CH_FETCH_DESC` | Yes | Channel reset |
| Descriptor address outside both configured ranges | Descriptor engine, before any fetch | Yes | Channel reset |
| Descriptor address of zero or otherwise invalid over APB | Descriptor engine | Yes | Channel reset |
| Descriptor fetch returns an AXI error (`RRESP` not OKAY) | Descriptor engine | Yes | Channel reset |
| Data read returns an AXI error (`RRESP` not OKAY) | AXI read engine | Yes | Channel reset |
| Data write returns an AXI error (`BRESP` not OKAY) | AXI write engine | Yes | Channel reset |
| **Sink packet length mismatch** (new) | Sink ingress, at `tlast` | Yes | Channel reset |
| Control read retry exhausted | Control read engine | Yes | Channel reset |
| Control write returns an AXI error | Control write engine | Yes | Channel reset |
| Write-progress timeout, first windows | Scheduler timeout counter | No | Any write progress |
| Write-progress timeout, escalated | Scheduler timeout counter | Yes | Channel reset |

: Error Classes

The first four rows and the control-engine rows behave exactly as in RAPIDS
Beats. The data-path rows are the same conditions. In RAPIDS the channel
reset also clears them; the "Recovery" section lists what it does to work
still in flight.

---

## The Byte-Granular Error: Packet Length Mismatch

### Contract

A sink descriptor of `length` bytes on a channel promises one AXI-Stream
packet on that channel. The packet is delimited by `tlast`. The number of
valid bytes in the packet, counted from `tstrb`, must equal `length`.

The sink ingress counts the valid bytes of every accepted beat. On the beat
that carries `tlast` it compares the running total, including that beat,
with the byte count in the channel's packet record. If the two differ, the
ingress sets a sticky per-channel bit and raises it on the channel's
`sched_wr_error` line.

| Situation | Result |
|-----------|--------|
| Packet shorter than `length` (early `tlast`) | Error |
| Packet longer than `length` (late `tlast`) | Error |
| Packet equals `length` | No error |
| Descriptor `length` = 0 | No packet record, no packet expected |

: Length Mismatch Cases

The hardware does not pad a short packet and does not drop the extra bytes
of a long one. Nothing is corrected silently. The bytes that were accepted
are still written, so memory that the descriptor covers must not be
trusted after this error.

### Exposure

The mismatch is visible in three places.

| Where | What software sees |
|-------|--------------------|
| `SNK.SCHED_ERROR.SCHED_ERR` | Bit for the channel set. This is the same per-channel bit that reports every fatal scheduler error, so the register does not say which class occurred. |
| MonBus | One error packet per error episode from the channel's scheduler. Its data field carries the sticky write-error flag. |
| Scheduler state | The channel is in its error state, so `SCHEDULER_IDLE.SCHED_IDLE` does not show it idle. |

: Where the Length Mismatch Appears

The error is raised on the sink half only. The source half has no
counterpart: the egress re-packer builds the packet from the descriptor, so
the packet it emits always has `length` bytes.

### How it Clears

The per-channel bit is cleared by the channel reset (and therefore by
the global reset, which asserts every channel's reset). It stays clear
afterwards; the next packet is checked against its own record. See
"Recovery" below for what the reset does to a packet that is part-way
through the stream.

### Prevention

- Issue the sink descriptor for a packet before, or together with, the
  first beat of that packet. The stream waits for the descriptor
  (see "Not Errors" below), so a late descriptor costs time and nothing
  else.
- Set `length` to the exact byte count of the packet. If the length is
  only known at the end of the packet, write the descriptor after the
  length is known.
- Do not split one packet across two descriptors and do not put two
  packets under one descriptor. One descriptor maps to one `tlast`
  delimited packet.

---

## Shared Error Classes

### Invalid or Unfetchable Descriptor

The scheduler leaves `CH_FETCH_DESC` only for a descriptor whose `valid` bit
is set. A descriptor with `valid` = 0 sends the channel to its error state.

The descriptor engine rejects a descriptor fetch whose address falls
outside the two configured address ranges. The rejection happens before
any AXI read is issued. It also reports an error for a fetch address of
zero or otherwise invalid on the APB path, and for an AXI error response
on the fetch itself.

A descriptor whose `length` is zero is not invalid. See "Not Errors".

### Data-Path AXI Errors

The AXI read engine sets a sticky per-channel flag when a data read returns
a response other than OKAY. The AXI write engine does the same for a write
response. Both flags drive the channel's error state.

### Control Engine Errors

A control read that does not match after the configured number of
retries reports an error. Retry exhaustion is what stops a control read
that can never match from hanging the channel. A control write that
returns an AXI error reports an error. Both are fatal to the descriptor
that issued them.

### Write-Progress Timeout

The scheduler counts the cycles in which it holds a write request that the
write engine has not accepted. A write completion or a write commit resets
the count. Its configuration is shared with RAPIDS Beats:

| Register field | Meaning | Default |
|----------------|---------|---------|
| `SCHED_TIMEOUT_CYCLES.TIMEOUT_CYCLES` | Length of one window in cycles | 0x3E8 |
| `SCHED_TIMEOUT_LIMIT.LIMIT` | Consecutive expired windows that escalate to a fatal error. Zero never escalates. | 4 |

: Timeout Configuration

A window that expires is recoverable. Any write progress clears the strike
count. Only the configured number of consecutive expired windows makes the
timeout fatal. A LIMIT of zero keeps the timeout purely advisory. The
timeout is unchanged by the byte-granular design.

---

## Not Errors

Three conditions look like faults and are normal operation.

### Packet Record Queue Full

Each channel keeps a queue of packet records, one per non-zero data
descriptor per enabled direction. The queue holds four records. When it is
full, the scheduler waits in `CH_FETCH_DESC` until a record is consumed.
Software sees the channel busy and nothing else.

No error bit is set and no MonBus error is sent. The timeout counter runs
only while the scheduler holds a write request the write engine has not
accepted, so waiting for a record does not count toward it. Descriptor chains longer than the queue therefore run at
the pace the data paths consume records.

### Sink Beat With No Packet Record

The sink ingress accepts a stream beat for a channel only when that
channel's packet record exists. Until then `s_axis_tready` stays low.

`s_axis_tready` is a single signal. It is qualified by the `tid` of the
beat that is on the bus. A beat for a channel with no record therefore
stalls the whole stream, including beats for other channels that are
queued behind it in the sender. The queues and holds inside RAPIDS are per
channel, so no data is lost or mixed. The cost is delay, and it lands on
every channel that shares the stream.

Two rules keep this delay short:

- Post the sink descriptor for a channel before the sender drives the first
  beat for that channel.
- A sender that interleaves channels on one stream must not assume that a
  waiting channel leaves the others unaffected at the AXI-Stream
  interface.

### The 4 KB Burst Cap

An AXI burst must not cross a 4 KB boundary. The scheduler splits a
transfer at each boundary. A descriptor that spans several pages issues
several bursts, and every burst starts beat-aligned. The split is
invisible to software, and it neither sets a flag nor counts against any
timeout. The cost appears only as throughput, described in the throughput
chapter.

---

## Error Reporting

### Registers

Software finds the failing channel from these fields. All names come from
the shared register map and are the same as in RAPIDS Beats.

| Register field | Use |
|----------------|-----|
| `SRC.SCHED_ERROR.SCHED_ERR` | One bit per channel, source half |
| `SNK.SCHED_ERROR.SCHED_ERR` | One bit per channel, sink half |
| `SCHEDULER_IDLE.SCHED_IDLE` | One bit per channel, set when the scheduler is idle |
| `CHANNEL_RESET.CH_RST` | One bit per channel, resets the scheduler and its engines |
| `GLOBAL_CTRL.GLOBAL_RST` | Resets every channel |
| `GLOBAL_CTRL.GLOBAL_EN` | Global enable |

: Error Registers

The per-channel error bit is the summary of every fatal class in the
"Error Classes" table. It does not name the class. To name the class, read
the MonBus error packet or use the scheduler debug outputs.

### MonBus

The scheduler sends one error packet the first time a channel enters its
error state. It does not repeat the packet on every cycle. The packet
carries the sticky write-error flag and the sticky read-error flag in its
data field. MonBus decoding is described in the shared monitor bus
chapter.

---

## Recovery

### Channel Reset

Writing the channel's bit in `CHANNEL_RESET.CH_RST` of the half that reported
the error, `SNK` or `SRC` (or `GLOBAL_CTRL.GLOBAL_RST` for every channel of
that half), returns the channel to idle. The reset reaches the
scheduler, the descriptor and control engines, the AXI read and write
engines, and the sink and source data paths. Every sticky error flag in
that chain clears, including the data read and write response flags and
the sink packet length flag. Software should:

1. Set the channel's `CH_RST` bit for at least one clock, then clear it.
   A single-cycle pulse and a held level both work. To reset both
   directions of a channel, write both halves.
2. Poll the `SCHED_ERR` bit and the `SCHED_IDLE` bit for the channel. The
   error bit stays clear and the idle bit sets.
3. Rebuild the descriptor chain from a known-good state. Bytes that the
   failed chain already wrote stay in memory.
4. Start the channel again as in the initialization sequence.

This recovers every error class in the "Error Classes" table. No
hardware reset is needed, and the other channels keep running through it.

### What the Reset Does to Work in Flight

A channel reset can arrive with beats, bursts and packets still moving.
The hardware settles them as follows, so the channel is clean when the
reset releases.

| Where | In-flight work | Effect |
|-------|----------------|--------|
| Sink stream, packet already started | Beats of the packet still to come | The ingress accepts and discards them up to and including `tlast`, so the tail of the old packet cannot be taken as the start of the next. The stream does not stall. |
| Sink stream, no packet started | None | Nothing to discard. A beat for the channel is held off while the reset is asserted. |
| Sink write path | An AXI write burst already open | The write engine finishes the burst with null beats (`WSTRB` = 0), so the AXI protocol stays legal and the null beats write nothing. A beat already presented on the write data channel when the reset hit is completed unchanged. No new burst opens for the channel until the open bursts and their responses have finished. Its `AWADDR` value is unchanged. |
| Sink write path | Write responses still due | They are consumed and ignored. A `BRESP` error that arrives after the reset does not set the error flag. |
| Source read path | Read bursts already issued | The read engine issues no further bursts, then drains and discards the returning read data until none is outstanding. A `RRESP` error in that data does not set the error flag. |
| Source stream, packet in progress | Beats not yet sent | The egress stops. A beat already on `m_axis` completes. The remaining beats are not sent (see below). |
| Other channels | Everything | Not affected. The data paths mask only the channel in reset. |

: Channel Reset: Handling of In-Flight Work

The sink ingress discards only the tail of a packet of which at least one
beat had been accepted when the reset hit. The sender must still send that
packet's `tlast`; the beat is taken and dropped, and the next beat for the
channel is checked against the next packet record as usual. While the reset
is asserted the channel's beats are held off (`s_axis_tready` low).

**The source stream is left unterminated.** If the reset lands between
the first and last beat of a source packet, RAPIDS stops sending it and
does not emit a `tlast` (and no null terminator). The receiver sees a
partial packet. A receiver that must resynchronize after a channel reset
should treat the reset as the end of the packet, or flush its own
per-channel state when it resets the channel. A packet that had not
started, or that had already sent its `tlast`, is unaffected.

**Head-of-line blocking is unchanged.** A sink beat for a channel with no
packet record still stalls the shared `s_axis_tready`, as described under
"Not Errors". A channel reset does not remove this. After the reset, post the
next sink descriptor before the sender starts the next packet.

---

## Software Checklist

| Step | Action |
|------|--------|
| Before the run | Program `SCHED_TIMEOUT_CYCLES` and `SCHED_TIMEOUT_LIMIT`. Post the sink descriptor before the first beat of its packet. |
| During the run | Poll `SCHED_ERR` for the active channels, or watch MonBus for error packets. |
| On an error | Note the channel and read the MonBus packet. Decide which class from the descriptor state and the stream. |
| Recovery | Channel reset for every error class, including a length mismatch or an AXI response error. |
| After recovery | Re-post descriptors. Re-send the whole packet, not the tail. A source receiver discards the partial packet of a reset channel. |

: Software Checklist

---

## Related Chapters

- [Descriptor Format](01_descriptor_format.md): the byte `length`, the
  packet record and the zero-length rule.
- [Register Map](../../rapids_beats_has/ch05_programming/02_register_map.md):
  the shared register layout.
- [Monitor Bus Interface](../../rapids_beats_has/ch03_interfaces/05_monbus_interface.md):
  the error packet format.
