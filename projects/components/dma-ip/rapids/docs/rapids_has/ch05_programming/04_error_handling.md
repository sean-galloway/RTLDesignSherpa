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
2. **Some sticky flags outlive a channel reset.** The three data-path flags
   listed under "Recovery" clear only on the hardware reset `aresetn`.
   Software cannot recover from these by channel reset alone.

---

## Error Classes

| Class | Detected by | Fatal to the channel | Sticky until |
|-------|-------------|----------------------|--------------|
| Invalid descriptor (`valid` = 0) | Scheduler, on `CH_FETCH_DESC` | Yes | Channel reset |
| Descriptor address outside both configured ranges | Descriptor engine, before any fetch | Yes | Channel reset |
| Descriptor address of zero or otherwise invalid over APB | Descriptor engine | Yes | Channel reset |
| Descriptor fetch returns an AXI error (`RRESP` not OKAY) | Descriptor engine | Yes | Channel reset |
| Data read returns an AXI error (`RRESP` not OKAY) | AXI read engine | Yes | `aresetn` |
| Data write returns an AXI error (`BRESP` not OKAY) | AXI write engine | Yes | `aresetn` |
| **Sink packet length mismatch** (new) | Sink ingress, at `tlast` | Yes | `aresetn` |
| Control read retry exhausted | Control read engine | Yes | Channel reset |
| Control write returns an AXI error | Control write engine | Yes | Channel reset |
| Write-progress timeout, first windows | Scheduler timeout counter | No | Any write progress |
| Write-progress timeout, escalated | Scheduler timeout counter | Yes | Channel reset |

: Error Classes

The first four rows and the control-engine rows behave exactly as in RAPIDS
Beats. The data-path rows are the same conditions, with one difference in
the last column that the "Recovery" section explains.

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

The per-channel bit is reset by `aresetn` and by nothing else. The sink
ingress has no channel-reset input. See "Recovery" below for what this
means for software.

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

Writing the channel's bit in `CHANNEL_RESET.CH_RST` returns the scheduler
to idle and clears the descriptor engine and the control engines. Software
should:

1. Set the channel's `CH_RST` bit for at least one clock, then clear it.
2. Poll the `SCHED_ERR` bit and the `SCHED_IDLE` bit for the channel.
3. Rebuild the descriptor chain from a known-good state. Bytes that the
   failed chain already wrote stay in memory.
4. Start the channel again as in the initialization sequence.

This recovers the descriptor errors, the control-engine errors and an
escalated timeout.

### Errors That Survive Channel Reset

Three flags are sticky in the data path and clear only on `aresetn`:

| Flag | Set by |
|------|--------|
| Read engine error, per channel | A data read response that is not OKAY |
| Write engine error, per channel | A data write response that is not OKAY |
| Packet length error, per channel | A mismatch at `tlast` on the sink stream |

: Data-Path Flags That Clear on aresetn Only

Neither data engine, and not the sink ingress, takes a channel-reset input. Each
flag feeds the scheduler as a level. The scheduler's own sticky copy clears
when the scheduler reaches idle, and the level sets it again on the next
cycle. After a channel reset or a global reset the scheduler therefore
returns to its error state as soon as reset is released, and
`SCHED_ERR` reads set again.

Software that meets one of these three errors has two options:

- Reset the whole block through the hardware reset that drives `aresetn`,
  then reprogram it.
- Treat the failing channel as lost until the next hardware reset, and
  keep using the other channels. The error bits are per channel, so the
  other channels keep running.

This behavior is the current RTL. A change that routes the channel reset
into the two engines and the sink ingress would let a channel reset clear
them, and this chapter would then move the three rows into the previous
section.

---

## Software Checklist

| Step | Action |
|------|--------|
| Before the run | Program `SCHED_TIMEOUT_CYCLES` and `SCHED_TIMEOUT_LIMIT`. Post the sink descriptor before the first beat of its packet. |
| During the run | Poll `SCHED_ERR` for the active channels, or watch MonBus for error packets. |
| On an error | Note the channel and read the MonBus packet. Decide which class from the descriptor state and the stream. |
| Recovery | Channel reset for descriptor, control and timeout errors. Hardware reset for a length mismatch or an AXI response error. |
| After recovery | Re-post descriptors. Re-send the whole packet, not the tail. |

: Software Checklist

---

## Related Chapters

- [Descriptor Format](01_descriptor_format.md): the byte `length`, the
  packet record and the zero-length rule.
- [Register Map](../../rapids_beats_has/ch05_programming/02_register_map.md):
  the shared register layout.
- [Monitor Bus Interface](../../rapids_beats_has/ch03_interfaces/05_monbus_interface.md):
  the error packet format.
