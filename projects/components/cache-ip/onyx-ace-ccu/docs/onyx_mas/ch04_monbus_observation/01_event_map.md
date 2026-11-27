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

# Event Classes and Payloads

**RTL:** `onyx_pkg.sv:20-50` (codes, ids), `onyx_monlite.sv:286-347`
(classes and payloads).

Every packet is a 128-bit house MonBus packet built by
`create_monitor_packet` (`ocelus_common_pkg`) with protocol `PROTOCOL_CORE`,
agent `ONYX_AGENT_ID = 16'h00A3`, unit `ONYX_UNIT_ID = 8'h01`, and a 64-bit
data field. Event packets are `PktTypePerf`; the drop report is
`PktTypeError`. The timestamp is `i_mon_time` at the cycle the packet
enters the output queue, carried beside the packet (`mon_timestamp`).

The codes start at `0x20`: the caches' `l1_monlite` uses `0x00`-`0x09` and
jet's monlite `0x10`-`0x16`, so one tally profile holds all three agents.

## Classes

| Code | Class | Source tap | Data field (bits of the 64-bit payload) |
|---|---|---|---|
| `0x20` | `TXN_START` | `evt_grant` | `[RQ_W-1:0]` requester; `[7:5]` class; `[15:8]` slot |
| `0x21` | (retired: `SNOOP_OUT`) | - | it was `TXN_START` times the peer count |
| `0x22` | `GATHER_DONE` | `evt_gather[p]` | `[7:0]` slot; `[8]` DataTransfer; `[9]` PassDirty; `[15:12]` answering port; `[31:16]` cycles from the grant (`i_mon_time` minus the slot's grant time, 16 bits) |
| `0x23` | `MEM_READ` | `evt_mem_ar` | `[7:0]` slot |
| `0x24` | `READ_WASTED` | `evt_read_wasted[p]` | `[15:12]` answering port |
| `0x25` | `ABSORB` | `evt_absorb` | `[7:0]` slot |
| `0x26` | `WRITEBACK` | `evt_wb` | `[RQ_W-1:0]` requester: `N_PORTS` for the IO's write, 0 for a cache write-back |
| `0x27` | `LOCK_WAIT` | `evt_lock_wait[d]` episodes | `[RQ_W-1:0]` requester; `[23:8]` the episode's duration in cycles, saturating at `0xFFFF` |
| `AMBER_EV_DROPPED` (`0x09`) | drop report (`PktTypeError`) | the drop count | `[7:0]` events lost since the last report |

: Table 4.1: onyx MonBus event classes

The IO's grant classes ride `TXN_START`'s class field in the `l1_pkg`
code space: 7 for an IO read (unused by `l1_pkg`), 5 for an IO write
(`EVICT`, which never allocates); the requester field `N_PORTS`
disambiguates in any case.

## Class instances

A class fires at most once a cycle, and the per-port taps can fire on
several ports at once, so the observer keeps one class instance per
port for the per-port events:

```
instances 0 .. N_PORTS-1            GATHER_DONE, answering port p
instances N_PORTS .. 2*N_PORTS-1    READ_WASTED, answering port p
2*N_PORTS + 0..4                    MEM_READ, TXN_START, ABSORB, WRITEBACK, LOCK_WAIT
```

`N_CL = 2 * N_PORTS + 5` instances (9 at two ports, 13 at four),
`onyx_monlite.sv:293-295`.

## Supporting state in the observer

- **Grant time per slot** (`r_grant_cyc[SLOTS]`): `i_mon_time` at each
  grant, for `GATHER_DONE`'s latency.
- **Lock-wait episodes per requester** (`onyx_monlite.sv:221-284`): an
  episode starts the first cycle `evt_lock_wait[d]` is high (duration 1,
  the window bit latched from the waiting address), counts while it stays
  high, and is released the first cycle it is low. One release is emitted
  a cycle, lowest requester first; a release not emitted parks in
  `r_lw_pend[d]` with its duration and emits in a later cycle.

## What the counts mean

HAS Chapter 4.4 reads them (the D6 trade from `MEM_READ`, `GATHER_DONE`
with DataTransfer and `READ_WASTED`; the serialization cost from
`LOCK_WAIT`). The exact counts are the counters' (ch04/03); the MonBus
gives them shape in time and may drop.
