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

# MonBus Event Emission Points

## Packet Format

`amber_monlite` emits standard 128-bit MonBus packets plus a 64-bit side-band timestamp. The packet layout is the house `monitor_common_pkg` spec; the timestamp is sampled at the same cycle as the packet and held stable while `mon_valid` is high.

## Emission Timing

Events are emitted as one-cycle pulses. The event class and payload are captured combinatorially from the control FSM state and registered at the emission point to avoid glitches.

| Event class | Emit point | Payload |
|-------------|------------|---------|
| hit | `CTRL_HIT_RD` / `CTRL_HIT_WR` | set, way, state before/after |
| miss | `CTRL_MISS_VICTIM` | set, way, miss class |
| snoop | AC handshake accepted | snoop type, hit/miss flag |
| eviction | `CTRL_MISS_DRAIN` start | clean/dirty, set, way |
| MESI transition | tag-array state write | old state, new state, cause code |
| fill_start | `CTRL_MISS_FILL` | line address |
| fill_end | `CTRL_FILL_WRITE` | line address |
| drain_start | `CTRL_MISS_DRAIN` | line address |
| drain_end | `drain_done` | line address |

## Drop-and-Count

If `mon_ready` is low when `mon_valid` would assert, the packet is dropped and a saturating drop counter increments. The counter is reported as an `EVENT_DROPPED` packet when MonBus next has room. This is identical to the STREAM monitor-lite behavior and never stalls the observed path.

## Backpressure Integrity

`amber_monlite` is a pure observer. Its FIFO state never gates the CPU GAXI port, the AXI4/ACE masters, or the snoop responder. This is the measurement-integrity rationale that chose `*_monlite` over the heavyweight `_mon` wrappers.

---

**Last Updated:** 2026-10-06
