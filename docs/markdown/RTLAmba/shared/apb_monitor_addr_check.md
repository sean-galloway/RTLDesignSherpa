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

# APB Monitor Address-Range Checker

**Module:** `apb_monitor_addr_check.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The APB Monitor Address-Range Checker is a configurable N-range address-violation filter for the APB monitor pipeline. It is the APB mirror of `axi_monitor_addr_check`: it watches the `cmd_valid`/`cmd_ready` handshake the `apb_monitor` already snoops, and when an accepted command's `paddr` falls inside any of N configured `[low, high]` inclusive ranges it emits a `PktTypeError` MonBus packet with event code `APB_ERR_ADDR_RANGE` (`8'h08`).

### Key Features

- Up to N configurable inclusive `[low, high]` address ranges (default 4, up to 16 usable via the 4-bit range index)
- Per-range enable plus a global `cfg_addr_check_enable`
- Emits a standard MonBus error packet with the offending address, range index, and direction
- Preserves an `is_read` bit (APB has no separate AR/AW channels, so direction must be carried explicitly)
- Per-range pending mask latches hits and drains them one packet at a time under backpressure
- Side-band timestamp captured from the broadcast free-running counter on emission
- Exact-match support by setting a range's `low == high`

---

## Module Purpose

APB peripherals frequently have reserved or protected address windows that software must never touch. This checker gives the APB monitor an inexpensive, fully-configurable way to flag such accesses in-band on the MonBus, without adding logic to the APB datapath itself. It snoops the same command handshake the monitor already observes, compares the accepted address against a set of programmable ranges, and reports a violation packet identifying which range was hit, the offending address, and whether the access was a read or a write.

**Use Cases:**
- Flagging accesses to reserved/protected APB register windows
- Security or safety guard-banding of peripheral address maps
- Debug tripwires on unexpected address regions during bring-up
- Exact-address watchpoints (set `low == high`)

**Key Benefit:** Programmable, per-range address-violation reporting on the MonBus that mirrors the AXI variant while carrying the APB-specific read/write direction bit.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N_ADDR_RANGES | int | 4 | Number of configurable `[low, high]` ranges |
| ADDR_WIDTH | int | 32 | APB address width |
| UNIT_ID | logic [7:0] | 8'h00 | Unit id stamped into emitted packets |
| AGENT_ID | logic [15:0] | 16'h0000 | Agent id stamped into emitted packets |
| M | int | ADDR_WIDTH | Internal address-width alias |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk | input | 1 | Clock |
| aresetn | input | 1 | Active-low asynchronous reset |

### Timestamp

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_mon_time | input | monbus_timestamp_t | Free-running counter broadcast by the monbus_group family; sampled on emission |

### Snooped APB Command Stream

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cmd_paddr | input | M | Command address (APB `paddr`) |
| cmd_pwrite | input | 1 | Command direction (1 = write, 0 = read) |
| cmd_valid | input | 1 | Command valid (from the monitor's snoop of the APB handshake) |
| cmd_ready | input | 1 | Command ready; `valid && ready && enable` marks an accepted command |

### Range Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_addr_check_enable | input | 1 | Global enable for the checker (also gates output valid) |
| cfg_addr_range_enable | input | N_ADDR_RANGES | Per-range enable mask |
| cfg_addr_range_low | input | N_ADDR_RANGES × M | Per-range inclusive lower bound |
| cfg_addr_range_high | input | N_ADDR_RANGES × M | Per-range inclusive upper bound |

### Outgoing MonBus Packet

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| addr_pkt_valid | output | 1 | Packet valid (a pending violation is ready to emit) |
| addr_pkt_ready | input | 1 | Downstream ready; `valid && ready` accepts the packet |
| addr_pkt_data | output | monitor_packet_t | Assembled MonBus error packet |
| addr_pkt_timestamp | output | monbus_timestamp_t | Timestamp side-band (`i_mon_time`) |

---

## Functional Description

### Combinational Range Hits

A command "fires" when `cmd_valid && cmd_ready && cfg_addr_check_enable`. For each range `i`, a one-hot hit is asserted when the range is enabled, the command fires, and `cmd_paddr` lies within `[cfg_addr_range_low[i], cfg_addr_range_high[i]]` inclusive. Setting a range's low and high equal yields exact-match (watchpoint) semantics.

### Pending Mask and Latched Snapshot

Each range has a pending bit. On a hit, the range's pending bit sets and its address and direction are latched (`r_lat_addr[i] = cmd_paddr`, `r_lat_is_read[i] = !cmd_pwrite`). This decouples detection from emission so a violation is not lost while the MonBus is backpressured. A first-match priority encoder over `r_pending` selects the range to emit (`emit_oh` / `emit_idx`); `addr_pkt_valid` asserts when any range is pending and the checker is enabled. When the packet is accepted (`addr_pkt_valid && addr_pkt_ready`), the emitted range's pending bit clears. If a fresh hit and an accept collide on the same range in one cycle, the hit wins (the pending bit stays set), so a back-to-back violation is not dropped.

### Packet Encoding

The emitted packet is the standard 128-bit MonBus format with a 64-bit `event_data` field, assembled via `create_monitor_packet`:

- **packet_type** = `PktTypeError` (`4'h0`)
- **protocol** = `PROTOCOL_APB` (`4'h2`)
- **event_code** = `APB_ERR_ADDR_RANGE` (`8'h08`)
- **channel_id** = 0 (APB has no ID concept)
- **unit_id** = `UNIT_ID`, **agent_id** = `AGENT_ID`
- **event_data[63:60]** = range index (4 bits → up to 16 ranges)
- **event_data[59]** = `is_read` (1 = read, 0 = write)
- **event_data[58:0]** = offending `cmd_paddr` (zero-padded if `M < 59`, or its low 59 bits if `M >= 59`)

### The is_read Carve-Out

The AXI variant drops the direction bit because AR and AW are separate channels — direction is implied by which monitor (read vs write) emitted the packet. APB has no such split: the same monitor sees both directions, so this block preserves an explicit `is_read` bit (carved out of the 60-bit address slot) so consumers can disambiguate read from write.

### Timestamp Side-Band

Exactly as in the AXI variant, `i_mon_time` (the free-running counter broadcast by the `monbus_group` family) is driven straight out on `addr_pkt_timestamp`, so the consuming group can stamp the violation with a bus-consistent time.

---

## Usage Example

```systemverilog
// Guard two reserved APB windows; report violations on the MonBus.
apb_monitor_addr_check #(
    .N_ADDR_RANGES  (4),
    .ADDR_WIDTH     (32),
    .UNIT_ID        (8'h10),
    .AGENT_ID       (16'h0001)
) u_apb_addr_check (
    .clk                    (pclk),
    .aresetn                (presetn),
    .i_mon_time             (mon_time),         // from the monbus group

    // Snooped APB command handshake (from apb_monitor)
    .cmd_paddr              (apb_paddr),
    .cmd_pwrite             (apb_pwrite),
    .cmd_valid              (cmd_valid),
    .cmd_ready              (cmd_ready),

    // Range config (range 0 = a window, range 1 = an exact watchpoint)
    .cfg_addr_check_enable  (1'b1),
    .cfg_addr_range_enable  (4'b0011),
    .cfg_addr_range_low     ('{32'h0000_1000, 32'h0000_2000, 32'h0, 32'h0}),
    .cfg_addr_range_high    ('{32'h0000_1FFF, 32'h0000_2000, 32'h0, 32'h0}),

    // MonBus output (connect to the group's error-drain path)
    .addr_pkt_valid         (addr_pkt_valid),
    .addr_pkt_ready         (addr_pkt_ready),
    .addr_pkt_data          (addr_pkt_data),
    .addr_pkt_timestamp     (addr_pkt_timestamp)
);
```

---

## Design Notes

### Mirror of the AXI Variant

The block is a deliberate mirror of `axi_monitor_addr_check` so the two share timestamp handling, the pending-mask/priority-encoder emission structure, and the range-index/address packet layout. The only intentional divergence is the preserved `is_read` bit.

### Backpressure Safety

Detection latches into `r_pending` and emission drains one range per accepted packet, so violations survive downstream backpressure. The hit-versus-accept collision rule keeps the pending bit set when a new hit lands on a range being drained the same cycle.

### Address Field Width

For `ADDR_WIDTH >= 59` the low 59 bits of the address are carried; for narrower buses the address is zero-extended into the 59-bit payload slot. The upper four `event_data` bits are always the range index.

### Exact-Match Watchpoints

Program `cfg_addr_range_low[i] == cfg_addr_range_high[i]` to turn a range into a single-address watchpoint.

---

## Related Modules

### Used By
- `apb_monitor` pipeline (address-range violation reporting)

### Uses
- **monitor_common_pkg** - `PktTypeError`, `PROTOCOL_APB`, `monbus_timestamp_t`, `create_monitor_packet`
- **monitor_amba4_pkg** - `APB_ERR_ADDR_RANGE` event code
- **reset_defs.svh** - `ALWAYS_FF_RST` / `RST_ASSERTED` reset macros

### See Also
- **axi_monitor_addr_check.sv** - AXI-side equivalent (no `is_read` bit)
- **apb_monitor.sv** - The APB monitor this checker plugs into

---

## References

### Source Code
- RTL: `rtl/amba/shared/apb_monitor_addr_check.sv`

### Documentation
- Packet format: `docs/markdown/RTLAmba/includes/monitor_package_spec.md`
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Design Guide: `rtl/amba/PRD.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
