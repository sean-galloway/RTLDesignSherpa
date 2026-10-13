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

# Memory Map and Register Spaces

Three memory-mapped views exist: the HIVE-C firmware address space, the
router configuration registers (written via PKT_CONFIG or HIVE-C's AXIL
master), and the soft-reset register. All offsets are byte addresses.

## HIVE-C Firmware Memory Map

```
0x0000_0000 - 0x0000_7FFF: Instruction memory (32 KB)
0x0000_8000 - 0x0000_FFFF: Data memory (32 KB)
0x4000_0000 - 0x4000_0FFF: RAPIDS register interface (AXIL master window)
0x4000_1000 - 0x4000_1FFF: Delta network control
0x4000_2000 - 0x4000_2FFF: SERV monitor status (16 × 256 bytes)
0x4000_3000 - 0x4000_3FFF: Configuration registers
0x4000_4000 - 0x4000_4FFF: Host interface (UART/AXI4-Lite)
```

: HIVE-C firmware memory map

The SERV status window (0x4000_2000) exposes one 256-byte record per monitor:
counters, occupancy snapshot, error flags, and firmware heartbeat. Layout is
fixed with the SERV firmware (see MAS Chapter 3).

## Router Configuration Registers (per tile)

Each Delta tile router exposes this register block. HIVE-C reaches them
through its AXI4-Lite master window (Delta network control region) or via
PKT_CONFIG broadcast.

```
Base + 0x00: MODE_SELECT     (RW) - Context ID [1:0]
Base + 0x04: ROUTE_TABLE_0   (RW) - Custom routing entry 0
Base + 0x08: ROUTE_TABLE_1   (RW) - Custom routing entry 1
     ...
Base + 0x20: FLOW_CTRL_CFG   (RW) - Credit limits, VC allocation
Base + 0x24: PRIORITY_MASK   (RW) - QoS priority weights
Base + 0x28: STATUS          (RO) - Buffer occupancy, active packets
Base + 0x2C: STATISTICS      (RO) - Packet counters
Base + 0x30: ERROR_FLAGS     (RO) - Overflow, underflow, parity errors
Base + 0x34: DEBUG_TRACE     (RW) - Trace filter configuration
```

: Router configuration register map

`ROUTE_TABLE_n` blocks are only meaningful in Context 3 (custom/debug);
contexts 0-2 use hardwired routing functions, and the table registers read
back as zero.

## Soft Reset Register

HIVE supports selective soft resets from configuration space (offset 0x0000
in the HIVE configuration region):

```
Bits [31:16] - SERV Reset Mask (one bit per SERV monitor)
Bit  [8]     - Delta Network Soft Reset
Bit  [4]     - Control Network Soft Reset
Bit  [0]     - HIVE-C Soft Reset (use with caution)
```

: Soft reset register

Write 1 to assert, 0 to deassert. Soft resets are synchronous to the target
clock domain and follow the reset sequencing rules in the MAS clocking
chapter. Use cases: SERV hang recovery without system disruption, clearing
Delta state during reconfiguration, and component-level debug.

## Register Access Rules

- **Host → HIVE-C:** host interface only; the host has no path to RAPIDS,
  Delta, or SERV registers except through HIVE-C firmware actions.
- **HIVE-C → RAPIDS/Delta/SERV:** AXI4-Lite master window and PKT_CONFIG
  broadcast; descriptor *data* never travels over the register path — it
  travels as CDA packets.
- **SERV → registers:** SERV monitors write tile configuration only via
  PKT_CONFIG injection; their router tap is observation-only.

---

**Last Updated:** 2026-10-12
