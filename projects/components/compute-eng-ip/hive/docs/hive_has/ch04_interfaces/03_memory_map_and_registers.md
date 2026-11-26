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
0x4000_2000 - 0x4000_2FFF: engine monitor status (4 × 256 bytes; the rest of the window is reserved)
0x4000_3000 - 0x4000_3FFF: Configuration registers
0x4000_4000 - 0x4000_4FFF: Host interface (UART/AXI4-Lite)
```

: HIVE-C firmware memory map

The engine monitor status window (0x4000_2000) exposes one 256-byte record
per compute engine:
counters, occupancy snapshot, error flags, and firmware heartbeat. Layout is
fixed with the engine monitor firmware (see MAS Chapter 3).

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
Bits [19:16] - Engine Monitor Context Hold Mask (one bit per monitor context;
               1 holds the context at its reset address, gatling's run bit)
Bits [31:20] - Reserved (v0.2's 16-bit SERV reset mask)
Bit  [8]     - Delta Network Soft Reset
Bit  [4]     - Control Network Soft Reset
Bit  [0]     - HIVE-C Soft Reset (use with caution)
```

: Soft reset register

Write 1 to assert, 0 to deassert. Soft resets are synchronous to the target
clock domain and follow the reset sequencing rules in the MAS clocking
chapter. Use cases: recovering one monitor context (gatling halts a context on a
trap and lets the other three run) without system disruption, clearing
Delta state during reconfiguration, and component-level debug.

## Fabric IDLE Status Register

A read-only status register in the HIVE configuration region carries the
aggregated **fabric IDLE** signal — the quiescent indication from the Delta
fabric covering all participating routers (and the engine monitor's injection paths).
HIVE-C firmware reads it to verify quiesce before issuing
`SET_ROUTING_MODE` (§5.4), and the host may read it for bring-up
diagnostics. The register is part of the PeakRDL-managed HIVE register
bank (generated from `rdl/` sources per the repo convention, see MAS
§2.5): bit [0] = fabric idle, bits [16:1] reserved (per-router idle
granularity is a possible future extension).

## Register Access Rules

- **Host → HIVE-C:** host interface only; the host has no path to RAPIDS,
  Delta, or engine-monitor registers except through HIVE-C firmware actions.
- **HIVE-C → RAPIDS/Delta/engine monitor:** AXI4-Lite master window and PKT_CONFIG
  broadcast; descriptor *data* never travels over the register path — it
  travels as CDA packets.
- **Engine monitor → registers:** the monitor writes tile configuration only via
  PKT_CONFIG injection; their router tap is observation-only.

---

**Last Updated:** 2026-11-25
