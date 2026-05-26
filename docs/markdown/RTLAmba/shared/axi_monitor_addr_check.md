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

# AXI Monitor Address-Range Checker

**Module:** `axi_monitor_addr_check.sv`
**Location:** `rtl/amba/shared/`
**Category:** Core Infrastructure
**Status:** ✅ Production Ready (Formally Verified)

---

## Overview

The `axi_monitor_addr_check` module is a parallel address-range comparator instantiated within AXI monitor wrappers. It observes command-phase handshakes (AR/AW) and detects when addresses fall within user-configured inclusive ranges `[low, high]`, emitting `PktTypeError` monbus packets with event code `AXI_ERR_ADDR_RANGE = 4'hD`.

This is a **shared infrastructure module** used internally by AXI4/AXIL4/AXI5 monitor wrappers when parameterized with `N_ADDR_RANGES > 0`. It is not typically instantiated directly by users but is critical for address-space validation and security monitoring.

---

## Key Features

- ✅ **Parallel Range Comparators:** N independent [low, high] inclusive range checkers
- ✅ **Per-Range Enable:** Individual mask bit for each range
- ✅ **Master Enable:** `cfg_addr_check_enable` gate for all comparators
- ✅ **Zero-Area Synthesis:** When `N_ADDR_RANGES = 0`, module is completely omitted (no gates, no regs)
- ✅ **Monbus Integration:** Standard error packet format with event code 4'hD
- ✅ **Per-Range Coalescing:** Latest address per range latched; one packet per cycle via priority encoder
- ✅ **Formal Verification:** All 6 properties proven (PASS)

---

## Module Purpose

The `axi_monitor_addr_check` module enables:

1. **Address-Space Validation:** Detect accesses to forbidden or suspicious memory regions
2. **Security Monitoring:** Flag unauthorized read/write attempts to protected address ranges
3. **Debug & Profiling:** Identify hot-spot access patterns and traffic targeting specific regions
4. **Design Verification:** Verify address constraints in functional simulation and formal proof

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `N_ADDR_RANGES` | int | 0 | Number of address-range comparators. 0 = module omitted entirely. |
| `ADDR_WIDTH` | int | 32 | Address bus width (matches AXI_ADDR_WIDTH of parent monitor). |
| `ID_WIDTH` | int | 4 | Transaction ID width (unused in addr_check; present for consistency). |
| `UNIT_ID` | int | 1 | 4-bit unit identifier in monitor packets. |
| `AGENT_ID` | int | 0 | 8-bit agent identifier in monitor packets. |
| `IS_READ` | bit | 1 | Flag indicating if this comparator monitors AR (1) or AW (0) channel. |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `aclk` | Input | 1 | AXI clock |
| `aresetn` | Input | 1 | AXI active-low reset |

### Command Interface (Snoop)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cmd_valid` | Input | 1 | Command valid (AR or AW handshake) |
| `cmd_ready` | Input | 1 | Command ready (slave accepting) |
| `cmd_addr` | Input | ADDR_WIDTH | Command address (araddr or awaddr) |
| `cmd_id` | Input | ID_WIDTH | Command transaction ID (arid or awid) |

### Configuration Inputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_addr_check_enable` | Input | 1 | Master enable for all comparators. 0 = no packets generated. |
| `cfg_addr_range_enable[N_ADDR_RANGES-1:0]` | Input | N | Per-range enable bits. 1 = range active, 0 = range disabled. |
| `cfg_addr_range_low[N_ADDR_RANGES-1:0][ADDR_WIDTH-1:0]` | Input | N × ADDR_WIDTH | Inclusive low bound for each range. |
| `cfg_addr_range_high[N_ADDR_RANGES-1:0][ADDR_WIDTH-1:0]` | Input | N × ADDR_WIDTH | Inclusive high bound for each range. |

### Monitor Bus Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `addr_pkt_valid` | Output | 1 | Address-check error packet valid |
| `addr_pkt_ready` | Input | 1 | Downstream ready to accept packet |
| `addr_pkt_data` | Output | 64 | Monitor packet (standard 64-bit format) |

---

## Internal Architecture

The module instantiates N parallel comparators:

1. **Per-Range Comparators:** Each range i computes a hit signal `hit[i] = (cfg_addr_range_enable[i] && cmd_valid && cmd_ready && (cmd_addr >= cfg_addr_range_low[i]) && (cmd_addr <= cfg_addr_range_high[i]))`

2. **Per-Range Latch:** On a hit, `latched_addr[i]` captures the lower 29 bits of `cmd_addr`; a pending bit `pending[i]` is set. If another hit occurs before the packet is emitted, the address is overwritten (latest-win coalescing).

3. **Packet Generator:** A lowest-index priority encoder scans `pending[N-1:0]` each cycle. When a pending range is found, a packet is generated on the monbus with the latched address, range index, and `is_read` flag. The pending bit is cleared after successful packet handshake.

This approach ensures:
- **No event loss per range:** Distinct ranges never drop hits.
- **Bounded latency:** One packet maximum per cycle per range (across all ranges).
- **Memory efficient:** O(N) area (N comparators + N latch pairs).

---

## Event Encoding

Monitor bus packet format (64-bit):

```
Bits [63:60] - Packet Type:
  0x0 = PktTypeError

Bits [59:57] - Protocol:
  0x0 = AXI

Bits [56:53] - Event Code:
  4'hD = AXI_ERR_ADDR_RANGE

Bits [52:47] - Channel ID:
  Encoded from IS_READ and ID fields (reserved/debug)

Bits [46:43] - Unit ID:
  From UNIT_ID parameter

Bits [42:35] - Agent ID:
  From AGENT_ID parameter

Bits [34:30] - Range Index:
  Which range (0 to N-1) generated this hit

Bits [29] - Is Read Flag:
  1 = hit on AR (read address), 0 = hit on AW (write address)

Bits [28:0] - Lower 29 Bits of Address:
  Part of the matched address for diagnostic/debug purposes
```

---

## Formal Properties

All properties proven via formal verification (see `formal/amba/axi_monitor_addr_check/formal_axi_monitor_addr_check.sv`):

| Property | Description | Status |
|----------|-------------|--------|
| **P1: Hit Detection** | When `cfg_addr_check_enable=1` and an address falls within enabled range, `pending[i]` is set. | PASS |
| **P2: Range Masking** | When `cfg_addr_check_enable=0`, no pending bits are set regardless of address. | PASS |
| **P3: Packet Generation** | When a pending range exists and `addr_pkt_ready=1`, a valid packet is generated with correct range index. | PASS |
| **P4: Pending Clearance** | After packet handshake, the corresponding pending bit is cleared in next cycle. | PASS |
| **P5: Latest-Win Coalescing** | If a range hits again while pending, the latched address is updated (not lost). | PASS |
| **P6: No Cross-Range Interference** | Hits in one range do not affect other ranges' pending/latched state. | PASS |

---

## Configuration Examples

### Example 1: Single Range Checker

Monitor writes to protected register space (0x1000_0000 to 0x1000_0FFF):

```systemverilog
axi4_master_wr_mon #(
    .N_ADDR_RANGES(1),
    .AXI_ADDR_WIDTH(32),
    // ... other parameters ...
) u_wr_mon (
    // ... AXI signals ...

    // Address-range checker config
    .cfg_addr_check_enable(1'b1),
    .cfg_addr_range_enable(1'b1),
    .cfg_addr_range_low(32'h1000_0000),
    .cfg_addr_range_high(32'h1000_0FFF),

    // ... monitor signals ...
);
```

### Example 2: Multi-Range Checker

Monitor accesses to three forbidden zones:

```systemverilog
axi4_master_rd_mon #(
    .N_ADDR_RANGES(3),
    .AXI_ADDR_WIDTH(32),
    // ... other parameters ...
) u_rd_mon (
    // ... AXI signals ...

    // Address-range checker config
    .cfg_addr_check_enable(1'b1),
    .cfg_addr_range_enable(3'b111),
    .cfg_addr_range_low({
        32'h2000_0000,  // Range 2: System RAM (protected)
        32'h1000_0000,  // Range 1: Registers
        32'h0800_0000   // Range 0: Firmware ROM (read-only)
    }),
    .cfg_addr_range_high({
        32'h2FFF_FFFF,
        32'h1000_FFFF,
        32'h08FF_FFFF
    }),

    // ... monitor signals ...
);
```

### Example 3: Exact-Match Detector

Detect accesses to a single address:

```systemverilog
.cfg_addr_range_low(32'hDEAD_BEEF),
.cfg_addr_range_high(32'hDEAD_BEEF)   // low == high => exact match only
```

---

## Filtering Integration

The address-range checker output is a standard error packet with event code **4'hD** (`AXI_ERR_ADDR_RANGE`).

**Gating via existing error mask:**
- Set `cfg_axi_error_mask[13]` to 1 in the parent monitor to suppress these packets.
- **No new mask wiring is needed** — the existing 16-bit error mask vector already has bit 13 reserved for this event code.

**Example:** Disable address-range packets while keeping other errors:
```systemverilog
.cfg_axi_error_mask(16'h2000)  // Bit 13 high = drop range packets
```

---

## Integration Notes

### Instantiation Pattern

The module is instantiated **inside** AXI monitor wrappers (`axi4_master_wr_mon`, etc.) by the monitor architecture. Users do not instantiate this module directly but configure it via wrapper parameters.

### Synthesis Behavior

- **`N_ADDR_RANGES = 0`:** Module is entirely synthesized away (zero area). All config inputs are tied off. Output packet valid is constant 0.
- **`N_ADDR_RANGES > 0`:** Full comparator logic synthesized. Area scales with N.

### Downstream FIFO

The monbus output should be fed into a standard FIFO (e.g., `gaxi_fifo_sync`) to prevent backpressure stalls:

```systemverilog
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(256)
) u_addr_check_fifo (
    .i_clk(aclk),
    .i_rst_n(aresetn),
    .i_valid(addr_pkt_valid),
    .i_data(addr_pkt_data),
    .o_ready(addr_pkt_ready),
    // ... downstream consumer ...
);
```

---

## Related Modules

- **[axi_monitor_base](./axi_monitor_base.md)** — Core monitor infrastructure that instantiates this module
- **[axi_monitor_filtered](./axi_monitor_filtered.md)** — 3-level packet filtering (sibling to addr_check)
- **[axi4_master_wr_mon](../axi4/axi4_master_wr_mon.md)** — Wrapper that uses this module (N_ADDR_RANGES parameter)

---

## See Also

- **Monitor Architecture:** `docs/markdown/RTLAmba/overview.md`
- **Monitor Configuration Guide:** [Monitor Base Configuration](./axi_monitor_base.md)
- **Packet Format Specification:** `docs/markdown/RTLAmba/includes/monitor_package_spec.md`
- **Formal Verification:** `formal/amba/axi_monitor_addr_check/`

---

## Navigation

- **[← Back to Shared Infrastructure Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
