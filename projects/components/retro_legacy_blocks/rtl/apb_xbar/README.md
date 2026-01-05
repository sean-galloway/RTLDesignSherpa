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

# APB Crossbar for Retro Legacy Blocks

## Overview

This directory contains the APB crossbar specifically designed for retro PC legacy peripheral blocks. The crossbar provides a single APB master interface that routes to 8 named slave interfaces.

### Architecture

```
┌─────────────────────────────────────────────────────┐
│ apb_xbar_legacy_1to8 (Named Port Wrapper)           │
│                                                      │
│  Master APB ─────► apb_xbar_1to8 ───────► Named     │
│  (m_apb_*)         (Generated)           Slaves     │
│                    (Registered)          (hpet_apb_*│
│                                           ioapic_*  │
│                                           etc.)     │
└─────────────────────────────────────────────────────┘
```

The implementation uses the official APB crossbar generator:
- **apb_xbar_1to8.sv** - Generated using `generate_xbars.py` from `projects/components/apb_xbar/bin/`
- **apb_xbar_legacy_1to8.sv** - Named-port wrapper mapping numbered ports to descriptive legacy block names

## Module: apb_xbar_legacy_1to8

### Features

- **1-to-8 APB Crossbar** - Single master to 8 slaves
- **Named Ports** - Descriptive port names for each legacy block
- **Registered Architecture** - Uses apb_slave/apb_master converters for better timing
- **4KB Address Ranges** - Each agent gets 4KB of address space (configurable)
- **Subtractive Decode** - Catch-all agent for unmapped addresses
- **Parameterizable Base Address** - Flexible memory mapping

### Address Map

Default Base Address: `0xFEC0_0000` (typical HPET/legacy range)

**Address decode uses bits [14:12] for 8 slaves with 4KB regions.**

### Standard Intel PC Architecture Compliance

This crossbar is designed to work with **two separate address regions** for maximum compatibility:

**Region 1 - IOAPIC Block (This Crossbar @ 0xFEC0_0000):**

| Slave | Agent | Address Range | Standard PC Address |
|-------|-------|---------------|---------------------|
| **0** | **IOAPIC** | 0xFEC0_0000 - 0xFEC0_0FFF | 0xFEC00000 ✅ **exact match!** |
| **1** | **HPET** | 0xFEC0_1000 - 0xFEC0_1FFF | See Region 2 below |
| **2** | **PIT 8254** | 0xFEC0_2000 - 0xFEC0_2FFF | I/O ports 0x40-0x5F |
| **3** | **RTC** | 0xFEC0_3000 - 0xFEC0_3FFF | I/O ports 0x70-0x7F |
| **4** | **PIC 8259** | 0xFEC0_4000 - 0xFEC0_4FFF | I/O ports 0x20-0xA1 |
| **5** | **PM ACPI** | 0xFEC0_5000 - 0xFEC0_5FFF | Varies by chipset |
| **6** | **SMBUS** | 0xFEC0_6000 - 0xFEC0_6FFF | Varies by chipset |
| **7** | **Subtractive** | 0xFEC0_7000 - 0xFEC0_7FFF | Catch-all unmapped |

**Region 2 - HPET Block (Separate Instance Recommended):**

For true Intel PC compatibility, instantiate HPET separately:
```systemverilog
// HPET at standard Intel address
apb_hpet u_hpet (
    .paddr(hpet_paddr),  // Decode for 0xFED0_0000 range
    // ...
);
```

**Integration Notes:**
- **IOAPIC** - Use this crossbar at 0xFEC00000 (standard address preserved)
- **HPET** - Either use slave 1 of this crossbar OR instantiate separately at 0xFED00000
- **Legacy I/O** - PIT, RTC, PIC are memory-mapped (originally I/O ports)

### Usage Example

```systemverilog
apb_xbar_legacy_1to8 #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .BASE_ADDR(32'hFEC0_0000)
) u_legacy_xbar (
    // Clock and Reset
    .pclk(apb_clk),
    .presetn(apb_rst_n),

    // Master interface (from CPU/interconnect)
    .m_apb_PSEL(cpu_psel),
    .m_apb_PENABLE(cpu_penable),
    .m_apb_PADDR(cpu_paddr),
    .m_apb_PWRITE(cpu_pwrite),
    .m_apb_PWDATA(cpu_pwdata),
    .m_apb_PSTRB(cpu_pstrb),
    .m_apb_PPROT(cpu_pprot),
    .m_apb_PRDATA(cpu_prdata),
    .m_apb_PSLVERR(cpu_pslverr),
    .m_apb_PREADY(cpu_pready),

    // HPET interface
    .hpet_apb_PSEL(hpet_psel),
    .hpet_apb_PENABLE(hpet_penable),
    .hpet_apb_PADDR(hpet_paddr),
    .hpet_apb_PWRITE(hpet_pwrite),
    .hpet_apb_PWDATA(hpet_pwdata),
    .hpet_apb_PSTRB(hpet_pstrb),
    .hpet_apb_PPROT(hpet_pprot),
    .hpet_apb_PRDATA(hpet_prdata),
    .hpet_apb_PSLVERR(hpet_pslverr),
    .hpet_apb_PREADY(hpet_pready),

    // ... repeat for other agents ...

    // Subtractive agent (catches all unmapped addresses)
    .subtractive_apb_PSEL(default_agent_psel),
    .subtractive_apb_PENABLE(default_agent_penable),
    // ... subtractive agent connections ...
);
```

### Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ADDR_WIDTH` | 32 | Address bus width |
| `DATA_WIDTH` | 32 | Data bus width |
| `BASE_ADDR` | 0xFEC0_0000 | Base address for legacy block range |
| `ADDR_BITS` | 12 | Address bits per agent (4KB = 2^12) |

### Port Naming Convention

All slave ports follow the pattern: `<agent_name>_apb_<signal>`

**Master Port:**
- `m_apb_*` - Master APB interface (input from CPU/interconnect)

**Slave Ports:**
- `hpet_apb_*` - HPET (High Precision Event Timer)
- `ioapic_apb_*` - IO APIC (Interrupt Controller)
- `pic_8259_apb_*` - PIC 8259 (Legacy Interrupt Controller)
- `pit_8254_apb_*` - PIT 8254 (Programmable Interval Timer)
- `pm_acpi_apb_*` - PM ACPI (Power Management)
- `rtc_apb_*` - RTC (Real-Time Clock)
- `smbus_apb_*` - SMBUS (System Management Bus)
- `subtractive_apb_*` - Subtractive agent (catches unmapped)

### Address Decode Logic

The crossbar uses bits [14:12] to decode 8 slaves (4KB per slave):

1. **Calculate offset:** `offset = PADDR - BASE_ADDR`
2. **Extract slave index:** `slave_idx = offset[14:12]` (bits 14:12 for 8×4KB slaves)
3. **Route to slave:** Direct mapping to one of 8 slaves
4. **Generate select:** One-hot encoding of slave select

**Decode calculation:**
- 4KB = 2^12 bytes → bits [11:0] are offset within slave
- 8 slaves need 3 bits → bits [14:12] select slave (0-7)
- Total address space: 8 × 4KB = 32KB

### How It Was Generated

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/apb_xbar/bin
python3 apb_xbar_generator.py --masters 1 --slaves 8 --base-addr 0xFEC00000 --slave-size 0x1000
# Output: apb_xbar_1to8.sv with 4KB regions (moved to retro_legacy_blocks/rtl/apb_xbar/)
```

Then wrapped with named ports in `apb_xbar_legacy_1to8.sv`.

### Subtractive Agent

The **subtractive agent** is the 8th slave that catches all addresses not mapped to the 7 specific agents. This is useful for:
- Returning errors for unmapped accesses
- Providing default responses
- System-wide configuration registers
- Future expansion

### Timing

The crossbar uses a **registered architecture** with apb_slave/apb_master converters:
- Better timing characteristics than pure combinational
- Registered slave selection when command accepted
- Improved synthesis timing closure
- Uses skid buffers for pipelining

### Integration Notes

1. **Base Address Selection:**
   - Default is `0xFEC0_0000` (typical for HPET in PC architecture)
   - Can be changed via `BASE_ADDR` parameter
   - Ensure no overlap with other system memory regions

2. **Subtractive Agent Implementation:**
   - Must respond to ALL unmapped addresses
   - Typical implementation: return PSLVERR=1 immediately
   - Can implement forwarding to external bus

3. **Signal Connections:**
   - All APB signals must be connected for each slave
   - Unused slaves can be tied to constant values (PREADY=1, PRDATA=0, PSLVERR=0)

4. **Address Alignment:**
   - Each agent receives full 32-bit address
   - Agent is responsible for decoding within its 4KB range
   - Lower 12 bits (0-11) are agent-specific offsets

### Directory Structure

```
retro_legacy_blocks/rtl/apb_xbar/
├── apb_xbar_1to8.sv           # Generated crossbar (from apb_xbar component)
├── apb_xbar_legacy_1to8.sv    # Named-port wrapper
├── apb_xbar_legacy_1to8.f     # Filelist with all dependencies
└── README.md                   # This file
```

### Dependencies

The crossbar requires:
- `rtl/amba/apb/apb_slave.sv` - APB slave protocol converter
- `rtl/amba/apb/apb_master.sv` - APB master protocol converter
- `rtl/amba/gaxi/gaxi_skid_buffer.sv` - Pipeline skid buffer
- `rtl/amba/gaxi/gaxi_fifo_sync.sv` - Synchronous FIFO
- `rtl/common/arbiter_*.sv` - Arbitration modules
- `rtl/amba/includes/reset_defs.svh` - Reset macros

All dependencies are listed in `apb_xbar_legacy_1to8.f`.

### Related Documentation

- Main APB Crossbar Component: `/projects/components/apb_xbar/`
- APB Crossbar PRD: `/projects/components/apb_xbar/PRD.md`
- Retro Legacy Blocks: `/projects/components/retro_legacy_blocks/`

### Testing

To test this crossbar, create a testbench that:
1. Instantiates the crossbar with test BASE_ADDR
2. Connects simple APB slave models to each port
3. Issues APB transactions to all 8 address ranges
4. Verifies correct routing and response multiplexing

Example test addresses (BASE_ADDR = 0xFEC0_0000):
- `0xFEC0_0100` → IOAPIC (slave 0)
- `0xFEC0_1200` → HPET (slave 1)
- `0xFEC0_2400` → PIT 8254 (slave 2)
- `0xFEC0_3800` → RTC (slave 3)
- `0xFEC0_4C00` → PIC 8259 (slave 4)
- `0xFEC0_5F00` → PM ACPI (slave 5)
- `0xFEC0_6ABC` → SMBUS (slave 6)
- `0xFEC0_7FFF` → Subtractive (slave 7)

---

**Created:** 2025-11-15
**Author:** Claude (AI Assistant)
**Version:** 1.0
