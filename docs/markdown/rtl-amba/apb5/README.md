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

# APB5 (Advanced Peripheral Bus - AMBA 5) Modules

**Location:** `rtl/amba/apb5/`
**Test Location:** `val/amba/`
**Status:** Production Ready

---

## Overview

The APB5 subsystem is a complete implementation of the ARM AMBA 5 APB (Advanced Peripheral Bus) protocol: masters, slaves, monitors, clock domain crossing, and testbench utilities.

APB5 extends APB4 with features aimed at modern SoC designs while staying backward compatible. The simple two-cycle handshake is preserved exactly -- what changes is the signal list, which picks up security attributes, wake-up signaling, and improved error handling.

### AMBA4 vs AMBA5 Comparison

The table below compares the APB4 and APB5 protocol definitions, and states what
this RTL release actually implements. Optional APB5 features that are not
implemented are simply absent from the module port lists -- there are no tie-off
ports to connect.

| Feature | APB4 | APB5 | Implemented here |
|---------|------|------|------------------|
| Basic Protocol | Two-phase handshake | Two-phase handshake | Yes |
| Protection | PPROT[2:0] | PPROT[2:0] + PNSE | PPROT only -- no PNSE port |
| Wake-up | Not supported | PWAKEUP signal | Yes |
| User Signals | Not supported | PAUSER, PWUSER, PRUSER, PBUSER | Yes |
| Atomic Operations | Not supported | PEXCL, PEXOKAY | No -- not in this release |
| Parity | Not supported | Optional signal parity | Yes (`ENABLE_PARITY`) |
| Error Response | PSLVERR | PSLVERR (enhanced semantics) | Yes |

### Module Categories

#### Core Protocol Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb5_master** | Full-featured APB5 master with command/response interface | [apb5_master.md](apb5_master.md) | Documented |
| **apb5_slave** | Complete APB5 slave with buffered cmd/rsp interface | [apb5_slave.md](apb5_slave.md) | Documented |
| **apb5_slave_cdc** | APB5 slave with clock domain crossing support | [apb5_slave_cdc.md](apb5_slave_cdc.md) | Documented |
| **apb5_monitor** | Transaction monitoring with 128-bit monitor bus packet + 64-bit side-band timestamp | [apb5_monitor.md](apb5_monitor.md) | Documented |

#### Clock-Gated Variants

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb5_master_cg** | APB5 master with integrated clock gating | [apb5_master_cg.md](apb5_master_cg.md) | Documented |
| **apb5_slave_cg** | APB5 slave with integrated clock gating | [apb5_slave_cg.md](apb5_slave_cg.md) | Documented |
| **apb5_slave_cdc_cg** | APB5 slave CDC with integrated clock gating | [apb5_slave_cdc_cg.md](apb5_slave_cdc_cg.md) | Documented |

#### Testbench Utilities

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb5_master_stub** | Lightweight APB5 master for testbench integration | [apb5_master_stub.md](apb5_master_stub.md) | Documented |
| **apb5_slave_stub** | Lightweight APB5 slave for testbench integration | [apb5_slave_stub.md](apb5_slave_stub.md) | Documented |

#### Interconnect

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apbx_xbar** | APB crossbar family; any port may be APB5, and APB4/APB5 may be mixed on one fabric | [../apbx/README.md](../apbx/README.md) | Documented |

The crossbar is documented in its own [apbx/](../apbx/README.md) area rather
than here, because it is not an APB5-only block — the same RTL covers APB4,
APB5, and mixed configurations. An APB5 port on the crossbar instantiates the
`apb5_master` / `apb5_slave` boundary IP listed above.

### Key Features

#### APB5 Protocol Support
- **PSTRB Support:** Byte-lane strobes for partial writes
- **PPROT Support:** Protection attributes for security-aware systems
- **PWAKEUP Support:** Low-power wake-up signaling
- **User Signals:** PAUSER, PWUSER, PRUSER, PBUSER for sideband data
- **Optional Parity:** Per-byte data parity plus address and control parity (`ENABLE_PARITY`)

**Not implemented in this release:** PNSE (Non-secure extension) and the
PEXCL/PEXOKAY exclusive-access pair. No module in `rtl/amba/apb5/` declares
these ports.

#### Clock Domain Crossing
- **Dual-Clock Operation:** APB (pclk) and backend (aclk) domains
- **Safe CDC:** Proper handshake-based clock domain crossing
- **Independent Frequencies:** Backend can run faster or slower than APB

#### Power Management
- **Clock Gating:** Per-module clock gating for power reduction
- **Wake-up Signaling:** PWAKEUP for low-power state exit
- **Idle Detection:** Automatic clock gate when bus is idle

#### Monitoring and Debug
- **Transaction Monitoring:** Real-time protocol monitoring
- **64-bit Monitor Bus:** Standardized packet format (`monbus_packet[63:0]`, no side-band timestamp)
- **Error Detection:** Protocol violations, timeout detection
- **Performance Tracking:** Transaction counting, latency measurement

---

## Functional Description

### APB5 Transfer Phases

APB5 uses the same two-phase protocol as APB4:

1. **SETUP Phase:** PSEL asserted, PENABLE low
   - Master presents address, control signals, and write data (if write)
   - Slave prepares for transfer

2. **ACCESS Phase:** PSEL and PENABLE both asserted
   - Slave completes transfer and asserts PREADY when ready
   - For reads, slave presents PRDATA
   - Slave may assert PSLVERR to signal error

### APB5 Signal Descriptions

In this implementation the clock and reset ports are named `pclk` and `presetn`,
and the bus signals are prefixed `m_apb_` on masters and `s_apb_` on slaves
(for example `m_apb_PADDR`, `s_apb_PREADY`).

| Signal | Direction | Description |
|--------|-----------|-------------|
| pclk | Input | APB clock |
| presetn | Input | Active-low reset |
| PSEL | Master to Slave | Slave select |
| PENABLE | Master to Slave | Enable (ACCESS phase indicator) |
| PREADY | Slave to Master | Transfer complete |
| PADDR | Master to Slave | Address bus |
| PWRITE | Master to Slave | Write enable (1=write, 0=read) |
| PWDATA | Master to Slave | Write data |
| PSTRB | Master to Slave | Byte lane strobes |
| PPROT | Master to Slave | Protection attributes |
| PWAKEUP | Slave to Master | Wake-up signal (APB5) -- see note below |
| PAUSER | Master to Slave | Address phase user signal (APB5) |
| PWUSER | Master to Slave | Write data user signal (APB5) |
| PRDATA | Slave to Master | Read data |
| PSLVERR | Slave to Master | Error response |
| PRUSER | Slave to Master | Read data user signal (APB5) |
| PBUSER | Slave to Master | Write response user signal (APB5) |

**PWAKEUP direction note:** this suite implements PWAKEUP as a slave-to-master
signal used by a peripheral to request that the master (and its power domain)
stay awake. `apb5_slave` drives `s_apb_PWAKEUP` from its `wakeup_request` input
and `apb5_master` consumes `m_apb_PWAKEUP` as an input, capturing it in the
response packet (`rsp_pwakeup`) and in the `wakeup_pending` status output.

**PNSE, PEXCL and PEXOKAY are not implemented** and do not appear on any module
port list.

### Optional Parity Signals

Present on all masters and slaves; meaningful only when `ENABLE_PARITY=1`.

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| PWDATAPARITY | STRB_WIDTH | Master to Slave | One parity bit per write-data byte lane |
| PADDRPARITY | 1 | Master to Slave | Single parity bit over the whole address |
| PCTRLPARITY | 1 | Master to Slave | Single parity bit over {PWRITE, PSTRB, PPROT} |
| PRDATAPARITY | STRB_WIDTH | Slave to Master | One parity bit per read-data byte lane |
| PREADYPARITY | 1 | Slave to Master | Parity bit for PREADY |
| PSLVERRPARITY | 1 | Slave to Master | Parity bit for PSLVERR |

---

## Usage Examples

### Using APB5 Master

```systemverilog
apb5_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .CMD_DEPTH (6),      // command FIFO entries: 2..8 inclusive (any integer)
    .RSP_DEPTH (6)       // response FIFO entries: 2..8 inclusive (any integer)
) u_apb5_master (
    .pclk           (clk),
    .presetn        (resetn),

    // Command interface
    .cmd_valid      (cmd_valid),
    .cmd_ready      (cmd_ready),
    .cmd_pwrite     (cmd_pwrite),
    .cmd_paddr      (cmd_paddr),
    .cmd_pwdata     (cmd_pwdata),
    .cmd_pstrb      (cmd_pstrb),
    .cmd_pprot      (cmd_pprot),
    .cmd_pauser     (cmd_pauser),
    .cmd_pwuser     (cmd_pwuser),

    // Response interface
    .rsp_valid      (rsp_valid),
    .rsp_ready      (rsp_ready),
    .rsp_prdata     (rsp_prdata),
    .rsp_pslverr    (rsp_pslverr),
    .rsp_pwakeup    (rsp_pwakeup),
    .rsp_pruser     (rsp_pruser),
    .rsp_pbuser     (rsp_pbuser),

    // APB5 master interface
    .m_apb_PSEL     (psel),
    .m_apb_PENABLE  (penable),
    .m_apb_PREADY   (pready),
    .m_apb_PADDR    (paddr),
    .m_apb_PWRITE   (pwrite),
    .m_apb_PWDATA   (pwdata),
    .m_apb_PSTRB    (pstrb),
    .m_apb_PPROT    (pprot),
    .m_apb_PAUSER   (pauser),
    .m_apb_PWUSER   (pwuser),
    .m_apb_PRDATA   (prdata),
    .m_apb_PSLVERR  (pslverr),
    .m_apb_PWAKEUP  (pwakeup),      // input: driven by the slave
    .m_apb_PRUSER   (pruser),
    .m_apb_PBUSER   (pbuser),

    // Parity (tie off / leave open when ENABLE_PARITY=0)
    .m_apb_PWDATAPARITY  (),
    .m_apb_PADDRPARITY   (),
    .m_apb_PCTRLPARITY   (),
    .m_apb_PRDATAPARITY  ('0),
    .m_apb_PREADYPARITY  (1'b0),
    .m_apb_PSLVERRPARITY (1'b0),
    .parity_error_rdata  (),
    .parity_error_ctrl   (),

    // Status
    .wakeup_pending (wakeup_pending)
);
```

### Using APB5 Slave

```systemverilog
apb5_slave #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .DEPTH(2)
) u_apb5_slave (
    .pclk           (clk),
    .presetn        (resetn),

    // APB5 slave interface
    .s_apb_PSEL     (psel),
    .s_apb_PENABLE  (penable),
    .s_apb_PREADY   (pready),
    .s_apb_PADDR    (paddr),
    .s_apb_PWRITE   (pwrite),
    .s_apb_PWDATA   (pwdata),
    .s_apb_PSTRB    (pstrb),
    .s_apb_PPROT    (pprot),
    .s_apb_PAUSER   (pauser),
    .s_apb_PWUSER   (pwuser),
    .s_apb_PRDATA   (prdata),
    .s_apb_PSLVERR  (pslverr),
    .s_apb_PWAKEUP  (pwakeup),      // output: driven to the master
    .s_apb_PRUSER   (pruser),
    .s_apb_PBUSER   (pbuser),

    // Command interface
    .cmd_valid      (cmd_valid),
    .cmd_ready      (cmd_ready),
    .cmd_pwrite     (cmd_pwrite),
    .cmd_paddr      (cmd_paddr),
    .cmd_pwdata     (cmd_pwdata),
    .cmd_pstrb      (cmd_pstrb),
    .cmd_pprot      (cmd_pprot),
    .cmd_pauser     (cmd_pauser),
    .cmd_pwuser     (cmd_pwuser),

    // Response interface
    .rsp_valid      (rsp_valid),
    .rsp_ready      (rsp_ready),
    .rsp_prdata     (rsp_prdata),
    .rsp_pslverr    (rsp_pslverr),
    .rsp_pruser     (rsp_pruser),
    .rsp_pbuser     (rsp_pbuser),

    // Wake-up request from the backend (drives s_apb_PWAKEUP)
    .wakeup_request (wakeup_request),

    // Parity (tie off / leave open when ENABLE_PARITY=0)
    .s_apb_PWDATAPARITY  ('0),
    .s_apb_PADDRPARITY   (1'b0),
    .s_apb_PCTRLPARITY   (1'b0),
    .s_apb_PRDATAPARITY  (),
    .s_apb_PREADYPARITY  (),
    .s_apb_PSLVERRPARITY (),
    .parity_error_wdata  (),
    .parity_error_ctrl   ()
);
```

---

## Design Notes

### Command/Response Architecture

All APB5 modules use a command/response interface pattern for backend integration, identical to the APB4 architecture:

**Command Interface:**
- `cmd_valid`, `cmd_ready` - Handshake signals
- `cmd_pwrite` - Write/read direction
- `cmd_paddr` - Transaction address
- `cmd_pwdata` - Write data
- `cmd_pstrb` - Byte strobes
- `cmd_pprot` - Protection attributes
- `cmd_pauser`, `cmd_pwuser` - APB5 user attributes

**Response Interface:**
- `rsp_valid`, `rsp_ready` - Handshake signals
- `rsp_prdata` - Read data
- `rsp_pslverr` - Error flag
- `rsp_pruser`, `rsp_pbuser` - APB5 user attributes
- `rsp_pwakeup` - Captured PWAKEUP state (master only)

### Migration from APB4

APB5 modules are backward compatible with APB4 systems:
- Connect APB5 signals to APB4 equivalents
- Tie unused APB5 inputs (PWAKEUP, user signals, parity) to default values and
  leave the corresponding outputs unconnected
- On a master, tie `m_apb_PWAKEUP` to 0 for always-awake operation
- On a slave, tie `wakeup_request` to 0 so `s_apb_PWAKEUP` stays low
- Leave `ENABLE_PARITY=0` (the default), which forces all generated parity
  outputs and both `parity_error_*` flags to 0

---

## Related Modules

- **[APB4 Modules](../apb4/README.md)** - APB4 protocol components
- **[AXI5 Modules](../axi5/README.md)** - AXI5 protocol components
- **[AXIS5 Modules](../axis5/README.md)** - AXI5-Stream components
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities

---

## Testing

All APB5 modules are verified using CocoTB-based testbenches located in `val/amba/`:

```bash
# Run all APB5 tests
pytest val/amba/test_apb5*.py -v

# Run specific module tests
pytest val/amba/test_apb5_master.py -v
pytest val/amba/test_apb5_slave.py -v
pytest val/amba/test_apb5_slave_cdc.py -v
pytest val/amba/test_apb5_monitor.py -v
```

---

## References

### Specifications
- ARM AMBA 5 APB Protocol Specification
- ARM AMBA APB Protocol Specification v2.0 (APB4)

### Source Code
- RTL: `rtl/amba/apb5/`
- Tests: `val/amba/test_apb5*.py`
- Framework: `bin/TBClasses/components/apb/`

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[Back to rtl-amba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
