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

# APB (Advanced Peripheral Bus) Modules

**Location:** `rtl/amba/apb4/`
**Test Location:** `val/amba/`
**Status:** Production Ready

---

## Overview

The APB subsystem provides a complete implementation of the ARM AMBA 4 APB (Advanced Peripheral Bus) protocol: masters, slaves, monitors, interconnect components, and testbench utilities. APB is the simple, low-power peripheral bus you hang low-bandwidth peripherals off a system bus with — a two-cycle handshake and a minimal set of control signals. That simplicity is the whole point.

### Protocol Scope: APB4, not APB5

Every module in `rtl/amba/apb4/` implements **AMBA 4 APB (APB4)**: `PSEL`, `PENABLE`,
`PREADY`, `PADDR`, `PWRITE`, `PWDATA`, `PSTRB`, `PPROT`, `PRDATA`, `PSLVERR`.

The APB5 additions — `PWAKEUP`, `PAUSER`/`PWUSER`/`PRUSER`/`PBUSER`, and the
optional parity signals — are **not** present on these modules. They live in a
separate module family:

| Family | RTL | Documentation |
|--------|-----|---------------|
| APB4 (this book) | `rtl/amba/apb4/` | `docs/markdown/rtl-amba/apb4/` |
| APB5 | `rtl/amba/apb5/` | [APB5 Modules](../apb5/README.md) |

Use `apb5_slave` / `apb5_master` (and their `_cg` / `_cdc` variants) when APB5
signalling is required. The two families are otherwise architecturally identical.

The modules in this book fall into four groups.

### Core Protocol Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb4_master** | Full-featured APB master with command/response interface | [apb4_master.md](apb4_master.md) | Documented |
| **apb4_slave** | Complete APB slave with buffered cmd/rsp interface | [apb4_slave.md](apb4_slave.md) | Documented |
| **apb4_slave_cdc** | APB slave with clock domain crossing support | [apb4_slave_cdc.md](apb4_slave_cdc.md) | Documented |
| **apb4_monitor** | Transaction monitoring with 128-bit monitor bus + 64-bit timestamp | [apb4_monitor.md](apb4_monitor.md) | Documented |

**Note:** `apb4_monitor.sv` lives HERE in `rtl/amba/apb4/` — the protocol
monitors stay with the protocol they wrap; only the monitor CORE pieces
live in `rtl/amba/monitor/`. Its specification is
[apb4_monitor.md](apb4_monitor.md) in this book.

### Testbench Utilities

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb4_master_stub** | Lightweight APB master for testbench integration | [apb4_master_stub.md](apb4_master_stub.md) | Documented |
| **apb4_slave_stub** | Lightweight APB slave for testbench integration | [apb4_slave_stub.md](apb4_slave_stub.md) | Documented |

### Interconnect Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apbx_xbar_thin** | Fully parameterized M×S combinational crossbar with weighted round-robin | [../apbx/apbx_xbar_thin.md](../apbx/apbx_xbar_thin.md) | Documented |
| **apbx_xbar_1to1** / **2to1** / **1to4** / **2to4** / **2to2_mixed** | Generated fixed-configuration crossbars | [../apbx/apbx_xbar_variants.md](../apbx/apbx_xbar_variants.md) | Documented |

**Note:** The crossbar moved out of this directory (2026-08-13). It is no
longer an APB4-only block: `apbx_xbar` carries per-port version masks and can
be APB4, APB5, or mixed on the same fabric, so it is documented in
[../apbx/](../apbx/README.md). An all-APB4 configuration — the default — is
still built entirely from the APB4 primitives here, which is why the entry
remains listed.

The RTL, generator, and testbenches live in the component area
(`projects/components/apbx-xbar/`), not under `rtl/amba/apb4/`.

### Clock-Gated Variants

Each adds `cfg_cg_enable` / `cfg_cg_idle_count` inputs and gating/idle
status outputs. `apb4_master_cg` and `apb4_slave_cg` wrap their base module
in one `amba_clock_gate_ctrl` with an `apb_clock_gating` status output;
`apb4_slave_cdc_cg` is a SIBLING of apb4_slave_cdc, not a wrapper — it
re-instantiates apb4_slave plus the two CDC FIFOs around TWO gate cells,
with per-domain `pclk_cg_*` / `aclk_cg_*` status outputs.

| Module | Base Module | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb4_master_cg** | `apb4_master` | [apb4_master_cg.md](apb4_master_cg.md) | Documented |
| **apb4_slave_cg** | `apb4_slave` | [apb4_slave_cg.md](apb4_slave_cg.md) | Documented |
| **apb4_slave_cdc_cg** | `apb4_slave_cdc` | [apb4_slave_cdc_cg.md](apb4_slave_cdc_cg.md) | Documented |

### Key Features

**APB protocol support:**
- **Full APB4 Compliance:** Complete AMBA 4 APB protocol implementation
- **PSTRB Support:** Byte-lane strobes for partial writes
- **PPROT Support:** Protection attributes for security-aware systems
- **Error Handling:** PSLVERR support for error responses
- **APB5 Available Separately:** See `rtl/amba/apb5/` for `PWAKEUP`, the
  `P*USER` sidebands, and optional parity

**Clock domain crossing:**
- **Dual-Clock Operation:** APB (pclk) and backend (aclk) domains
- **Safe CDC:** Gray-pointer asynchronous FIFOs (`gaxi_fifo_async`) in both directions
- **Independent Frequencies:** Backend can run faster or slower than APB
- Caveat: **Reset both domains together** across the CDC variants — a one-sided reset is NOT safe (consumed entries replay / responses fabricate; see apb4_slave_cdc.md's reset analysis)

**Monitoring and debug:**
- **Transaction Monitoring:** Real-time protocol monitoring
- **128-bit Monitor Bus:** Standardized packet format plus a 64-bit side-band timestamp
- **Error Detection:** Protocol violations, timeout detection
- **Performance Tracking:** Transaction counting, latency measurement

**Testbench integration:**
- **Packed Interfaces:** Simplified testbench connectivity
- **Stub Modules:** Lightweight wrappers for CocoTB integration
- **WaveDrom Support:** Automated waveform generation

---

## Functional Description

### APB Transfer Phases

APB uses a simple two-phase protocol:

1. **SETUP Phase:** PSEL asserted, PENABLE low
   - Master presents address, control signals, and write data (if write)
   - Slave prepares for transfer

2. **ACCESS Phase:** PSEL and PENABLE both asserted
   - Slave completes transfer and asserts PREADY when ready
   - For reads, slave presents PRDATA
   - Slave may assert PSLVERR to signal error

### Signal Descriptions

| Signal | Direction | Description |
|--------|-----------|-------------|
| PCLK | Input | APB clock |
| PRESETn | Input | Active-low reset |
| PSEL | Master→Slave | Slave select |
| PENABLE | Master→Slave | Enable (ACCESS phase indicator) |
| PREADY | Slave→Master | Transfer complete |
| PADDR | Master→Slave | Address bus |
| PWRITE | Master→Slave | Write enable (1=write, 0=read) |
| PWDATA | Master→Slave | Write data |
| PSTRB | Master→Slave | Byte lane strobes |
| PPROT | Master→Slave | Protection attributes |
| PRDATA | Slave→Master | Read data |
| PSLVERR | Slave→Master | Error response |

---

## Usage Example

### Using APB Master

```systemverilog
apb4_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .CMD_DEPTH(2),
    .RSP_DEPTH(2)
) u_apb4_master (
    .pclk           (clk),
    .presetn        (resetn),

    // Command interface
    .cmd_valid      (cmd_valid),
    .cmd_ready      (cmd_ready),
    .cmd_pwrite     (cmd_pwrite),
    .cmd_paddr      (cmd_paddr),
    .cmd_pwdata     (cmd_pwdata),
    .cmd_pstrb      (cmd_pstrb),
    .cmd_pprot      (3'b000),      // floating this drives Z into the FIFO

    // Response interface
    .rsp_valid      (rsp_valid),
    .rsp_ready      (rsp_ready),
    .rsp_prdata     (rsp_prdata),
    .rsp_pslverr    (rsp_pslverr),

    // APB master interface
    .m_apb_PSEL     (psel),
    .m_apb_PENABLE  (penable),
    .m_apb_PREADY   (pready),
    .m_apb_PADDR    (paddr),
    .m_apb_PWRITE   (pwrite),
    .m_apb_PWDATA   (pwdata),
    .m_apb_PSTRB    (pstrb),
    .m_apb_PRDATA   (prdata),
    .m_apb_PSLVERR  (pslverr)
);
```

### Using APB Slave

```systemverilog
apb4_slave #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .DEPTH(2)
) u_apb4_slave (
    .pclk           (clk),
    .presetn        (resetn),

    // APB slave interface
    .s_apb_PSEL     (psel),
    .s_apb_PENABLE  (penable),
    .s_apb_PREADY   (pready),
    .s_apb_PADDR    (paddr),
    .s_apb_PWRITE   (pwrite),
    .s_apb_PWDATA   (pwdata),
    .s_apb_PSTRB    (pstrb),
    .s_apb_PRDATA   (prdata),
    .s_apb_PSLVERR  (pslverr),

    // Command interface
    .cmd_valid      (cmd_valid),
    .cmd_ready      (cmd_ready),
    .cmd_pwrite     (cmd_pwrite),
    .cmd_paddr      (cmd_paddr),
    .cmd_pwdata     (cmd_pwdata),
    .cmd_pstrb      (cmd_pstrb),
    .cmd_pprot      (cmd_pprot),   // OUTPUT to the backend (do not tie)

    // Response interface
    .rsp_valid      (rsp_valid),
    .rsp_ready      (rsp_ready),
    .rsp_prdata     (rsp_prdata),
    .rsp_pslverr    (rsp_pslverr)
);
```

---

## Design Notes

### Command/Response Architecture

All APB modules use a command/response interface pattern for backend integration:

**Command Interface (Master → Backend or APB → Backend):**
- `cmd_valid`, `cmd_ready` - Handshake signals
- `cmd_pwrite` - Write/read direction
- `cmd_paddr` - Transaction address
- `cmd_pwdata` - Write data
- `cmd_pstrb` - Byte strobes
- `cmd_pprot` - Protection attributes

**Response Interface (Backend → Master or Backend → APB):**
- `rsp_valid`, `rsp_ready` - Handshake signals
- `rsp_prdata` - Read data
- `rsp_pslverr` - Error flag

This separation buys you:
- Clean clock domain crossing
- Buffering and pipelining
- Easy testbench integration
- Backend processing flexibility

### Monitor Bus Protocol

The APB monitor outputs standardized 128-bit `monitor_packet_t` records, paired
with a 64-bit side-band timestamp:

```
[127:124] - Packet Type    (4 bits)
[123:109] - Reserved       (15 bits, forward-compat slack)
[108:105] - Protocol       (4 bits)
[104:97]  - Event Code     (8 bits)
[96:88]   - Channel ID     (9 bits)
[87:72]   - Agent ID       (16 bits)
[71:64]   - Unit ID        (8 bits)
[63:0]    - Event Data     (64 bits)
```

See [apb4_monitor.md](apb4_monitor.md) for detailed packet format.

---

## Related Modules

- **[APB5 Modules](../apb5/README.md)** - APB5 family (`PWAKEUP`, `P*USER`, parity)
- **[AXI4 Modules](../axi4/README.md)** - Full AXI4 protocol components
- **[AXIL4 Modules](../axil4/README.md)** - AXI4-Lite components
- **[AXIS4 Modules](../axis4/README.md)** - AXI4-Stream components
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities

---

## Testing

All APB modules are verified using CocoTB-based testbenches located in `val/amba/`:

```bash
# Run all APB tests
pytest val/amba/test_apb*.py -v

# Run specific module tests
pytest val/amba/test_apb4_master.py -v
pytest val/amba/test_apb4_slave.py -v
pytest val/amba/test_apb4_slave_cdc.py -v
pytest val/amba/test_apb4_monitor.py -v

# Clock-gated CDC variant
pytest val/amba/test_apb4_slave_cdc_cg.py -v

# Generated crossbars (component area)
pytest projects/components/apbx-xbar/dv/tests/ -v

# Run with waveform generation
env ENABLE_WAVEDROM=1 pytest val/amba/test_apb4_slave_wavedrom.py -v
```

### WaveDrom Tests

Several modules have dedicated WaveDrom tests that generate detailed timing diagrams:

- `test_apb4_slave_wavedrom.py::test_comprehensive_apb4_slave` - APB slave protocol waveforms
- `test_apb4_slave_cdc.py::test_apb4_slave_cdc_wavedrom` - CDC timing diagrams

### Test Coverage Gaps

The following APB4 modules have no dedicated test at `val/amba/`. They are
exercised indirectly (stubs through the generated crossbars and the AXI4-to-APB
bridge; the clock-gated wrappers through their base modules), and direct tests
exist for the APB5 equivalents:

| Module | Direct APB4 test | APB5 equivalent |
|--------|------------------|-----------------|
| `apb4_master_stub` | None | `test_apb5_master_stub.py` |
| `apb4_slave_stub` | None | `test_apb5_slave_stub.py` |
| `apb4_master_cg` | None | `test_apb5_master_cg.py` |
| `apb4_slave_cg` | None | `test_apb5_slave_cg.py` |

Generated waveforms are stored in:
- JSON format: `_wavedrom/`
- SVG images: `_wavedrom_svg/`

---

## References

### Specifications
- ARM IHI 0024C -- AMBA APB Protocol Specification, Version 2.0 (defines APB4:
  adds `PSTRB` and `PPROT`). This is the specification these modules implement.
- ARM IHI 0024E -- AMBA APB Protocol Specification, Issue E (APB5: `PWAKEUP`,
  `P*USER` sidebands, parity). Applies to `rtl/amba/apb5/`, not to this family.

**Naming caution:** ARM's *document* version 2.0 (IHI 0024C) is the APB4
specification. The older APB3 protocol is IHI 0024B. Citing "APB Protocol
Specification v2.0" without the IHI number is ambiguous.

### Source Code
- RTL: `rtl/amba/apb4/`
- Tests: `val/amba/test_apb*.py`
- Framework: `bin/TBClasses/components/apb/`

### Test Documentation
- APB Master Tests: `val/amba/test_apb4_master.py`
- APB Slave Tests: `val/amba/test_apb4_slave.py`
- APB CDC Tests: `val/amba/test_apb4_slave_cdc.py`
- APB Monitor Tests: `val/amba/test_apb4_monitor.py`
- APB Crossbar Tests: `projects/components/apbx-xbar/dv/tests/`

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
