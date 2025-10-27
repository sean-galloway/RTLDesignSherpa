# APB Crossbar Modules

This directory contains APB crossbar modules generated using the proven `apb_slave` and `apb_master` architecture.

## Architecture

All crossbars follow a consistent design:

```
Master Side:     apb_slave modules convert APB → cmd/rsp interface
Internal:        Round-robin arbitration + address decoding
Slave Side:      apb_master modules convert cmd/rsp → APB interface
```

### Key Features

- **Independent arbitration per slave**: Each slave has its own round-robin arbiter
- **Grant persistence**: Grants held from command acceptance through response completion
- **Address decoding**: Automatic slave selection based on address ranges
- **Proven architecture**: Uses production-tested apb_slave/apb_master modules

## Available Modules

| Module | Description | Masters | Slaves | Use Case |
|--------|-------------|---------|--------|----------|
| `apb_xbar_1to1.sv` | Simple passthrough | 1 | 1 | Protocol conversion, testing |
| `apb_xbar_2to1.sv` | Arbitration only | 2 | 1 | Multi-master to single slave |
| `apb_xbar_1to4.sv` | Address decode only | 1 | 4 | Single master to multi-slave |
| `apb_xbar_2to4.sv` | Full crossbar | 2 | 4 | Multi-master to multi-slave |

## Generating Crossbars

### Method 1: Convenience Script (Recommended)

Generate all standard variants:
```bash
cd rtl/amba/apb/xbar/
python generate_xbars.py
```

Generate custom variant:
```bash
python generate_xbars.py --masters 3 --slaves 6
python generate_xbars.py --masters 4 --slaves 8 --base-addr 0x80000000
```

### Method 2: Direct Generator

Use the main generator for more control:
```bash
cd bin/rtl_generators/amba/
python apb_xbar_generator.py --masters 2 --slaves 4 --output ../../../rtl/amba/apb/xbar/apb_xbar_2to4.sv
```

## Address Map

All crossbars use a uniform address mapping (configurable via `BASE_ADDR` parameter):

```
Slave 0: [BASE_ADDR + 0x0000_0000, BASE_ADDR + 0x0000_FFFF]  (64KB)
Slave 1: [BASE_ADDR + 0x0001_0000, BASE_ADDR + 0x0001_FFFF]  (64KB)
Slave 2: [BASE_ADDR + 0x0002_0000, BASE_ADDR + 0x0002_FFFF]  (64KB)
Slave 3: [BASE_ADDR + 0x0003_0000, BASE_ADDR + 0x0003_FFFF]  (64KB)
...
```

**Default BASE_ADDR**: `0x1000_0000`

## Parameters

All modules support these parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ADDR_WIDTH` | 32 | Address bus width |
| `DATA_WIDTH` | 32 | Data bus width |
| `STRB_WIDTH` | DATA_WIDTH/8 | Strobe width (auto-calculated) |
| `BASE_ADDR` | 0x10000000 | Base address for slave address map |

## Usage Example

```systemverilog
apb_xbar_2to4 #(
    .ADDR_WIDTH (32),
    .DATA_WIDTH (32),
    .BASE_ADDR  (32'h8000_0000)
) u_xbar (
    .pclk       (apb_clk),
    .presetn    (apb_rst_n),

    // Master 0 interface
    .m0_apb_PSEL    (m0_psel),
    .m0_apb_PENABLE (m0_penable),
    .m0_apb_PADDR   (m0_paddr),
    .m0_apb_PWRITE  (m0_pwrite),
    .m0_apb_PWDATA  (m0_pwdata),
    .m0_apb_PSTRB   (m0_pstrb),
    .m0_apb_PPROT   (m0_pprot),
    .m0_apb_PRDATA  (m0_prdata),
    .m0_apb_PSLVERR (m0_pslverr),
    .m0_apb_PREADY  (m0_pready),

    // Master 1 interface
    .m1_apb_PSEL    (m1_psel),
    // ... (similar connections)

    // Slave 0-3 interfaces
    .s0_apb_PSEL    (s0_psel),
    // ... (similar connections)
);
```

## Testing

All generated crossbars have corresponding test files in `val/integ_amba/`:

- `test_apb_xbar_1to1.py` - 100+ transactions, variable delay profiles
- `test_apb_xbar_2to1.py` - 130+ transactions, arbitration stress tests
- `test_apb_xbar_1to4.py` - 200+ transactions, address decode validation
- `test_apb_xbar_2to4.py` - 350+ transactions, full crossbar stress

Run tests:
```bash
pytest val/integ_amba/test_apb_xbar_2to4.py -v
pytest val/integ_amba/test_apb_xbar_*.py -v  # All variants
```

## Design Notes

### Arbitration Strategy

- **Round-robin per slave**: Master priority rotates (M0→M1→M0...)
- **Grant persistence**: Once granted, master owns slave until transaction completes
- **Fairness**: No master can starve another master

### Address Decoding

- **Parallel decode**: All masters decode addresses simultaneously
- **Registered routing**: Slave selection registered at command acceptance
- **Response routing**: Based on registered slave selection

### Timing

- **Zero bubble overhead**: Back-to-back transactions supported
- **Single-cycle arbitration**: New grants issued in same cycle as previous completion
- **Pipelined datapath**: Command and response phases overlap different transactions

## Known Limitations

1. **Fixed address map**: 64KB regions per slave
   - Can be changed by modifying generator's `addr_offset` calculation
2. **No slave disable**: All slaves always active
   - Could add enable parameter if needed
3. **No timeout handling**: Assumes slaves always respond
   - Add watchdog if needed for unreliable slaves

## Generating Custom Variants

For variants beyond 16x16, modify generator limits in `apb_xbar_generator.py`:

```python
if M < 1 or M > 16:  # Change 16 to desired max
    raise ValueError(f"Number of masters must be 1-16, got {M}")
```

## Files

- `generate_xbars.py` - Convenience script for generation
- `apb_xbar_1to1.sv` - 1-to-1 passthrough
- `apb_xbar_2to1.sv` - 2-to-1 with arbitration
- `apb_xbar_1to4.sv` - 1-to-4 with address decode
- `apb_xbar_2to4.sv` - 2-to-4 full crossbar
- `README.md` - This file

## References

- APB Specification: ARM IHI 0024C (AMBA APB Protocol v2.0)
- Generator: `projects/components/apb_xbar/bin/apb_xbar_generator.py`
- Base modules: `rtl/amba/apb/apb_slave.sv`, `rtl/amba/apb/apb_master.sv`
- Tests: `val/integ_amba/test_apb_xbar_*.py`

---

**Generated by RTL Design Sherpa** | **Last Updated:** 2025-10-14
