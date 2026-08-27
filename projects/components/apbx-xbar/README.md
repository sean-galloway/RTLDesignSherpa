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

# APB Crossbar Modules

This directory contains the APB crossbar family: a parameterized core plus
generated fixed-configuration variants. Every port independently speaks
**APB4 or APB5**, so one fabric can carry a mix of both.

The `x` in `apbx` is the version wildcard — it is not a separate protocol.

## Architecture

Generated variants follow a consistent design:

```
Master Side:     apb4_slave / apb5_slave convert APB → cmd/rsp interface
Internal:        Round-robin arbitration + address decoding
Slave Side:      apb4_master / apb5_master convert cmd/rsp → APB interface
```

> **`apbx_xbar_thin` is RETIRED (2026-08-27)** and is not a supported
> part of this family. It remains in-tree for reference. Use the
> generated variants instead. Everything below about thin describes a
> retired module, including its known zero-setup-cycle APB deviation
> (APBX-006).

`apbx_xbar_thin` is a different architecture — a combinational passthrough
with weighted round-robin and no cmd/rsp conversion. See
[the docs](../../../docs/markdown/rtl-amba/apbx/README.md) for choosing
between them.

### Key Features

- **Independent arbitration per slave**: Each slave has its own round-robin arbiter
- **Grant persistence**: Grants held from command acceptance through response completion
- **Address decoding**: Automatic slave selection based on address ranges
- **Mixed APB4/APB5**: per-port version selection, sideband gated at both ends
- **Proven architecture**: Uses production-tested apb4/apb5 slave and master modules

### Why mixing needs no converters

APB5 is APB4's transfer protocol plus extra sideband pins — the handshake and
phases are identical. So sideband rides the same select/grant/demux muxes as
`PADDR`, and the version selection only gates *contribution*: an APB4 master
contributes `'0`, and an APB4 slave is never driven with nonzero sideband.
Both gates are compile-time constants, so synthesis prunes any pairing that
cannot occur, and an all-APB4 build is bit-identical to the pre-APB5 crossbar.

One exception in the GENERATED mixed variant: `PWAKEUP` is dropped.
Its boundary IP leaves `rsp_pwakeup` unconnected and ties
`wakeup_request` to '0, so an APB5 slave asserting PWAKEUP is never
seen at the APB5 master. The thin core does route it.

## Available Modules

| Module | Description | Masters | Slaves | Use Case |
|--------|-------------|---------|--------|----------|
| `apbx_xbar_1to1.sv` | Simple passthrough | 1 | 1 | Protocol conversion, testing |
| `apbx_xbar_2to1.sv` | Arbitration only | 2 | 1 | Multi-master to single slave |
| `apbx_xbar_1to4.sv` | Address decode only | 1 | 4 | Single master to multi-slave |
| `apbx_xbar_2to4.sv` | Full crossbar | 2 | 4 | Multi-master to multi-slave |
| `apbx_xbar_2to2_mixed.sv` | Mixed APB4/APB5 | 2 | 2 | m0=APB4, m1=APB5, s0=APB5, s1=APB4 |
| `apbx_xbar_thin.sv` | Parameterized core | M | S | Any topology; versions set by parameter |

## Generating Crossbars

### Method 1: Convenience Script (Recommended)

Generate all standard variants:
```bash
cd projects/components/apbx-xbar/bin/
python generate_xbars.py
```

Generate custom variant:
```bash
python generate_xbars.py --masters 3 --slaves 6
python generate_xbars.py --masters 4 --slaves 8 --base-addr 0x80000000
```

Generate a mixed-version variant — versions are positional per port, and are
baked in at generation time rather than being a runtime parameter:

```python
# in generate_xbars.py
mixed = [
    ((2, 2), ['apb4', 'apb5'], ['apb5', 'apb4'], '_mixed'),
]
```

**`rtl/*.sv` is generator output.** The generator emits the final form (SPDX
banner, `reset_defs.svh` include, reset macros) straight into `rtl/`, so there
is no post-processing step and nothing to hand-edit. Regeneration is
idempotent:

```bash
python3 generate_xbars.py && git status --short ../rtl/   # expect no output
```

### Method 2: Direct Generator

Use the main generator for more control:
```bash
cd projects/components/apbx-xbar/bin/
python apbx_xbar_generator.py --masters 2 --slaves 4 --output ../rtl/apbx_xbar_2to4.sv
```

## Address Map

The GENERATED crossbars (1to1/2to1/1to4/2to4/2to2_mixed) use a uniform address map, configurable via the `BASE_ADDR` parameter. The slave index
is decoded from the OFFSET (`PADDR - BASE_ADDR`), so `BASE_ADDR` needs no
span alignment (the one illegal region is the top S x 64KB of the
address space, where `BASE_ADDR + S*64KB` wraps 32-bit and the range
check can never pass). `apbx_xbar_thin` is different -- see below.

```
Slave 0: [BASE_ADDR + 0x0000_0000, BASE_ADDR + 0x0000_FFFF]  (64KB)
Slave 1: [BASE_ADDR + 0x0001_0000, BASE_ADDR + 0x0001_FFFF]  (64KB)
Slave 2: [BASE_ADDR + 0x0002_0000, BASE_ADDR + 0x0002_FFFF]  (64KB)
Slave 3: [BASE_ADDR + 0x0003_0000, BASE_ADDR + 0x0003_FFFF]  (64KB)
...
```

**Default BASE_ADDR**: `0x1000_0000`

## Parameters

The GENERATED modules support these parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ADDR_WIDTH` | 32 | Address bus width |
| `DATA_WIDTH` | 32 | Data bus width |
| `STRB_WIDTH` | DATA_WIDTH/8 | Strobe width (auto-calculated) |
| `BASE_ADDR` | 0x10000000 | Base of the slave address map |

**`apbx_xbar_thin` does NOT have `BASE_ADDR`.** Its address map is
runtime-programmable through input ports, and it carries its own set of
parameters:

| Parameter / Port | Default | Description |
|------------------|---------|-------------|
| `M`, `S` (params) | 2, 4 | master / slave counts |
| `MAX_THRESH` (param) | 16 | weighted-RR threshold range |
| `MST_APB5`, `SLV_APB5` (params) | '0 | per-port APB5 masks |
| `ENABLE_PARITY` (param) | 0 | end-to-end APB5 parity |
| `SLAVE_ENABLE` (**port**) | — | per-slave enable, `[S-1:0]` |
| `SLAVE_ADDR_BASE` (**port**) | — | per-slave window base |
| `SLAVE_ADDR_LIMIT` (**port**) | — | per-slave window limit |
| `THRESHOLDS` (**port**) | — | weighted-RR weights, `M x $clog2(MAX_THRESH)` |

Its APB pins are packed arrays (`m_apb_psel[M-1:0]`), not the
`m0_apb_PSEL` style of the generated variants. Leaving the four decode
ports undriven means nothing routes.

## Usage Example

```systemverilog
apbx_xbar_2to4 #(
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

All generated crossbars have corresponding test files in `dv/tests/`:

- `test_apbx_xbar_1to1.py` - 100+ transactions, variable delay profiles
- `test_apbx_xbar_2to1.py` - 130+ transactions, arbitration stress tests
- `test_apbx_xbar_1to4.py` - 200+ transactions, address decode validation
- `test_apbx_xbar_2to4.py` - 350+ transactions, full crossbar stress
- `test_apbx_xbar_2to2_mixed.py` - all four version pairings on the generated
  mixed fabric: sideband value where both ends are APB5, no leak anywhere else,
  plus a structural check that APB4 ports carry no sideband pins
- `test_apbx_xbar_thin_mixed.py` - the same pairing matrix against
  `apbx_xbar_thin` with `MST_APB5`/`SLV_APB5` masks

The mixed tests drive their DUT directly; the four legacy tests drive a
`rtl/wrappers/*_wrap.sv` scaffold. Those wrappers are hand-written testbench
scaffolding, not generator output, so a variant gets one only when a test
needs it.

Run tests:
```bash
pytest projects/components/apbx-xbar/dv/tests/test_apbx_xbar_2to4.py -v
pytest projects/components/apbx-xbar/dv/tests/ -v  # All variants
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

- **Back-to-back transactions**: supported with no master-side idle
  cycles; they do not overlap inside the fabric (~10 pclk cycles each)
- **Single-cycle arbitration**: New grants issued the cycle AFTER the previous completion (the
arbiter's grant is registered)
- **Pipelined datapath**: Command and response phases overlap different transactions

## Known Limitations

1. **Fixed address map**: 64KB regions per slave
   - Can be changed by modifying generator's `addr_offset` calculation
2. **No slave disable**: All slaves always active
   - Could add enable parameter if needed
3. **No timeout handling**: Assumes slaves always respond
   - Add watchdog if needed for unreliable slaves

## Generating Custom Variants

For variants beyond 16x16, modify generator limits in `apbx_xbar_generator.py`:

```python
if M < 1 or M > 16:  # Change 16 to desired max
    raise ValueError(f"Number of masters must be 1-16, got {M}")
```

## Files

- `generate_xbars.py` - Convenience script for generation
- `apbx_xbar_1to1.sv` - 1-to-1 passthrough
- `apbx_xbar_2to1.sv` - 2-to-1 with arbitration
- `apbx_xbar_1to4.sv` - 1-to-4 with address decode
- `apbx_xbar_2to4.sv` - 2-to-4 full crossbar
- `README.md` - This file

## References

- APB Specification: ARM IHI 0024C (AMBA APB Protocol v2.0), and IHI 0024E for
  the APB5 sideband signals
- Documentation: [docs/markdown/rtl-amba/apbx/](../../../docs/markdown/rtl-amba/apbx/README.md)
- Generator: `projects/components/apbx-xbar/bin/apbx_xbar_generator.py`
- Base modules: `rtl/amba/apb4/apb4_{slave,master}.sv`,
  `rtl/amba/apb5/apb5_{slave,master}.sv`
- Formal: `formal/apbx_xbar/` (all-APB4 configuration)
- Tests: `dv/tests/test_apbx_xbar_*.py`

## Not implemented

- **APB5 parity across the GENERATED variants** (1to1/2to1/1to4/2to4).
  Their boundary IP deconstructs each transfer into cmd/rsp, so parity
  terminates there and is instantiated with `ENABLE_PARITY=0`.
  `apbx_xbar_thin` is the exception: it passes parity END TO END
  (APBX-003, `ENABLE_PARITY` parameter) because it is a combinational
  mux that never modifies the payload. (There is no `PSELPARITY` signal
  in this library -- the APB5 parity pins are `paddrparity`,
  `pwdataparity`, `pctrlparity`, `prdataparity`, `preadyparity`,
  `pslverrparity`.)
- **Version gating IS formally proven** for the thin core:
  `formal/apbx_xbar/apbx_xbar_thin_mixed` runs the mixed configuration
  (m0=APB4, m1=APB5, s0=APB5, s1=APB4) with `ENABLE_PARITY=1` and
  asserts that APB4 ports never see sideband or parity in either
  direction. The sibling `apbx_xbar_thin` harness proves the all-APB4
  build. What is NOT yet proven formally: the generated MtoN variants
  beyond their existing all-APB4 harnesses.

---

**Generated by RTL Design Sherpa** | **Last Updated:** 2026-08-13
