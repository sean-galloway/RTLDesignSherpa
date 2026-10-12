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

# AXIS5 Slave

**Module:** `axis5_slave.sv`
**Location:** `rtl/amba/axis5/`
**Status:** Production Ready

---

## Overview

The AXIS5 Slave implements an AXI5-Stream slave interface with the AMBA5 extensions — wake-up signaling for power management — plus optional interface parity protection (the IHI 0051B ch. 5 check signals). It accepts incoming stream data and buffers it through an internal skid buffer, which is what keeps backpressure off your upstream link.

### Key Features

- AXI4-Stream data path (TDATA, TSTRB, TLAST, TID, TDEST, TUSER, TVALID/TREADY)
- TWAKEUP: Wake-up signaling for power management
- Interface parity (IHI 0051B ch. 5): TDATACHK, TSTRBCHK, TLASTCHK, TIDCHK, TDESTCHK, TUSERCHK, TVALIDCHK, TREADYCHK, TWAKEUPCHK -- odd parity, one check bit per 8 bits, gated by `ENABLE_PARITY`
- Internal skid buffer for backpressure handling
- Configurable data, ID, destination, and user signal widths
- Check-signal error detection (sticky `parity_error`)
- Busy status indication

**Signal coverage:** this module does not implement TKEEP, TPOISON, or any chunking sideband. See [Implemented Signal Set](README.md#implemented-signal-set) for the full list of deviations from the ARM signal set.

### AXIS5 Extensions Over AXIS4

| Feature | AXIS4 | AXIS5 | ARM standard signal? |
|---------|-------|-------|----------------------|
| Wake-up signal | None | TWAKEUP (configurable) | Yes, AXI5-Stream addition |
| Interface parity | None | T*CHK check signals, odd parity, 1 bit per 8 bits (configurable) | Yes, AXI5-Stream ch. 5 (Check_Type = Odd_Parity_Byte_All) |
| Parity error detection | None | Built-in sticky `parity_error` flag | No - implementation status output |

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH | int | 4 | Internal skid buffer depth |
| AXIS_DATA_WIDTH | int | 32 | AXIS data bus width (must be multiple of 8) |
| AXIS_ID_WIDTH | int | 8 | AXIS ID signal width (0 to disable) |
| AXIS_DEST_WIDTH | int | 4 | AXIS TDEST signal width (0 to disable) |
| AXIS_USER_WIDTH | int | 1 | AXIS TUSER signal width (0 to disable) |
| ENABLE_WAKEUP | bit | 1 | Enable TWAKEUP signal (1=enabled) |
| ENABLE_PARITY | bit | 0 | Enable the IHI 0051B ch. 5 check signals (1 = Check_Type Odd_Parity_Byte_All, 0 = False) |

**Note on `ENABLE_WAKEUP`:** the default is 1, so TWAKEUP ports exist and are carried through the buffer unless you explicitly set `ENABLE_WAKEUP=0`. Set it to 0 for an AXI4-Stream-compatible port list with no wake-up sideband and slightly less area. `ENABLE_PARITY` defaults to 0, the spec's `Check_Type = False`: the `*chk` ports are still present but outputs are tied 0 and inputs are ignored.

### Derived Values (do not override)

These are declared in the parameter list so they can be used in port widths, but they are derived from the parameters above. Overriding them directly produces an inconsistent module.

| Name | Derivation | Meaning |
|------|------------|---------|
| DW | AXIS_DATA_WIDTH | Data width short name |
| IW | AXIS_ID_WIDTH | ID width short name |
| DESTW | AXIS_DEST_WIDTH | DEST width short name |
| UW | AXIS_USER_WIDTH | USER width short name |
| SW | DW/8 | Strobe width in bytes |
| IW_WIDTH / DESTW_WIDTH / UW_WIDTH | max(width, 1) | Zero-width avoidance for disabled sidebands |
| TDATACHK_W | SW | TDATACHK width, TDATA_WIDTH/8 (Table 5-1) |
| TSTRBCHK_W | ceil(SW/8) | TSTRBCHK width, ceil(TDATA_WIDTH/64) |
| TIDCHK_W / TDESTCHK_W / TUSERCHK_W | ceil(width/8) | TIDCHK / TDESTCHK / TUSERCHK widths |

`TSize` (skid payload width) is a body `localparam` now, not a parameter.

---

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXIS clock |
| aresetn | 1 | Input | AXIS active-low asynchronous reset |

### Slave AXIS5 Interface (Input Side)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_axis_tdata | DW | Input | Transfer data from upstream |
| s_axis_tstrb | SW | Input | Transfer byte strobes |
| s_axis_tlast | 1 | Input | Last transfer in packet |
| s_axis_tid | IW_WIDTH | Input | Transfer ID (optional) |
| s_axis_tdest | DESTW_WIDTH | Input | Transfer destination (optional) |
| s_axis_tuser | UW_WIDTH | Input | Transfer user-defined signals (optional) |
| s_axis_tvalid | 1 | Input | Transfer valid from upstream |
| s_axis_tready | 1 | Output | Transfer ready (skid buffer not full) |
| s_axis_twakeup | 1 | Input | Wake-up signal (AXIS5 extension) |
| s_axis_tdatachk | TDATACHK_W | Input | TDATACHK: odd parity, bit n covers tdata[8n+7:8n] |
| s_axis_tstrbchk | TSTRBCHK_W | Input | TSTRBCHK: odd parity over tstrb, 1 bit per 8 strobes |
| s_axis_tlastchk | 1 | Input | TLASTCHK |
| s_axis_tidchk | TIDCHK_W | Input | TIDCHK |
| s_axis_tdestchk | TDESTCHK_W | Input | TDESTCHK |
| s_axis_tuserchk | TUSERCHK_W | Input | TUSERCHK |
| s_axis_tvalidchk | 1 | Input | TVALIDCHK, checked every cycle out of reset |
| s_axis_treadychk | 1 | Output | TREADYCHK = ~s_axis_tready, generated here every cycle |
| s_axis_twakeupchk | 1 | Input | TWAKEUPCHK, checked every cycle when ENABLE_WAKEUP=1 |

### FUB AXIS5 Interface (Output Side to Backend)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axis_tdata | DW | Output | Transfer data to backend |
| fub_axis_tstrb | SW | Output | Transfer byte strobes |
| fub_axis_tlast | 1 | Output | Last transfer in packet |
| fub_axis_tid | IW_WIDTH | Output | Transfer ID (optional) |
| fub_axis_tdest | DESTW_WIDTH | Output | Transfer destination (optional) |
| fub_axis_tuser | UW_WIDTH | Output | Transfer user-defined signals (optional) |
| fub_axis_tvalid | 1 | Output | Transfer valid to backend |
| fub_axis_tready | 1 | Input | Transfer ready from backend |
| fub_axis_twakeup | 1 | Output | Wake-up signal (AXIS5 extension) |
| fub_axis_tdatachk | TDATACHK_W | Output | TDATACHK, carried with the beat |
| fub_axis_tstrbchk | TSTRBCHK_W | Output | TSTRBCHK, carried |
| fub_axis_tlastchk | 1 | Output | TLASTCHK, carried |
| fub_axis_tidchk | TIDCHK_W | Output | TIDCHK, carried |
| fub_axis_tdestchk | TDESTCHK_W | Output | TDESTCHK, carried |
| fub_axis_tuserchk | TUSERCHK_W | Output | TUSERCHK, carried |

### Status Outputs

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| busy | 1 | Output | Module busy (data in buffer or input valid) |
| parity_error | 1 | Output | Sticky: a payload check mismatched on an s_axis TVALID cycle, or TVALIDCHK/TWAKEUPCHK was not the inversion of its signal |

---

## Functional Description

```mermaid
flowchart TB
    subgraph INPUT["Slave AXIS5 Interface (Input)"]
        s_tdata["s_axis_tdata"]
        s_tvalid["s_axis_tvalid"]
        s_tready["s_axis_tready"]
        s_twakeup["s_axis_twakeup"]
        s_tchk["s_axis_t*chk<br/>tvalidchk / twakeupchk"]
    end

    subgraph PARITY_IN["Input Check-signal Check (ENABLE_PARITY)"]
        calc_in["dataint_parity per 8-bit piece<br/>(odd, CHUNKS=1)"]
        cmp_in["Compare with<br/>s_axis_t*chk"]
        err["parity_error<br/>flag"]
    end

    subgraph PACK["Packet Packing"]
        pack["Pack signals based on<br/>ENABLE_WAKEUP/ENABLE_PARITY"]
    end

    subgraph SKID["Skid Buffer"]
        sb["gaxi_skid_buffer<br/>Depth: SKID_DEPTH"]
    end

    subgraph UNPACK["Packet Unpacking"]
        unpack["Unpack to FUB signals"]
    end

    subgraph OUTPUT["FUB AXIS5 Interface (Output)"]
        fub_tdata["fub_axis_tdata"]
        fub_tvalid["fub_axis_tvalid"]
        fub_tready["fub_axis_tready"]
        fub_twakeup["fub_axis_twakeup"]
        fub_tchk["fub_axis_t*chk"]
    end

    INPUT --> PARITY_IN
    PARITY_IN --> err
    INPUT --> PACK
    PACK --> SKID
    SKID --> UNPACK
    UNPACK --> OUTPUT

    style PARITY_IN fill:#fff4e6
    style err fill:#ffe6e6
```

### Skid Buffer Operation

The module uses an internal `gaxi_skid_buffer` to:
- Accept incoming transfers even when backend is not ready
- Prevent backpressure to upstream
- Provide registered outputs for timing closure
- Track buffer occupancy via `busy` signal

### Packet Packing/Unpacking

**Conditional packing based on configuration:**

```systemverilog
// Full feature set (ENABLE_WAKEUP=1, ENABLE_PARITY=1)
{tdata, tstrb, tlast, tid, tdest, tuser, twakeup, tdatachk, tstrbchk, tlastchk, tidchk, tdestchk, tuserchk}

// Wake-up only (ENABLE_WAKEUP=1, ENABLE_PARITY=0)
{tdata, tstrb, tlast, tid, tdest, tuser, twakeup}

// Parity only (ENABLE_WAKEUP=0, ENABLE_PARITY=1)
{tdata, tstrb, tlast, tid, tdest, tuser, tdatachk, tstrbchk, tlastchk, tidchk, tdestchk, tuserchk}

// Base AXIS4 (ENABLE_WAKEUP=0, ENABLE_PARITY=0)
{tdata, tstrb, tlast, tid, tdest, tuser}
```

### Interface Parity (ENABLE_PARITY=1)

The check signals follow IHI 0051B ch. 5 with `Check_Type = Odd_Parity_Byte_All`:

- **Odd parity** (§5.3): a check bit plus the bits it covers always hold an odd number of ones.
- **Granularity** (§5.3, Table 5-1): check bit [n] covers bits [8n+7:8n] of its signal; when the signal is not a whole number of bytes, the top check bit covers the short remainder. TDATACHK is TDATA_WIDTH/8 bits, TSTRBCHK ceil(TDATA_WIDTH/64), TIDCHK/TDESTCHK/TUSERCHK ceil(width/8), and TLASTCHK, TVALIDCHK, TREADYCHK, TWAKEUPCHK one bit each (a one-bit check is the inversion of its signal).
- Every check bit is computed by one `rtl/common/dataint_parity` instance (`CHUNKS=1`, `parity_type=0` = odd) over its own piece, which gives the spec layout at any width.

What this module does with each signal:

| Check signal | Here | Check Enable (Table 5-1) |
|--------------|------|--------------------------|
| TDATACHK, TSTRBCHK, TLASTCHK, TIDCHK, TDESTCHK, TUSERCHK | Checked on `s_axis`, then carried through the skid buffer to `fub_axis_t*chk` | TVALID |
| TVALIDCHK | Input, checked against `~s_axis_tvalid` | ARESETn (every cycle) |
| TWAKEUPCHK | Input, checked against `~s_axis_twakeup` (only when `ENABLE_WAKEUP=1`) | ARESETn |
| TREADYCHK | Generated: `s_axis_treadychk = ~s_axis_tready` | ARESETn |

`parity_error` latches (until reset) on any payload mismatch in a cycle where `s_axis_tvalid` is high, whether or not the beat is accepted, or on any cycle where TVALIDCHK or TWAKEUPCHK is wrong. When a parameter removes TID, TDEST or TUSER, the spec omits its check (§5.3): the input is ignored and the `fub_axis` check output is driven as the odd parity of the tied-zero field.

Checking at the input covers the upstream link and catches errors as early as possible. This is the receiver-side check of the pair; `axis5_master` checks on its output side, which covers its own internal data path.

### Busy Signal

The `busy` output indicates:
- Input side has valid data (`s_axis_tvalid`)
- Skid buffer contains data (`int_t_count > 0`)

---

## Timing Characteristics
### Basic Receive with Wake-up

<!-- TODO: Add wavedrom timing diagram for AXIS5 receive with wake-up -->
> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - aclk
> - s_axis_tvalid/tready
> - s_axis_tdata
> - s_axis_tlast
> - s_axis_twakeup (AXIS5 extension)
> - fub_axis_tvalid/tready
> - fub_axis_tdata
> - fub_axis_twakeup
> - busy

### Receive with Parity Error

<!-- TODO: Add wavedrom timing diagram for parity error detection -->
> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - aclk
> - s_axis_tdata
> - s_axis_tvalid, s_axis_tvalidchk
> - s_axis_tdata, s_axis_tdatachk (received)
> - parity_error (sticky flag set)

### Skid Buffer Backpressure from Backend

<!-- TODO: Add wavedrom timing diagram for backend backpressure -->
> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - aclk
> - s_axis_tvalid/tready
> - fub_axis_tvalid/tready (backend blocked)
> - int_t_count (buffer fill level)
> - busy

---

## Usage Examples

Every parameter and port below is read from the module declaration.

```systemverilog
axis5_slave #(
    .SKID_DEPTH            (4),
    .AXIS_DATA_WIDTH       (32),
    .AXIS_ID_WIDTH         (8),
    .AXIS_DEST_WIDTH       (4),
    .AXIS_USER_WIDTH       (1),
    .ENABLE_WAKEUP         (1),
    .ENABLE_PARITY         (0)
) u_axis5_slave (
    .aclk                  (aclk),
    .aresetn               (aresetn),
    .s_axis_tdata          (s_axis_tdata),
    .s_axis_tstrb          (s_axis_tstrb),
    .s_axis_tlast          (s_axis_tlast),
    .s_axis_tid            (s_axis_tid),
    .s_axis_tdest          (s_axis_tdest),
    .s_axis_tuser          (s_axis_tuser),
    .s_axis_tvalid         (s_axis_tvalid),
    .s_axis_tready         (s_axis_tready),
    .s_axis_twakeup        (s_axis_twakeup),
    .s_axis_tdatachk       (s_axis_tdatachk),
    .s_axis_tstrbchk       (s_axis_tstrbchk),
    .s_axis_tlastchk       (s_axis_tlastchk),
    .s_axis_tidchk         (s_axis_tidchk),
    .s_axis_tdestchk       (s_axis_tdestchk),
    .s_axis_tuserchk       (s_axis_tuserchk),
    .s_axis_tvalidchk      (s_axis_tvalidchk),
    .s_axis_treadychk      (s_axis_treadychk),
    .s_axis_twakeupchk     (s_axis_twakeupchk),
    .fub_axis_tdata        (fub_axis_tdata),
    .fub_axis_tstrb        (fub_axis_tstrb),
    .fub_axis_tlast        (fub_axis_tlast),
    .fub_axis_tid          (fub_axis_tid),
    .fub_axis_tdest        (fub_axis_tdest),
    .fub_axis_tuser        (fub_axis_tuser),
    .fub_axis_tvalid       (fub_axis_tvalid),
    .fub_axis_tready       (fub_axis_tready),
    .fub_axis_twakeup      (fub_axis_twakeup),
    .fub_axis_tdatachk     (fub_axis_tdatachk),
    .fub_axis_tstrbchk     (fub_axis_tstrbchk),
    .fub_axis_tlastchk     (fub_axis_tlastchk),
    .fub_axis_tidchk       (fub_axis_tidchk),
    .fub_axis_tdestchk     (fub_axis_tdestchk),
    .fub_axis_tuserchk     (fub_axis_tuserchk),
    .busy                  (busy),
    .parity_error          (parity_error)
);
```

## Design Notes

### AXIS5 vs AXIS4 Differences

| Feature | AXIS4 | AXIS5 |
|---------|-------|-------|
| Wake-up signal | Not supported | TWAKEUP (optional) |
| Interface parity | Not supported | IHI 0051B ch. 5 T*CHK check signals (optional) |
| Power management | Limited | Enhanced via TWAKEUP |
| Data integrity | CRC/checksum in TUSER | Odd-parity check signals option |

### Parity Check Location

**Key difference from AXIS5 Master:**
- **Slave:** checks on **input** (`s_axis_t*` vs `s_axis_t*chk`, plus TVALIDCHK/TWAKEUPCHK), and generates TREADYCHK
- **Master:** checks on **output** (`m_axis_t*` vs the carried `m_axis_t*chk`, plus TREADYCHK), and generates TVALIDCHK/TWAKEUPCHK

Checking at the input means transmission errors get caught at the receiving side, as early as possible.

### Skid Buffer Sizing

- **Typical depth:** 4-8 entries
- Deeper buffers:
  - Absorb longer backend stalls
  - Increase area and latency
- Shallower buffers:
  - Lower latency
  - May cause upstream backpressure

**Recommendation:** depth 4 covers most applications; go deeper if your backend stalls frequently.

### Parity Implementation

When `ENABLE_PARITY=1`:
- **Overhead:** 1 bit per 8 bits of every protected signal (a 512-bit TDATA adds 64 TDATACHK bits and 8 TSTRBCHK bits), plus 1 bit each for TLAST, TVALID, TREADY and TWAKEUP
- **Detection:** Any odd number of bit errors within an 8-bit piece; two flipped bits in the same piece are undetected
- **Correction:** None - error flag only
- **Polarity:** Odd, as IHI 0051B §5.3 requires; there is no parameter to select even parity
- **Use case:** Low-cost error detection in reliable environments

For stronger protection, use:
- CRC in TUSER field
- ECC (external module)
- End-to-end checksums at packet level

### Error Handling Strategy

The `parity_error` flag is **sticky** (latches high until reset):
- Simplifies error detection (level-sensitive interrupt)
- Software must clear by resetting module
- For edge-sensitive interrupts, external logic must detect rising edge

**Alternative:** modify the module to add a `parity_error_clear` input if your system needs one.

---

## Related Modules

- **[AXIS5 Master](axis5_master.md)** - AXIS5 master interface (transmit side)
- **[AXIS5 Slave CG](axis5_slave_cg.md)** - Clock-gated variant with power management
- **[AXIS5 Master CG](axis5_master_cg.md)** - Clock-gated master variant
- **[AXIS4 Slave](../axis4/axis4_slave.md)** - AXIS4 version for comparison
- **[AMBA5 Overview](../overview.md)** - AMBA5 specifications and extensions

---

## Testing

`val/amba/test_axis5_slave.py` exercises this module. It collects 3 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_axis5_slave.py -v
```

## References

- Arm. *AMBA AXI-Stream Protocol Specification*, ARM IHI 0051B, Apr. 2021 (defines AXI4-Stream and AXI5-Stream). [developer.arm.com/documentation/ihi0051/b](https://developer.arm.com/documentation/ihi0051/b/) — §2.2 "Handshake signaling", §2.3 "Wake-up signaling" (`TWAKEUP`), ch. 5 "Interface parity protection" (§5.3 odd parity and the 8-bit granularity, Table 5-1 check-signal names, widths and Check Enable terms), implemented here as specified when `ENABLE_PARITY=1` (issue #102). Citation only.
- Carloni, L.P., McMillan, K.L., Sangiovanni-Vincentelli, A.L. "Theory of Latency-Insensitive Design." *IEEE Trans. Computer-Aided Design of Integrated Circuits and Systems*, 20(9), Sept. 2001. DOI: [10.1109/43.945302](https://doi.org/10.1109/43.945302) — the valid/ready channel discipline behind the `gaxi_skid_buffer` queues: a buffered stage may stall or add latency without changing what the endpoints compute.
- Maaref, M. *Architecting and Building High-Speed SoCs*, Packt, 2022, ch. 3 "Basic and Advanced On-Chip Busses and Interconnects", section "ARM AMBA interconnect protocols suite" (AXI Stream bus protocol overview) — textbook treatment (secondary source).
- Chipressian. *Crack the Hardware Interview - from RTL Designers' Perspective*, Part 2 ch. 2 "Handshake Protocols" (valid-ready protocol and valid-ready slices) — textbook treatment of the skid buffer (secondary source).
- Indexed in `rtl/amba/references/README.md` (local PDF: `LatencyInsensitiveDesign__Carloni2001.pdf`)

---

## Navigation

- **[← Back to AXIS5 Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
