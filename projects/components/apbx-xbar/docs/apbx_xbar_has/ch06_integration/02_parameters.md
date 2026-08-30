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

# Parameter Configuration

## Module Parameters

### Core Parameters

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| ADDR_WIDTH | int | 32 | 18-64 for decoding variants; 1-64 for 1to1/2to1 | Address bus width in bits. The decode part-select reads bits `16 +: $clog2(S)`, so a 2-slave variant needs only bit 16 -- but the generator emits the range-check span as a fixed 32-bit constant (`paddr < BASE_ADDR + 32'h...`), so anything below 18 width-expands and fails a warnings-fatal build. 17 lints clean only with `-Wno-fatal`; it is not usable. |
| DATA_WIDTH | int | 32 | 8, 16, 32, 64 | Data bus width in bits |
| STRB_WIDTH | int | DATA_WIDTH/8 | derived | Write strobe width. Declared as a parameter, but it is computed from DATA_WIDTH and overriding it is not supported |
| BASE_ADDR | logic[ADDR_WIDTH-1:0] | 0x10000000 | any address; the slave index is decoded from the OFFSET, so no span alignment is required | Base of the slave map. **UNUSED on `1to1` and `2to1`** -- they have a single slave and no decode, so the parameter is declared only for interface uniformity and setting it changes nothing (see those modules' RTL headers) |

: Core Parameter Definition

### Derived Parameters

These are calculated automatically:

| Parameter | Derivation | Description |
|-----------|------------|-------------|
| STRB_WIDTH | DATA_WIDTH / 8 | Byte strobe width |
| (none) | — | Each variant declares only the four parameters above; master/slave counts are baked into the module name and port list, NOT exposed as parameters. |


: Derived Parameters

## Parameter Usage Examples

### Default Configuration

```systemverilog
apbx_xbar_2to4 u_xbar (
    .pclk(apb_clk),
    .presetn(apb_rst_n),
    // ... port connections
);
// Uses defaults: ADDR_WIDTH=32, DATA_WIDTH=32, BASE_ADDR=0x10000000
```

### Custom Base Address

```systemverilog
apbx_xbar_2to4 #(
    .BASE_ADDR(32'h4000_0000)
) u_xbar (
    .pclk(apb_clk),
    .presetn(apb_rst_n),
    // ... port connections
);
// Slaves at 0x4000_0000, 0x4001_0000, 0x4002_0000, 0x4003_0000
```

### 64-bit Data Width

```systemverilog
apbx_xbar_2to4 #(
    .DATA_WIDTH(64)
) u_xbar (
    .pclk(apb_clk),
    .presetn(apb_rst_n),
    // ... port connections with 64-bit data buses
);
// STRB_WIDTH automatically becomes 8
```

### Wide Address

```systemverilog
apbx_xbar_2to4 #(
    .ADDR_WIDTH(40),
    .BASE_ADDR(40'h80_0000_0000)
) u_xbar (
    .pclk(apb_clk),
    .presetn(apb_rst_n),
    // ... port connections with 40-bit address buses
);
```

## Parameter Validation

### Address Width Check

Ensure ADDR_WIDTH can accommodate the full address range:

```
Required minimum: log2(BASE_ADDR + NUM_SLAVES * 64KB)
```

**Example:** 4 slaves at BASE_ADDR=0x1000_0000
- Max address: 0x1000_0000 + 4*0x10000 = 0x1004_0000
- Required: 29 bits minimum
- ADDR_WIDTH=32 is sufficient

### Data Width Constraints

| DATA_WIDTH | STRB_WIDTH | Valid APB Widths |
|------------|------------|------------------|
| 8 | 1 | Yes |
| 16 | 2 | Yes |
| 32 | 4 | Yes (most common) |
| 64 | 8 | Yes |

: Valid Data Width Configurations

## Custom Generation Parameters

When using the Python generator for custom configurations:

```bash
python generate_xbars.py \
    --masters 3 \
    --slaves 6 \
    --base-addr 0x80000000 \
   
```

| Option | Description | Default |
|--------|-------------|---------|
| --masters | Number of master ports | Required |
| --slaves | Number of slave ports | Required |
| --base-addr | Base address (hex) | 0x10000000 |

: Generator Command Line Options

---

**Next:** [Verification Strategy](03_verification.md)
