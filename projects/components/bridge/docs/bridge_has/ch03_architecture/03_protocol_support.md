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

# Protocol Support

## Supported Protocols

### AXI4 Full

Complete AMBA AXI4 protocol support:

- **5 channels:** AW, W, B, AR, R
- **Burst transactions:** FIXED, INCR, WRAP
- **Transaction IDs:** Configurable width
- **Out-of-order:** Response reordering supported
- **Data widths:** 32, 64, 128, 256, 512 bits

### AXI4-Lite

Simplified AXI4 for register access:

- **5 channels:** Same as AXI4
- **Single-beat only:** AWLEN/ARLEN = 0
- **No IDs:** Transaction ordering by channel
- **Fixed width:** Typically 32 or 64 bits

### APB (Advanced Peripheral Bus)

Low-power peripheral protocol:

- **Single channel:** Combined address and data
- **Simple handshake:** PSEL, PENABLE, PREADY
- **No bursts:** Single transfer per transaction
- **Low overhead:** Minimal logic for slow peripherals

## Protocol Conversion Matrix

| Master | Slave | Conversion Type | Notes |
|--------|-------|-----------------|-------|
| AXI4 | AXI4 | Direct | Width conversion if needed |
| AXI4 | AXI4-Lite | Downgrade | Burst split to single beats |
| AXI4 | APB | Full convert | Channel and timing conversion |
| AXI4-Lite | AXI4 | Upgrade | Single-beat pass-through |
| AXI4-Lite | AXI4-Lite | Direct | Width conversion if needed |
| AXI4-Lite | APB | Convert | Simplified conversion |

: Table 3.3: Protocol Conversion Matrix

## Automatic Conversion Shims at Slave Boundary

When a slave port's TOML entry names a protocol other than native AXI4 (e.g.,
`protocol = "axil"` or `protocol = "apb"`), the generator emits the conversion
shims between the crossbar core and that slave port. This happens once, at
generation time; there is nothing to configure at runtime.

**Supported Slave Protocols** -- these are the exact TOML values the generator
accepts (`config_validator.valid_protocols`); anything else is a generation
error, so spelling matters:

| `protocol` | Meaning | Shim emitted at the slave boundary |
| --- | --- | --- |
| `axi4` | Native AXI4 | none |
| `axi5` | AXI5, interop mode | `axi5_master_{wr,rd}` boundary wrappers |
| `axil` | AXI4-Lite | `axi4_to_axil4_{rd,wr}` |
| `axil5` | AXI5-Lite | `axi4_to_axil5_{rd,wr}` |
| `apb` | APB3/APB4 | `axi4_to_apb4_shim` |
| `apb5` | APB5 | `axi4_to_apb5_shim` |

: Table 3.4: Slave-port protocol values

Note the spelling: it is `axil`, not `axi4lite`. Earlier revisions of this
page used the latter, which the generator rejects.

The shim modules live in `projects/components/converters/rtl/`; the generator instantiates them into each generated top-level module. The slave port still presents the configured protocol (AXIL or APB) to the outside; inside, the crossbar core is uniformly AXI4.

## AXI4 to APB Conversion

### Conversion Process

### Figure 3.1: AXI4 to APB Conversion Sequence

![AXI4 to APB Conversion](../assets/mermaid/axi4_to_apb4_sequence.png)

### Burst Handling

- AXI4 bursts split into individual APB transfers
- WSTRB converted to per-byte enables
- B response generated after all beats complete

### Timing Considerations

- APB is inherently slower (minimum 2 cycles per transfer)
- Pipeline stalls during APB access
- Consider separate APB crossbar for multiple slow peripherals

## Width Conversion

### Upsize (Narrow to Wide)

### Figure 3.2: Width Upsize Conversion

![Width Upsize](../assets/mermaid/width_upsize_sequence.png)

### Downsize (Wide to Narrow)

### Figure 3.3: Width Downsize Conversion

![Width Downsize](../assets/mermaid/width_downsize_sequence.png)

## Channel-Specific Protocol

### Write-Only Masters

Only AW, W, B channels active:

- AR permanently deasserted
- R channel ignored (no routing logic)
- Reduced signal count and logic

### Read-Only Masters

Only AR, R channels active:

- AW, W, B channels ignored
- No write arbitration for this master
- Reduced signal count and logic
