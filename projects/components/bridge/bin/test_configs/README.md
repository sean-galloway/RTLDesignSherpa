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

# Bridge Configuration Files

## Current Format: TOML + CSV (Preferred)

Bridge configurations use a hybrid approach:
- **TOML**: Port definitions, interface module configuration, default parameters
- **CSV**: Connectivity matrix (reviewable table format)

**Why TOML?**
- Better structured than CSV (hierarchical, type-safe)
- More maintainable than YAML (simpler syntax, no indentation issues)
- Native support for inline defaults and comments
- Excellent tooling support (linters, formatters, editors)

## File Naming Convention

For a bridge named `bridge_2x2_rw`:
```
bridge_2x2_rw.toml               # Port definitions and interface config
bridge_2x2_rw_connectivity.csv   # Connectivity matrix
```

## Usage

```bash
# Generate bridge from TOML + CSV
cd projects/components/bridge/bin
python3 bridge_generator.py --ports test_configs/bridge_2x2_rw.toml

# Generator automatically finds companion CSV:
# test_configs/bridge_2x2_rw_connectivity.csv

# Or use bulk generation
python3 bridge_generator.py --bulk bridge_batch.csv
```

## Example Configuration

### TOML File (`bridge_2x2_rw.toml`)

Port definitions with interface module configuration:

```toml
[bridge]
  name: bridge_2x2_rw
  description: "2x2 bridge with timing isolation"

  defaults:
    skid_depths: {ar: 2, r: 4, aw: 2, w: 4, b: 2}

  masters:
    - name: cpu
      prefix: cpu_m_axi
      id_width: 4
      addr_width: 32
      data_width: 32
      user_width: 1
      interface:
        type: axi4_master  # Add timing isolation
        # Uses default skid depths

    - name: dma
      prefix: dma_m_axi
      id_width: 4
      addr_width: 32
      data_width: 32
      user_width: 1
      interface:
        type: axi4_master
        skid_depths:
          ar: 4  # Deeper buffers for DMA
          r: 8
          aw: 4
          w: 8
          b: 4

  slaves:
    - name: ddr
      prefix: ddr_s_axi
      id_width: 4
      addr_width: 32
      data_width: 32
      user_width: 1
      base_addr: 0x00000000       # Address mapping
      addr_range: 0x80000000      # 2GB range
      interface:
        type: axi4_slave
        # Uses default skid depths

    - name: sram
      prefix: sram_s_axi
      id_width: 4
      addr_width: 32
      data_width: 32
      user_width: 1
      base_addr: 0x80000000       # Address mapping
      addr_range: 0x80000000      # 2GB range
      interface:
        type: axi4_slave
        skid_depths: {ar: 2, r: 2, aw: 2, w: 2, b: 2}
```

### CSV File (`bridge_2x2_rw_connectivity.csv`)

Connectivity matrix (easy to review as table):

```csv
master\slave,ddr,sram
cpu,1,1
dma,1,1
```

**Format**: First column is `master\slave`, remaining columns are slave names. Values: `1` = connected, `0` = not connected.

**Note**: Address mappings (base_addr, addr_range) are in the YAML file under each slave definition, NOT in the connectivity CSV.

## Why Hybrid Format?

### TOML Benefits (for port config)
- Hierarchical structure for interface modules
- Comments and documentation inline
- Optional fields (e.g., no interface = direct connection)
- Extensible for future features

### CSV Benefits (for connectivity)
- Easy to review as table (spreadsheet-friendly)
- Quick visual verification of address routing
- Simple format for large connectivity matrices
- Familiar to hardware engineers

## Available Examples

### `bridge_2x2_rw.toml` + `bridge_2x2_rw_connectivity.csv`
- Full-featured 2x2 bridge
- Interface modules on all ports
- Different skid depths per port

### `bridge_1x2_wr_matched.toml` + `bridge_1x2_wr_matched_connectivity.csv`
- Minimal 1x2 write-only bridge
- Matched data widths (no conversion needed)
- Useful for testing basic functionality

### `bridge_1x4_rd_apb.toml` + `bridge_1x4_rd_apb_connectivity.csv`
- 1x4 read-only bridge with APB protocol slave
- Demonstrates AXI4-to-APB protocol conversion
- Mixed AXI4 and APB slaves

### `bridge_1x5_rd_axil.toml` + `bridge_1x5_rd_axil_connectivity.csv`
- 1x5 read-only bridge with AXI4-Lite slave
- Demonstrates AXI4-to-AXI4-Lite protocol conversion
- Mixed AXI4, APB, and AXI4-Lite slaves

## Migration from Legacy Formats

**Old CSV Format (two CSV files):**
```
test_2x2_ports.csv          # Port definitions
test_2x2_connectivity.csv   # Connectivity matrix
```

**Old YAML Format (YAML + CSV):**
```
bridge_2x2_rw.yaml               # Port definitions + interface config
bridge_2x2_rw_connectivity.csv   # Connectivity matrix
```

**Current TOML Format (TOML + CSV):**
```
bridge_2x2_rw.toml               # Port definitions + interface config
bridge_2x2_rw_connectivity.csv   # Connectivity matrix (same format!)
```

**Migration Notes:**
- Connectivity CSV format unchanged - same columns, same data
- TOML provides better structure than YAML (simpler syntax, no indentation issues)
- Legacy CSV and YAML formats still supported for backwards compatibility
- New bridges should use TOML for best maintainability

**Conversion Example:**

YAML:
```yaml
bridge:
  name: bridge_2x2_rw
  masters:
    - name: cpu
      prefix: cpu_m_axi
```

TOML:
```toml
[bridge]
  name = "bridge_2x2_rw"
  masters = [
    {name = "cpu", prefix = "cpu_m_axi", ...}
  ]
```

## Interface Module Types

| Type | Description | Modules Used |
|------|-------------|--------------|
| `none` (omit field) | Direct connection, no timing isolation | None |
| `axi4_master` | Timing isolation on master port | `axi4_master_rd.sv` + `axi4_master_wr.sv` |
| `axi4_slave` | Timing isolation on slave port | `axi4_slave_rd.sv` + `axi4_slave_wr.sv` |
| `axi4_master_mon` | Timing + monitoring on master | `axi4_master_rd_mon.sv` + `axi4_master_wr_mon.sv` |
| `axi4_slave_mon` | Timing + monitoring on slave | `axi4_slave_rd_mon.sv` + `axi4_slave_wr_mon.sv` |

## Skid Buffer Depths

Valid depths: 2, 4, 6, 8 (per channel)

Channels:
- `ar`: Read address channel
- `r`: Read data channel
- `aw`: Write address channel
- `w`: Write data channel
- `b`: Write response channel

Defaults: `{ar: 2, r: 4, aw: 2, w: 4, b: 2}`

Override per port or use bridge-level defaults.
