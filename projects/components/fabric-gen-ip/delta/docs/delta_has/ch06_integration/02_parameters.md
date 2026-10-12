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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Parameter Configuration

## Generated Module Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | CLI `--data-width` | Width of `TDATA` in bits. |
| `DEST_WIDTH` | `clog2(NUM_SLAVES)` | Width of `TDEST`. |
| `ID_WIDTH` | `clog2(NUM_MASTERS)` | Width of `TID`. |
| `USER_WIDTH` | CLI `--user-width` | Width of `TUSER`. |
| `NUM_MASTERS` | CLI `--masters` | Number of master interfaces. |
| `NUM_SLAVES` | CLI `--slaves` | Number of slave interfaces. |
| `STRB_WIDTH` | CLI `--strb-width` | Width of `TSTRB` (only when `--strb-width` is used). |
| `PW_WIDTH` | `DATA_WIDTH/8` (or `--parity-width`) | Width of `TPARITY` (only when `--amba5` is used). |

: Table 6.1: Generated Module Parameters

## Generator CLI Options

| Option | Values | Default | Description |
|--------|--------|---------|-------------|
| `--topology` | `flat` only | `flat` | Crossbar topology (tree/both retired 2026-10-12). |
| `--masters` | 1-32 | required | Number of master interfaces. |
| `--slaves` | 1-256 | required | Number of slave interfaces. |
| `--data-width` | 8-1024 | 64 | `TDATA` width in bits. |
| `--user-width` | 1-32 | 1 | `TUSER` width in bits. |
| `--strb-width` | ≥ 0 | 0 | `TSTRB` width; 0 omits `TSTRB`. |
| `--amba5` | flag | off | Emit AMBA 5 `TWAKEUP` and `TPARITY`. |
| `--parity-width` | ≥ 0 | 0 | Override `TPARITY` width (requires `--amba5`). |
| `--no-counters` | flag | off | Disable packet counters. |
| `--output-dir` | path | `../rtl` | Output directory for generated SystemVerilog. |

: Table 6.2: Generator Command-Line Options

## Example Configurations

### Base flavor 4×16 @ 64-bit

```bash
python3 bin/delta_generator.py \
    --topology flat --masters 4 --slaves 16 --data-width 64 \
    --output-dir rtl/
```

### Rich flavor 2×4 @ 32-bit with TSTRB and AMBA5

```bash
python3 bin/delta_generator.py \
    --topology flat --masters 2 --slaves 4 --data-width 32 \
    --strb-width 4 --amba5 --output-dir rtl_test/
```

### Base flavor without counters

```bash
python3 bin/delta_generator.py \
    --topology flat --masters 4 --slaves 16 --data-width 64 \
    --no-counters --output-dir rtl/
```
