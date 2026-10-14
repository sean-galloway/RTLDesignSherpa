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

# AXI4 Frontend

The AXI4 frontend is the host-facing boundary of the pumice controller. In `pumice_core` it is instantiated as `mc_axi4_plane` from the common memory-controller stack, the first plane on the controller clock (`aclk`). It terminates the host AXI4 channels, chops and splits host bursts into DFI-burst-sized descriptors, and hands those descriptors across the descriptor seam to `mc_storage_plane`. The descriptor seam contract is documented in the family architecture specification ([`common_has` chapter 2](../../../../../common-ip/docs/common_has/ch02_architecture/02_descriptor_seam.md)); the plane's internals are documented in the family microarchitecture specification ([`common_mas` chapter 2](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md)).

Until 2026-10-09 this functionality lived in the pumice-local `pumice_axi4_plane` (`rtl/macro/pumice_axi4_plane.sv`), which was removed during the Phase-2 common-stack extraction.

## What pumice consumes from the common stack

`mc_axi4_plane` provides:

- host AXI4 slave termination and burst chop/split (`mc_wr_splitter`, `mc_axi_burst_chopper`);
- write and read intakes (`mc_wr_intake`, `mc_rd_intake`) that push decoded descriptors into the storage plane;
- the read-return ring (`mc_rd_return_ring`) that decouples in-flight read count from CAM depth and enforces AXI per-ID ordering;
- the snarf probe path that lets reads hit unscheduled writes in the write-data CAM.

Pumice instantiates this plane with `DRAM_BEAT_WIDTH = DW` (the DFI word width) and `AXI_BEATS_PER_BURST = BURST_WORDS`, so one AXI beat equals one DFI word and the front end remains DFI-word granular. Sub-DFI-word burst expansion is handled downstream in `mc_dfi_2p1_plane`.

## What pumice configures

### Address mapping (`mc_addr_mapper`)

The flat-AXI-address to `{rank, bank, row, col}` decode is performed inside `mc_axi4_plane`: each intake (`mc_wr_intake`, `mc_rd_intake`) instantiates the common `mc_addr_mapper` (`common-ip/rtl/fub/mc_addr_mapper.sv`) and pushes the decoded coordinates across the descriptor seam. There is no pumice-local mapper. What pumice owns is the configuration: the mapping knobs are runtime CSRs in the `ADDR_MAP` register:

| Field | Width | Role |
|-------|-------|------|
| `ADDR_MAP.bank_lsb` | 5 | Bank-field LSB in the byte-offset-stripped word address |
| `ADDR_MAP.hash_en`  | 1 | Enable bank XOR-hash |
| `ADDR_MAP.hash_seed`| 8 | XOR-hash seed |

#### Mapping function (single knob: `bank_lsb`)

There is **no scheme selector** anymore. The mapping is driven by one runtime knob, `ADDR_MAP.bank_lsb`, which places the bank field within the byte-offset-stripped word address (`word = axi_addr >> BYTE_OFFSET_WIDTH`). The column auto-splits around the bank; row and rank stack above the column region and their positions are **invariant**:

```
word address, low -> high:
[ col_lo(bank_lsb) | bank(BW) | col_hi(CW - bank_lsb) | row(RW) | rank(KW) ]
col = { col_hi, col_lo }
row LSB is always at CW + BW (invariant — only the bank slides)
```

The RTL clamps `bank_lsb` to `[0, COL_WIDTH]` so the `col_hi` width stays non-negative and the row/rank slices land where the geometry expects.

#### Classic schemes as `bank_lsb` settings

| Effect              | Setting                                    | Notes                                              |
|---------------------|--------------------------------------------|----------------------------------------------------|
| `ROW_MAJOR`         | `bank_lsb == COL_WIDTH`                     | Bank above the whole column; default (`0x0A`)      |
| max `BANK_INTERLEAVE` | `bank_lsb == log2(DRAM_BL)`              | Minimal `col_lo` keeps a DRAM burst inside one bank |
| partial interleave  | any value in between                       | Column splits around the bank                       |

Software keeps `log2(DRAM_BL) <= bank_lsb <= COL_WIDTH` so a DRAM burst's column walk stays inside one bank. (`DRAM_BL`, not `cols/burst` and not `BL/DFI_RATE` — the mapper indexes device words, so a burst spans `DRAM_BL` columns here; measured in `dv/tests/fub/test_addr_mapper.py::minimum_bank_lsb_is_measured`. pumice BUG-022.)

#### Optional bank XOR-hash

When `hash_en` is set, the bank index is XOR-folded with row bits and the seed to defeat power-of-two-stride hot-banking (the former `XOR_HASH` scheme, now an orthogonal overlay on any `bank_lsb` placement):

```
bank[i] ^= row[i] ^ row[i + BW] ^ hash_seed[i]
```

The mid-slice index is clamped so it never runs past `ROW_WIDTH`.

### AXI gearing wrapper (`pumice_top_geared`)

`pumice_top_geared` (`rtl/top/pumice_top_geared.sv`) is a pumice-specific wrapper around `pumice_top` that allows the host AXI data width to differ from the controller's fixed DFI-word width. It inserts the repository's formally-verified AXI data-width converters (`axi4_dwidth_converter_wr` / `axi4_dwidth_converter_rd`) between a host-width AXI slave and the `pumice_top` AXI interface. When `HOST_AXI_DATA_WIDTH == DW` the converters are bypassed by generate so the build is bit-identical to `pumice_top`. The wrapper enforces a compile-time power-of-two ratio between host width and DFI word width.

### Observed status registers

`pumice_top` captures controller-level status into the PeakRDL-generated CSR. AXI-frontend-relevant observable registers include:

- `STATUS.init_done` — initialization complete;
- `ADDR_MAP.bank_lsb`, `ADDR_MAP.hash_en`, `ADDR_MAP.hash_seed` — address-map controls.

The per-bank/page statistics, stall counters, and training-plane status are produced by downstream planes and are described in the data-paths, scheduler, and training chapters.
