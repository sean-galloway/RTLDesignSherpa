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

The AXI frontend is `pumice_axi4_ifc` (`rtl/macro/pumice_axi4_ifc.sv`). It bolts the repository's common AXI burst splitters onto two "dumb" 1:1 intakes and holds the two CAMs that decouple AXI-side handshake from the DRAM-side command scheduler:

```
host AXI4 -> [axi_master_wr_splitter] -> pumice_wr_intake -> pumice_wr_data_cam
          -> [axi_master_rd_splitter] -> pumice_rd_intake -> pumice_rd_cmd_cam
```

The intakes each contain a common `axi4_slave` (write or read side) plus an `addr_mapper` that translates the flat AXI address into `(rank, bank, row, col)`. The write intake also carries an AW-meta FIFO and a write-data FIFO; the read intake carries a snarf (read-your-write) probe into the write CAM. This chapter covers the splitters, the intakes, and `addr_mapper`. The two CAMs are covered in the data-paths chapter (`07_data_paths.md`).

## Burst Splitters

`axi_master_wr_splitter` and `axi_master_rd_splitter` are formally-verified common modules. Each host burst is split at DRAM-burst-byte boundaries so every burst that reaches an intake maps to exactly one DRAM burst. The alignment mask is `DRAM_BURST_BYTES - 1`, where `DRAM_BURST_BYTES = BL * (DRAM_BEAT_WIDTH / 8)`. Splitting is transparent to the AXI master: a host burst that crosses a DRAM-burst boundary is decomposed into multiple aligned sub-bursts, each of which becomes one CAM entry / one DRAM command.

## `pumice_wr_intake` / `pumice_rd_intake`

### Purpose

Terminate the AXI channels (via the embedded `axi4_slave`), decode each transaction's address, and push a `{rank, bank, row, col, id}` insert request downstream into the corresponding CAM. The intakes are deliberately "dumb": there is no reordering or scheduling here — that lives in the scheduler layer reading the CAMs.

### Write intake

- Accepts AW transactions and issues an `aw_push` insert into `pumice_wr_data_cam`.
- Streams W beats into the write-data FIFO tagged for the CAM SRAM fill mover.
- Returns the B response when the CAM signals commit-done for the transaction ID (`wr_done_valid` / `wr_done_id`), matching AXI4 posted-write semantics.

### Read intake

- Accepts AR transactions and issues an `ar_push` insert into `pumice_rd_cmd_cam`.
- Before committing a miss to the read CAM, it probes the write CAM with a snarf query (`snarf_probe_*`). On a snarf hit the read is serviced directly from the write CAM's SRAM (read-your-write forwarding) rather than being scheduled to DRAM.
- Drains the read CAM (in AR order) onto the AXI R channel with the correct ID and `rlast`.

### Per-ID Ordering

AXI4 requires reads from the same ID to return in order and writes from the same ID to commit in order. Because each intake inserts in AR/AW arrival order and the read CAM drains in insert order, per-ID ordering is preserved. The CAMs allow row-hit scheduling to reorder DRAM commands across entries, but the AXI completion layer honors per-ID order.

### Backpressure

- AW/AR `.ready` deassert when the corresponding CAM has no free entry (`ins_ready` low).
- W `.ready` deasserts when the write-data FIFO/SRAM fill path is full.
- R and B `.valid` follow standard AXI protocol; a stalled consumer stalls only the drain path and does not corrupt the controller core.

---

## `addr_mapper`

### Purpose

Translate a flat AXI address into DRAM coordinates `(rank, bank, row, col)`. RTL: `rtl/fub/addr_mapper.sv`. It is combinational and single-stage, instantiated inside each intake.

### Interfaces

**Inputs:**

- `axi_addr_i` — `AXI_ADDR_WIDTH` bits
- `bank_lsb_i[4:0]` — the `ADDR_MAP.bank_lsb` CSR field
- `hash_en_i` — the `ADDR_MAP.hash_en` CSR field
- `hash_seed_i[7:0]` — the `ADDR_MAP.hash_seed` CSR field

**Outputs:**

- `rank_o` — `$clog2(NUM_RANKS)` bits
- `bank_o` — `$clog2(NUM_BANKS)` bits
- `row_o` — `ROW_WIDTH` bits
- `col_o` — `COL_WIDTH` bits

### Mapping Function (single knob: `bank_lsb`)

There is **no scheme selector** anymore. The mapping is driven by one runtime knob, `ADDR_MAP.bank_lsb`, which places the bank field within the byte-offset-stripped word address (`word = axi_addr >> BYTE_OFFSET_WIDTH`). The column auto-splits around the bank; row and rank stack above the column region and their positions are **invariant**:

```
word address, low -> high:
[ col_lo(bank_lsb) | bank(BW) | col_hi(CW - bank_lsb) | row(RW) | rank(KW) ]
col = { col_hi, col_lo }
row LSB is always at CW + BW (invariant — only the bank slides)
```

The RTL clamps `bank_lsb` to `[0, COL_WIDTH]` so the `col_hi` width stays non-negative and the row/rank slices land where the geometry expects.

### Classic Schemes as `bank_lsb` Settings

The former named schemes are just settings of the one knob:

| Effect              | Setting                                    | Notes                                              |
|---------------------|--------------------------------------------|----------------------------------------------------|
| `ROW_MAJOR`         | `bank_lsb == COL_WIDTH`                     | Bank above the whole column; default (`0x0A`)      |
| max `BANK_INTERLEAVE` | `bank_lsb == log2(cols/burst)`            | Minimal `col_lo` keeps a DRAM burst inside one bank |
| partial interleave  | any value in between                       | Column splits around the bank                       |

Software keeps `log2(cols/burst) <= bank_lsb <= COL_WIDTH` so a DRAM burst's column walk stays inside one bank.

### Optional Bank XOR-Hash

When `hash_en` is set, the bank index is XOR-folded with row bits and the seed to defeat power-of-two-stride hot-banking (the former `XOR_HASH` scheme, now an orthogonal overlay on any `bank_lsb` placement):

```
bank[i] ^= row[i] ^ row[i + BW] ^ hash_seed[i]
```

The mid-slice index is clamped so it never runs past `ROW_WIDTH`.

### Relationship to the DFI BFM

This module mirrors the `AddressMapping` class in the DFI BFM (`CocoTBFramework/components/dfi/`). The same `bank_lsb` / hash configuration drives both RTL elaboration-time verification and BFM checking, so the address decode is consistent between simulation and silicon.
