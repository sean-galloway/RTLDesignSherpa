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

# AXI4 Slave + Intakes (`axi4_slave_wr` / `axi4_slave_rd`)

**Modules:** `axi4_slave_wr` / `axi4_slave_rd` (repo AMBA IP) inside
`pumice_wr_intake` / `pumice_rd_intake`
**Location:** intakes in `rtl/fub/`; slaves in the shared AMBA library
**Category:** FUB (intakes)
**Parent:** `pumice_axi4_ifc`
**Status:** Implemented

> **Rearchitected:** the SWAG had a single `axi4_slave_fub` that also owned
> transaction state and an R-emit FSM. That block is retired. In the live design
> the AXI4 protocol engine is the repo's `axi4_slave_wr` / `axi4_slave_rd` skid
> IP, and each is wrapped by a thin **intake** FUB (`pumice_wr_intake`,
> `pumice_rd_intake`) that is FIFO-based and FSM-free. All in-flight transaction
> state lives downstream in the two CAMs (see [ch02/04](04_rd_cmd_cam.md),
> [ch02/05](05_wr_cmd_cam.md)).

---

## Purpose

The host-facing AXI4 protocol handling is split by direction and factored into
two layers each:

- **`axi4_slave_wr` / `axi4_slave_rd`** — the repo's standard AXI4 slave skid
  buffers. They do the channel handshakes, provide `SKID_DEPTH_*` buffering, and
  present a clean post-skid "fub" face (`fub_axi_*`).
- **`pumice_wr_intake` / `pumice_rd_intake`** — the pumice-specific intake FUBs
  that sit on the post-skid face. They decode the burst address via
  `addr_mapper`, push a decoded command downstream to a CAM, stream write/read
  data through FIFOs, and return B/R responses.

Ahead of both intakes, `pumice_axi4_ifc` places the repo's
`axi_master_wr_splitter` / `axi_master_rd_splitter` so that each burst delivered
to an intake is **exactly one DRAM burst** (aligned to `DRAM_BURST_BYTES =
BL * DRAM_BEAT_WIDTH/8`). The intakes therefore assume "one AXI burst == one DFI
burst" and carry no burst-splitting logic.

## `pumice_wr_intake` — structure

Exactly three things plus the address decoder, per the locked µarch spec:

1. **`axi4_slave_wr` (`u_slave_wr`)** — AXI protocol / skid buffering. Parameters
   `SKID_DEPTH_AW=2`, `SKID_DEPTH_W=4`, `SKID_DEPTH_B=2`.
2. **AW-meta FIFO (`u_aw_meta_fifo`)** — a `gaxi_fifo_sync`, depth `AW_FIFO_DEPTH`
   (4), width `AWM_W = 1 + IW + AW`, capturing `{err, awid, awaddr}` per burst.
3. **wr-data FIFO (`u_wr_data_fifo`)** — a `gaxi_fifo_sync`, depth
   `WDATA_FIFO_DEPTH` (16), width `WD_W = 1 + SW + DW`, capturing
   `{wlast, wstrb, wdata}` per AXI beat.
4. **`addr_mapper` (`u_addr_mapper`)** — combinational decode of the FIFO-head
   address into `{rank, bank, row, col}` for the downstream `aw_push`.

Plus a **B-response FIFO (`u_b_fifo`)**, depth `B_FIFO_DEPTH` (4), width
`B_W = 2 + IW`.

### Write data flow

1. **AW intake** — `fub_awvalid` writes `{err, awid, awaddr}` into the AW-meta
   FIFO. `fub_awready = w_awm_wr_ready` (accept while the FIFO has room).
2. **W intake** — `fub_wvalid` writes `{wlast, wstrb, wdata}` into the wr-data
   FIFO; `fub_wready = w_wd_wr_ready`. AW and W are decoupled — each has its own
   FIFO.
3. **Decode + push** — the AW-meta FIFO head address is decoded by `addr_mapper`;
   the decoded `{bank, row, col, id, err}` is presented on `aw_push_*` and
   valid whenever the AW-meta FIFO is non-empty. It pops on the downstream
   `aw_push_ready_i` handshake. (`aw_push_rank_o` is driven but left unconnected
   at the IFC — single-rank pick.)
4. **wr-data pop** — the wr-data FIFO head is exposed on `wdata_*` and drained by
   the wr-data CAM (`wdata_ready_i`) in commit order.
5. **B response** — a completed commit strobes `wr_done_valid_i` / `wr_done_id_i`
   from the CAM; that pushes `{resp, id}` into the B FIFO, which drives the
   AXI B channel.

### Ragged-burst handling

The intake computes `w_aw_err = ((awlen+1)*GEAR != BL)` where
`GEAR = AXI_DATA_WIDTH / DRAM_BEAT_WIDTH`. On a ragged burst the intake
**self-generates** a `SLVERR` B response at the `aw_push` pop (err takes
priority over a `wr_done`), and the downstream CAM drops the illegal command. A
simulation `$error` fires when `RAGGED_ASSERT != 0` (a guardrail under
`translate_off`); a companion assertion catches a B-push collision between the
err path and a same-cycle `wr_done`.

## `pumice_rd_intake` — structure

Mirror of the write intake, plus the read **snarf** path:

1. **`axi4_slave_rd` (`u_slave_rd`)** — AXI protocol / skid buffering
   (`SKID_DEPTH_AR=2`, `SKID_DEPTH_R=4`).
2. **`addr_mapper` (`u_addr_mapper`)** — decode `fub_araddr` → `{rank, bank,
   row, col}` at the AR inlet (combinational).
3. **Snarf probe** — the decoded `{bank, row, col, id, len}` is presented on the
   `snarf_probe_*` ports every cycle `fub_arvalid` is high; the wr-data CAM
   returns a combinational `snarf_hit_i`.
4. **Order FIFO (`u_order_fifo`)** — a `gaxi_fifo_sync`, depth `ORDER_FIFO_DEPTH`
   (8), width `ORD_W = 1 + IW`, storing `{source, id}` per admitted read to
   preserve AR order (`SRC_SNARF=1`, `SRC_DFI=0`).
5. **Source arbiter** — a combinational mux selecting the snarf stream or the DFI
   read-return stream by the order-FIFO head's `source` tag.
6. **rd-data FIFO (`u_rd_data_fifo`)** — a `gaxi_fifo_sync`, depth
   `RD_FIFO_DEPTH` (16), width `RD_W = 2 + 1 + IW + DW` = `{resp, last, id,
   data}`, feeding the AXI R channel.

### Read admission and ordering

- An AR is admitted (`w_can_admit`) when the order FIFO has room **and**, for a
  MISS, `ar_push_ready_i` is asserted. `fub_arready = w_can_admit`.
- On a **HIT** (`snarf_hit_i`) the read is tagged `SRC_SNARF`, `snarf_accept_o`
  fires, and no `ar_push` is emitted (the data is streamed from the write CAM's
  SRAM — DRAM is stale for the in-flight write).
- On a **MISS** the read is tagged `SRC_DFI` and `ar_push_valid_o` fires with the
  decoded `{bank, row, col, id}` toward the scheduler / rd CAM.
- The source arbiter drains one burst at a time in AR order: the order-FIFO head's
  `source` selects which input stream is connected to the rd-data FIFO, and the
  head is popped only when the last beat of that burst is accepted. So a
  snarf-ready read still waits behind an earlier DFI read at the head (in-order R
  per the AXI contract).

## External interface

Both intakes present a full AXI4 write (AW/W/B) or read (AR/R) slave face plus:

| Port group        | Direction | Purpose                                             |
|-------------------|-----------|-----------------------------------------------------|
| `bank_lsb_i` / `hash_en_i` / `hash_seed_i` | in | `ADDR_MAP` config forwarded to `addr_mapper` |
| `aw_push_*` / `ar_push_*` | out | Decoded command to the wr/rd CAM              |
| `wdata_*` (wr)    | out       | Write-data pop to the wr-data CAM                   |
| `wr_done_*` (wr)  | in        | Commit-completion strobe from the CAM → B response  |
| `snarf_probe_*` / `snarf_hit_i` / `snarf_accept_o` (rd) | in/out | Read-your-write probe into the wr CAM |
| `snarf_rd_*` (rd) | in        | Snarf data stream from the wr CAM SRAM              |
| `dfi_rd_*` (rd)   | in        | DFI read-return stream (MISS reads) from the rd CAM |
| `busy_o`          | out       | Any FIFO non-empty / slave busy                     |

## Notes

- There is **no** AXI ID side table, no `w_buf`/`b_fifo` in the SWAG sense, and no
  R-emit FSM. Per-ID metadata that must survive into the DRAM layer is carried in
  the CAM entries; everything else is dropped at the intake.
- Outstanding-count limits are structural: writes are bounded by the wr-data CAM
  depth (`NUM_ENTRIES`), reads by the rd-cmd CAM depth plus the order FIFO depth.
  There are no `MAX_PER_ID_*` parameters.
- The intakes are strict-FIFO and back-pressure cleanly: an intake stalls its AXI
  channel when the relevant FIFO or the downstream CAM is full.
