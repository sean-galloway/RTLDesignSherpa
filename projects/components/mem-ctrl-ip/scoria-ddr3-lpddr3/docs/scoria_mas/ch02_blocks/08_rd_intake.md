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

# Read Intake (`scoria_rd_intake`)

**Module:** `scoria_rd_intake.sv`
**Location:** `rtl/fub/`
**Category:** AXI4 host interface
**Parent:** `scoria_axi4_layer`
**Status:** complete and sim-verified

---

## Purpose

The read intake converts post-split AXI4 read requests into either a snarf hit against the write CAM or a miss command bound for the read command CAM. It owns the AR protocol skid buffer, address decode, the snarf probe handshake, the order FIFO that preserves AR order, and the source arbiter that merges snarf and DFI return data back onto the AXI R channel. It does not schedule; it only admits, tags, and reorders.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `AXI_ID_WIDTH` | int | 1+ | 8 | host AXI ID width |
| `AXI_ADDR_WIDTH` | int | 1+ | 32 | host address width |
| `AXI_DATA_WIDTH` | int | 1+ | 64 | host/DFI word width |
| `AXI_USER_WIDTH` | int | 1+ | 1 | AXI USER width |
| `NUM_RANKS` | int | 1+ | 1 | DRAM ranks |
| `NUM_BANKS` | int | 1+ | 8 | DRAM banks |
| `ROW_WIDTH` | int | 1+ | 14 | row address width |
| `COL_WIDTH` | int | 1+ | 10 | column address width |
| `BYTE_OFFSET_WIDTH` | int | 1+ | 3 | log2(device word bytes) |
| `AXI_BEATS_PER_BURST` | int | power of 2 | 4 | AXI beats per DRAM burst |
| `AR_FIFO_DEPTH` | int | 1+ | 4 | AR meta FIFO depth |
| `ORDER_FIFO_DEPTH` | int | 1+ | 8 | AR-order / source-tag FIFO depth |
| `RD_FIFO_DEPTH` | int | 1+ | 16 | read-data FIFO depth |
| `SKID_DEPTH_AR` | int | 1+ | 2 | AR skid buffer depth |
| `SKID_DEPTH_R` | int | 1+ | 4 | R channel skid buffer depth |

: Table 2.8.1: Read intake parameters

`scoria_axi4_layer` overrides `ORDER_FIFO_DEPTH` to `RD_RET_DEPTH + 8` so the FIFO can hold one slot for every in-flight read plus the snarf hits that never enter the return ring.

## Interface

### AXI4 read slave

| Signal | Direction | Width | Description |
|---|---|---|---|
| `aclk` | in | 1 | controller clock |
| `aresetn` | in | 1 | active-low reset |
| `s_axi_arid` | in | `AXI_ID_WIDTH` | AR ID |
| `s_axi_araddr` | in | `AXI_ADDR_WIDTH` | AR address |
| `s_axi_arlen` | in | 8 | AR burst length |
| `s_axi_arvalid` | in | 1 | AR valid |
| `s_axi_arready` | out | 1 | AR ready |
| `ar_agg_i` | in | 1 | high when the host burst split into >1 sub-command |
| `ar_last_i` | in | 1 | high on the final sub-command |
| `s_axi_rid` | out | `AXI_ID_WIDTH` | R ID |
| `s_axi_rdata` | out | `AXI_DATA_WIDTH` | R data |
| `s_axi_rresp` | out | 2 | R response |
| `s_axi_rlast` | out | 1 | R last |
| `s_axi_rvalid` | out | 1 | R valid |
| `s_axi_rready` | in | 1 | R ready |
| `bank_lsb_i` | in | 5 | address-map bank LSB |
| `hash_en_i` | in | 1 | address-hash enable |
| `hash_seed_i` | in | 8 | address-hash seed |

: Table 2.8.2: AXI4 read slave interface

### Read command miss path

| Signal | Direction | Width | Description |
|---|---|---|---|
| `ar_push_valid_o` | out | 1 | miss command valid to read CAM |
| `ar_push_ready_i` | in | 1 | read CAM ready |
| `ar_push_rank_o` | out | `$clog2(NUM_RANKS)` or 1 | decoded rank |
| `ar_push_bank_o` | out | `$clog2(NUM_BANKS)` | decoded bank |
| `ar_push_row_o` | out | `ROW_WIDTH` | decoded row |
| `ar_push_col_o` | out | `COL_WIDTH` | decoded column |
| `ar_push_id_o` | out | `AXI_ID_WIDTH` | AXI ID |
| `ar_push_qos_o` | out | 4 | AxQOS to CAM |

: Table 2.8.3: Read command miss path

### Snarf probe to write CAM

| Signal | Direction | Width | Description |
|---|---|---|---|
| `snarf_probe_valid_o` | out | 1 | probe valid |
| `snarf_probe_rank_o` | out | rank width | probe rank |
| `snarf_probe_bank_o` | out | bank width | probe bank |
| `snarf_probe_row_o` | out | `ROW_WIDTH` | probe row |
| `snarf_probe_col_o` | out | `COL_WIDTH` | probe column |
| `snarf_probe_id_o` | out | `AXI_ID_WIDTH` | read AXI ID |
| `snarf_probe_len_o` | out | 8 | read `AxLEN` |
| `snarf_hit_i` | in | 1 | registered hit from write CAM |
| `snarf_accept_o` | out | 1 | AR admitted as snarf |

: Table 2.8.4: Snarf probe interface

### Snarf data stream

| Signal | Direction | Width | Description |
|---|---|---|---|
| `snarf_rd_valid_i` | in | 1 | snarf data valid from write CAM |
| `snarf_rd_ready_o` | out | 1 | snarf data ready |
| `snarf_rd_data_i` | in | `AXI_DATA_WIDTH` | snarf data |
| `snarf_rd_last_i` | in | 1 | snarf last beat |

: Table 2.8.5: Snarf data stream

### DFI read-return stream

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_rd_valid_i` | in | 1 | DFI return data valid |
| `dfi_rd_ready_o` | out | 1 | DFI return data ready |
| `dfi_rd_data_i` | in | `AXI_DATA_WIDTH` | DFI return data |
| `dfi_rd_last_i` | in | 1 | DFI return last beat |
| `dfi_rd_resp_i` | in | 2 | DFI return response |
| `busy_o` | out | 1 | OR of internal busy flags |

: Table 2.8.6: DFI read-return stream

## Microarchitecture internals

### Two-stage AR admit pipeline

The snarf probe inside the write CAM is registered, so a probe presented on cycle `c` only produces its hit on cycle `c+1`. The AR being admitted must therefore sit one cycle behind the AR being probed. The old implementation used a single `r_armed` bit on the skid head: probe the head, wait one cycle, admit it. Because the arm cleared on admit and could not re-arm until the next cycle, admits were capped at one every two cycles. One admitted sub-command equals one DRAM burst, so the gate halved read bandwidth on geometries where one burst is one AXI beat — the x16 BL4 case measured on the board (pumice BUG-011).

The fix stages the AR:

```text
skid head  -> probed this cycle
stage reg  -> admitted this cycle
```

The skid head advances whenever the stage frees, so a sub-command is admitted every cycle while the downstream path is ready. While the stage is held because downstream is not ready, the probe is re-pointed at the stage itself rather than the head, so the hit is refreshed every cycle. The admit decision is never more than one cycle old, matching the exposure of the original arm bit but without the throughput penalty.

### Snarf probe handshake

The probe is combinational out of `scoria_rd_intake` but registered inside `scoria_wr_data_cam`. The hit `snarf_hit_i` belongs to whatever was probed last cycle, which by construction is the AR now in the admit stage. A hit forces the snarf path: the write CAM holds the youngest matching same-ID entry that is fully written, and the read streams from the CAM's SRAM instead of DRAM. Snarf is same-ID only; cross-ID reads are sent to DRAM even if the data is present, because the CAM key does not include ID and allowing cross-ID snarf would forward data belonging to a different transaction.

### Order FIFO

Every admitted read pushes one tag into the order FIFO in AR order. The tag is `{agg, last, source, len, id}`:

- `agg` and `last` come from the aggregation sideband and are used to collapse per-sub `RLAST`.
- `source` is `SRC_DFI` (0) for a miss or `SRC_SNARF` (1) for a hit.
- `len` is the sub-command's `AxLEN`.
- `id` is the AXI ID.

The order FIFO is popped when the last beat of the current sub-command is consumed from whichever source the head selects.

### Beat dropping and RLAST generation

A DRAM burst always returns `AXI_BEATS_PER_BURST` beats, but the host may have asked for fewer. Beats past the requested `AxLEN` are consumed from the source and dropped rather than returned to the host. Without this, a single-beat read would receive the full DRAM burst and the R channel would never frame correctly.

`RLAST` is asserted on the last requested beat, not on the last returned DRAM beat. For a split host burst (`agg=1`), the host only sees `RLAST` on the last requested beat of the final sub-command (`last=1`); non-split reads pass `RLAST` per sub-command unchanged.

### Source arbiter and read-data FIFO

The source arbiter selects between the snarf stream and the DFI return stream based on the order-FIFO head's `source` bit. The selected beat is pushed into the read-data FIFO as `{resp, last, id, data}`. The FIFO decouples the source-side handshake from the final AXI R channel, which is driven from the FIFO head.

## FSM policy

There is no state machine. Control is distributed across the skid buffer, the one-cycle admit stage, the order FIFO, and the source arbiter. The only counter is the per-sub forward counter `r_fwd`, which counts beats forwarded so far and resets on every DRAM burst boundary.

## Timing

AR admission is one cycle from skid head to `ar_push_valid_o` or `snarf_accept_o`. The snarf hit is available one cycle after the probe, matching the write CAM's registered lookup. DFI return data is returned to the host in AR order with one read-data FIFO cycle of elasticity.

The critical throughput path is the AR admit stage: in steady state the stage admits and reloads in the same cycle, so the rate is one sub-command per cycle.

## Notes

- **BUG-011 fix:** the two-stage pipeline replaced the one-cycle arm bit. The old design halved x16 BL4 read bandwidth because one sub-command is one AXI beat there; the board measurement was 291.7 MB/s for reads versus 570 MB/s for writes, consistent with a one-every-two-cycles gate.
- **Probe freshness:** latching the hit would be cheaper but wrong. A latched hit goes stale against writes entering the write CAM behind the probe, which is exactly the RAW-forwarding case the snarf path exists to catch.
- **Same-ID snarf only:** the probe includes the read ID, and the write CAM match requires ID equality. Cross-ID reads always take the DRAM path.
- **Address alignment:** the AR address is aligned down to the AXI beat before address mapping. This prevents double-counting byte offsets when a wide AXI beat spans multiple device words; the byte lanes are already carried by the AXI strobes on the write side.
