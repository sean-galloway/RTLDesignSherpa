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

# AXI4 Intake (`axi_intake`)

**Module:** `axi_intake.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `axi_frontend_macro`
**Status:** v1 implemented (outputs strict-flop registered)

> **Renamed:** the SWAG called this `axi4_slave_fub`; the implementation
> name is `axi_intake`. It owns the AXI4 protocol engine, the `w_buf` for
> write data staging, the `b_fifo` for ID-aware B-channel ordering, and the
> R-emit FSM that returns read beats (from `rd_inject` and the
> `wr2rd_forward` snarf path).

---

## Purpose

`axi4_slave_fub` is the AXI4 host-facing protocol engine. It accepts AW/W/AR transactions from the SoC, hands off the address to `addr_mapper` for decode, and pushes the resulting transaction into the appropriate CAM (`wr_cmd_cam` or `rd_cmd_cam`). On B and R returns, it pulls completion signals from the CAMs and merges them with AXI-side metadata to produce protocol-compliant responses.

The FUB owns the AXI ID side table — the per-ID set of fields (`awcache`, `awprot`, `awqos`, `awregion`, `bid` echo, `rid` echo) that never need to cross into the DRAM-layer state.

## External Interface (AXI side)

Per HAS §2.4 §1 — full AW/W/B/AR/R channel signal list. No additions in MAS.

## Internal Buffers

| Buffer            | Depth                           | Width                                                                | Purpose                                          |
|-------------------|---------------------------------|----------------------------------------------------------------------|--------------------------------------------------|
| `aw_buf`          | `TXN_QUEUE_DEPTH/2` (default 8) | `AW + IDW + 8(len) + 3(size) + 2(burst) + 4(cache) + 3(prot) + 4(qos) + 4(region)` | Pending AW until CAM push |
| `w_buf`           | `TXN_QUEUE_DEPTH × max(burst_len)` | `DW + SW + 1(last)` per beat                                       | Write data staging                               |
| `ar_buf`          | `TXN_QUEUE_DEPTH/2` (default 8) | same AW fields                                                       | Pending AR until CAM push                        |
| `b_response_fifo` | small (4)                       | `IDW + 2(resp)`                                                      | Pending B responses                              |
| `r_response_fifo` | small (4)                       | `IDW + DW + 2(resp) + 1(last)` per beat                              | Pending R responses                              |
| `id_side_table`   | `2^IDW`                         | `4(cache) + 3(prot) + 4(qos) + 4(region)`                            | Per-ID AXI metadata, indexed by `awid`/`arid`    |

The buffers above are FUB-internal; they do **not** appear in the architecture-level transaction queue (`txn_queue_fub`). The transaction queue holds the DRAM-layer view of pending work; these buffers hold the AXI-layer view of in-flight bursts.

## Data Flow

### Write Path

1. AW intake: capture `aw*` fields; push to `aw_buf`. Compute outstanding-count and assert `awready` if `aw_buf` not full.
2. W intake: accept `w*` beats into `w_buf`. Each W beat carries `wstrb` and `wlast`. The W path does not wait for AW — W can lead AW or trail it within AXI ordering rules.
3. CAM push: when both `aw_buf` head and the matching `w_buf` head are present (or when a write-only / address-only burst's prerequisites are satisfied), push to `wr_cmd_cam` with:
   - `key = awid`
   - `data = (rank, bank, row, col, burst_len, w_buf_ptr, strb_ptr)`
   - where (rank, bank, row, col) come from `addr_mapper` (combinational, same cycle)
4. Scheduler issue: when scheduler picks this entry, the FUB hands `w_data_path_fub` the `w_buf_ptr` and `strb_ptr` for it to walk the data beats.
5. B response: when `wr_cmd_cam` reports the entry complete (last W beat issued + tDFI write to DFI), the FUB pops the AXI ID, joins with `id_side_table[id].axi_metadata`, and pushes `b_response_fifo`.
6. B emit: standard B-channel handshake; pop `b_response_fifo`.

### Read Path

1. AR intake: capture `ar*` fields; push to `ar_buf`. Assert `arready` if not full.
2. CAM push: pop `ar_buf` head; push to `rd_cmd_cam` with:
   - `key = arid`
   - `data = (rank, bank, row, col, burst_len, rid_counter, expected_beats)`
   - where (rank, bank, row, col) come from `addr_mapper`
   - `rid_counter` is the AXI ID echo
3. Scheduler issue: when scheduler picks this entry, it commands the issue of RD / RDA. `rd_data_path_fub` watches for the corresponding DFI rddata beats.
4. R response: as each R beat completes, `rd_data_path_fub` strobes `rd_cmd_cam` to decrement `expected_beats`; the CAM emits `r_beat_to_axi` with `rid`, beat data, `rlast` when the last beat arrives.
5. R emit: standard R-channel handshake; pop `r_response_fifo`.

## Outstanding Burst Tracking

The FUB enforces:

| Limit                     | Constraint                                            |
|---------------------------|-------------------------------------------------------|
| Total in-flight reads     | ≤ `rd_cmd_cam` depth (default 16)                 |
| Total in-flight writes    | ≤ `wr_cmd_cam` depth (default 16)                 |
| Per-ID in-flight reads    | ≤ `MAX_PER_ID_READS` parameter (default 4)            |
| Per-ID in-flight writes   | ≤ `MAX_PER_ID_WRITES` parameter (default 4)           |

If `AXI_OOO_ACROSS_IDS == false`, the per-ID counts reduce to "one in-flight per ID" — the AXI completion is strictly in-order per ID, but the issue order at the scheduler is still OoO.

## Timing Budget

| Path                                       | Budget               |
|--------------------------------------------|----------------------|
| `awvalid` → `awready` (combinational)      | ≤ 0.7 of cycle      |
| `aw_buf` push to `addr_mapper` valid       | 0 cycles (combinational) |
| `addr_mapper` valid to CAM push            | 1 cycle              |
| `wr_cmd_cam` push to scheduler-visible     | 1 cycle              |
| Worst path: `awvalid` → CAM-push register | 2 cycles             |

The two-cycle AXI→CAM latency is the limit on AXI sustained issue rate; with default config it allows 1 burst per 2 cycles, well within the AXI burst rate at 200 MHz.

## CSR Hooks

- `STATUS.axi_inflight_rd` (R only) — current count of in-flight read bursts
- `STATUS.axi_inflight_wr` (R only) — current count of in-flight write bursts
- `STATUS.axi_id_table_occ` (R only) — number of distinct AXI IDs currently in the side table
- `OBS_AXI_R_LATENCY_AVG`, `OBS_AXI_W_LATENCY_AVG` — driven from R/B-channel sampling in this FUB

## TODO (week-of-MAS work)

- FSM diagram for the AW/W join and the AR intake (mermaid)
- B/R response-ordering corner cases (per HAS §3.1 OoO-across-IDs)
- Waveform examples (wavedrom) for back-pressure scenarios
- Detailed table of `id_side_table` field widths and reset values
