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

# `mc_axi4_layer` — AXI4 host interface and read-return ring

**Module:** `macro/mc_axi4_layer.sv`
**Child FUBs:** `fub/mc_wr_splitter.sv`, `fub/mc_axi_burst_chopper.sv`, `fub/mc_wr_intake.sv`, `fub/mc_rd_intake.sv`, `fub/mc_rd_return_ring.sv`

`mc_axi4_layer` is the host-facing AXI4 slave boundary of the common memory-controller stack. It transforms host AXI4 read and write bursts into DFI-burst-sized descriptors that cross into `mc_storage_layer`, sources read-your-write snarf data from the write-data CAM, and presents the final AXI4 read-data and write-response channels to the host (`macro/mc_axi4_layer.sv:8-12`). It is the N=1 provider of the descriptor seam in lite builds (see [`common_has` chapter 2](../../common_has/common_has_index.md)).

## Child-instance map
| Instance | Module | Parameter bindings in this layer | Role |
|----------|--------|----------------------------------|------|
| `u_wr_split` | `mc_wr_splitter` | `AXI_ID_WIDTH=IW`, `AXI_ADDR_WIDTH=AW`, `AXI_DATA_WIDTH=DW`, `AXI_USER_WIDTH=UW`, `AXI_BEATS_PER_BURST=AXI_BEATS_PER_BURST` | Split host AW/W into DFI-burst sub-bursts and reframe WLAST (`macro/mc_axi4_layer.sv:207-256`) |
| `u_rd_split` | `mc_axi_burst_chopper` | `AXI_ID_WIDTH=IW`, `AXI_ADDR_WIDTH=AW`, `AXI_USER_WIDTH=UW`, `STRB_BYTES=SW`, `AXI_BEATS_PER_BURST=AXI_BEATS_PER_BURST` | Split host AR into DFI-burst sub-commands (`macro/mc_axi4_layer.sv:259-296`) |
| `u_wr_intake` | `mc_wr_intake` | full address-map set plus `AXI_BEATS_PER_BURST` | Write descriptor push + write-data pop + commit-driven B (`macro/mc_axi4_layer.sv:304-370`) |
| `u_rd_intake` | `mc_rd_intake` | as `u_wr_intake`, plus `ORDER_FIFO_DEPTH=RD_RET_DEPTH+8` | Read descriptor push + snarf probe + R return (`macro/mc_axi4_layer.sv:373-445`) |
| `u_rd_ring` | `mc_rd_return_ring` | `DEPTH=RD_RET_DEPTH`, `AXI_DATA_WIDTH=DW`, `AXI_BEATS_PER_BURST=AXI_BEATS_PER_BURST` | In-flight read return buffer (`macro/mc_axi4_layer.sv:450-475`) |

## Burst chop, split, and final coalescing
`mc_axi_burst_chopper` is an FSM-free AR/AW burst chopper with one active bit, a remaining-beats counter, and a running address. Each sub-command spans at most `AXI_BEATS_PER_BURST` AXI beats; addresses step by `AXI_BURST_BYTES` so each sub-command lands on a DRAM-burst boundary (`fub/mc_axi_burst_chopper.sv:8-14`, `fub/mc_axi_burst_chopper.sv:44-64`). A ragged final chunk takes `min(remaining, AXI_BEATS_PER_BURST)` beats (`fub/mc_axi_burst_chopper.sv:27-29`).

`mc_wr_splitter` wraps the same chopper for AW with `PAD_TO_CHUNK=1` and reframes the W stream so every sub-command sees exactly one WLAST at its `AXI_BEATS_PER_BURST` boundary (`fub/mc_wr_splitter.sv:8-12`). The WLAST re-frame is driven by a W-beat down-counter, not by the AW FSM, so it stays exact for any `AXI_BEATS_PER_BURST` including 1 (`fub/mc_wr_splitter.sv:15-22`). Short write bursts are completed with zero-strobe filler beats; `strb=0` becomes `DM=1` in the DFI write serializer (`fub/mc_wr_splitter.sv:134-139`).

Both splitters emit an aggregation sideband: `m_ax_agg` is high when the host command splits into more than one sub-command, and `m_ax_last` is high on the final sub-command (`fub/mc_axi_burst_chopper.sv:31-37`). The intakes push these bits through their FIFOs so the return path can collapse per-sub B/RLAST into a single host response without a separate aggregator (`macro/mc_axi4_layer.sv:200-204`). For reads, the intake forwards only the beats the host requested and drops excess DRAM-burst beats; `RLAST` is generated on the last requested beat, and for a split burst it is asserted only when `w_head_last` is also set (`fub/mc_rd_intake.sv:380-384`, `fub/mc_rd_intake.sv:465-473`).

## Read return ring: ordering contract
`mc_rd_return_ring` separates the in-flight read count from the read-command CAM depth. The CAM entry lives from insert to issue only; after issue, a ticket follows the read through DRAM (`fub/mc_rd_return_ring.sv:8-12`). The ordering rules are:

1. **Allocation order equals AR order.** A ticket is allocated at the ring tail when `alloc_valid_i` is asserted with the CAM insert (`fub/mc_rd_return_ring.sv:53-55`, `fub/mc_rd_return_ring.sv:97-100`).
2. **DFI returns are accepted in issue order**, mapped by an internal ticket FIFO (`fub/mc_rd_return_ring.sv:60-63`, `fub/mc_rd_return_ring.sv:106-120`).
3. **Drain order equals ring/AR order.** The ring drains from its head once the head slot's data is complete; because allocation order is AR order, per-ID AXI reads return in request order structurally (`fub/mc_rd_return_ring.sv:74-80`, `fub/mc_rd_return_ring.sv:135-143`).
4. **A slot is freed only when its last beat is consumed** by the drain (`fub/mc_rd_return_ring.sv:185-186`).

The ring is sized by `RD_RET_DEPTH` (default 32). This decoupling fixed a bandwidth ceiling: with the CAM holding reads for the full DRAM round trip, eight entries over a ~27-cycle round trip bounded board reads to about 180 MB/s; the ring fix took board reads to ~572 MB/s (`research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/ch02_blocks/22_rd_return_ring.md:32-42`, inherited from the pumice measured history).

## Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `AXI_ID_WIDTH` | 8 | Host AXI ID width |
| `AXI_ADDR_WIDTH` | 32 | Host AXI address width |
| `AXI_DATA_WIDTH` | 64 | Host AXI data width (and DFI word width in this layer) |
| `AXI_USER_WIDTH` | 1 | Host AXI user width |
| `DRAM_BEAT_WIDTH` | 64 | Retained only to size `DRAM_BURST_BYTES`; pumice instantiates this with the AXI data width, not the DRAM beat width (`macro/mc_axi4_layer.sv:29-34`) |
| `NUM_RANKS` | 1 | Rank count passed to the address mapper |
| `NUM_BANKS` | 8 | Bank count passed to the address mapper |
| `ROW_WIDTH` | 14 | Row address width passed to the address mapper |
| `COL_WIDTH` | 10 | Column address width passed to the address mapper |
| `BYTE_OFFSET_WIDTH` | 3 | Byte-offset width passed to the address mapper |
| `BG_WIDTH` | 1 | Bank-group width; `HAS_BG=0` keeps generations 2/3 bit-identical (`macro/mc_axi4_layer.sv:41-44`) |
| `HAS_BG` | 0 | Bank-group enable; andesite passes 1/2 (`macro/mc_axi4_layer.sv:41-44`) |
| `AXI_BEATS_PER_BURST` | 4 | AXI beats per DFI burst; this is what pumice passes as `BURST_WORDS`, not the JEDEC burst length (`macro/mc_axi4_layer.sv:45-51`) |
| `NUM_ENTRIES` | 8 | Storage/scheduler entry count passed from core |
| `N_SRAM_SLOTS` | `NUM_ENTRIES` | SRAM slot count |
| `N_SCHED_LU` | 4 | Scheduler lookup port count |
| `AGE_WIDTH` | 16 | Age field width |
| `RD_RET_DEPTH` | 32 | In-flight read count (ring depth) |
| `IW`, `AW`, `DW`, `UW`, `SW`, `BKW`, `PTRW`, `RKW`, `DRAM_BURST_BYTES` | derived | Shorthand widths; `DRAM_BURST_BYTES = AXI_BEATS_PER_BURST * (DRAM_BEAT_WIDTH / 8)` |

## Ports
### Clock, reset, address map, and status
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `aclk` | input | 1 | Layer clock |
| `aresetn` | input | 1 | Active-low reset |
| `bank_lsb_i` | input | 5 | Address-map bank LSB selector |
| `hash_en_i` | input | 1 | Bank hash enable |
| `hash_seed_i` | input | 8 | Bank hash seed |
| `busy_o` | output | 1 | OR of write-intake, read-intake, and return-ring busy flags (`macro/mc_axi4_layer.sv:477`) |

### Host AXI4 slave
| Channel | Port | Direction | Width | Description |
|---------|------|-----------|-------|-------------|
| AW | `s_axi_awid` | input | `IW` | Write address ID |
| AW | `s_axi_awaddr` | input | `AW` | Write address |
| AW | `s_axi_awlen` | input | 8 | Burst length |
| AW | `s_axi_awsize` | input | 3 | Burst size |
| AW | `s_axi_awburst` | input | 2 | Burst type |
| AW | `s_axi_awlock` | input | 1 | Lock signal |
| AW | `s_axi_awcache` | input | 4 | Cache signal |
| AW | `s_axi_awprot` | input | 3 | Protection signal |
| AW | `s_axi_awqos` | input | 4 | QoS signal |
| AW | `s_axi_awregion` | input | 4 | Region signal |
| AW | `s_axi_awuser` | input | `UW` | User sideband |
| AW | `s_axi_awvalid` | input | 1 | Write address valid |
| AW | `s_axi_awready` | output | 1 | Write address ready |
| W | `s_axi_wdata` | input | `DW` | Write data |
| W | `s_axi_wstrb` | input | `SW` | Write strobe |
| W | `s_axi_wlast` | input | 1 | Write data last |
| W | `s_axi_wuser` | input | `UW` | Write data user |
| W | `s_axi_wvalid` | input | 1 | Write data valid |
| W | `s_axi_wready` | output | 1 | Write data ready |
| B | `s_axi_bid` | output | `IW` | Write response ID |
| B | `s_axi_bresp` | output | 2 | Write response |
| B | `s_axi_buser` | output | `UW` | Write response user |
| B | `s_axi_bvalid` | output | 1 | Write response valid |
| B | `s_axi_bready` | input | 1 | Write response ready |
| AR | `s_axi_arid` | input | `IW` | Read address ID |
| AR | `s_axi_araddr` | input | `AW` | Read address |
| AR | `s_axi_arlen` | input | 8 | Burst length |
| AR | `s_axi_arsize` | input | 3 | Burst size |
| AR | `s_axi_arburst` | input | 2 | Burst type |
| AR | `s_axi_arlock` | input | 1 | Lock signal |
| AR | `s_axi_arcache` | input | 4 | Cache signal |
| AR | `s_axi_arprot` | input | 3 | Protection signal |
| AR | `s_axi_arqos` | input | 4 | QoS signal |
| AR | `s_axi_arregion` | input | 4 | Region signal |
| AR | `s_axi_aruser` | input | `UW` | User sideband |
| AR | `s_axi_arvalid` | input | 1 | Read address valid |
| AR | `s_axi_arready` | output | 1 | Read address ready |
| R | `s_axi_rid` | output | `IW` | Read data ID |
| R | `s_axi_rdata` | output | `DW` | Read data |
| R | `s_axi_rresp` | output | 2 | Read response |
| R | `s_axi_rlast` | output | 1 | Read data last |
| R | `s_axi_ruser` | output | `UW` | Read data user |
| R | `s_axi_rvalid` | output | 1 | Read data valid |
| R | `s_axi_rready` | input | 1 | Read data ready |

### Downstream interfaces
| Group | Port | Direction | Width | Description |
|-------|------|-----------|-------|-------------|
| WR push | `aw_push_valid_o` | output | 1 | Write command valid |
| WR push | `aw_push_ready_i` | input | 1 | Write command ready |
| WR push | `aw_push_bank_o` | output | `BKW` | Decoded bank |
| WR push | `aw_push_row_o` | output | `ROW_WIDTH` | Decoded row |
| WR push | `aw_push_col_o` | output | `COL_WIDTH` | Decoded column |
| WR push | `aw_push_id_o` | output | `IW` | Write AXI ID |
| WR push | `aw_push_qos_o` | output | 4 | Write QoS |
| WR push | `aw_push_agg_o` | output | 1 | Part of a split host burst |
| WR push | `aw_push_last_o` | output | 1 | Final sub-command of host burst |
| WR data | `wd_valid_o` | output | 1 | Write data valid |
| WR data | `wd_ready_i` | input | 1 | Write data ready |
| WR data | `wd_data_o` | output | `DW` | Write data |
| WR data | `wd_strb_o` | output | `SW` | Write strobe |
| WR data | `wd_last_o` | output | 1 | Write data last |
| WR done | `wr_done_valid_i` | input | 1 | Write commit completion |
| WR done | `wr_done_id_i` | input | `IW` | Completion ID |
| Snarf probe | `snarf_probe_valid_o` | output | 1 | Probe valid |
| Snarf probe | `snarf_probe_bank_o` | output | `BKW` | Probe bank |
| Snarf probe | `snarf_probe_row_o` | output | `ROW_WIDTH` | Probe row |
| Snarf probe | `snarf_probe_col_o` | output | `COL_WIDTH` | Probe column |
| Snarf probe | `snarf_probe_id_o` | output | `IW` | Read AXI ID |
| Snarf probe | `snarf_probe_len_o` | output | 8 | Read AXI length |
| Snarf hit | `snarf_hit_i` | input | 1 | Probe hit (combinational, one cycle delayed by the CAM register) |
| Snarf hit | `snarf_accept_o` | output | 1 | AR admitted as a snarf hit |
| Snarf data | `snarf_rd_valid_i` | input | 1 | Snarf data valid |
| Snarf data | `snarf_rd_ready_o` | output | 1 | Snarf data ready |
| Snarf data | `snarf_rd_data_i` | input | `DW` | Snarf data |
| Snarf data | `snarf_rd_last_i` | input | 1 | Snarf data last |
| RD push | `ar_push_valid_o` | output | 1 | Read command valid |
| RD push | `ar_push_ready_i` | input | 1 | Read command ready |
| RD push | `ar_push_bank_o` | output | `BKW` | Decoded bank |
| RD push | `ar_push_row_o` | output | `ROW_WIDTH` | Decoded row |
| RD push | `ar_push_col_o` | output | `COL_WIDTH` | Decoded column |
| RD push | `ar_push_id_o` | output | `IW` | Read AXI ID |
| RD push | `ar_push_qos_o` | output | 4 | Read QoS |
| Ring alloc | `rt_alloc_ready_o` | output | 1 | Ring has space to allocate a ticket |
| Ring alloc | `rt_alloc_ticket_o` | output | `$clog2(RD_RET_DEPTH)` | Allocated ticket (ring tail) |
| Ring issue | `rd_iss_ready_o` | output | 1 | Ring ready for issue notify |
| Ring issue | `rd_iss_valid_i` | input | 1 | Issue notify valid |
| Ring issue | `rd_iss_ticket_i` | input | `$clog2(RD_RET_DEPTH)` | Ticket that issued |
| Ring gate | `rd_cam_ins_ready_i` | input | 1 | Combined gate for ring allocation with `ar_push_valid_o` (`macro/mc_axi4_layer.sv:457`) |
| DFI return | `rd_dfi_ret_valid_i` | input | 1 | DFI return data valid |
| DFI return | `rd_dfi_ret_ready_o` | output | 1 | DFI return data ready |
| DFI return | `rd_dfi_ret_data_i` | input | `DW` | DFI return data |
| DFI return | `rd_dfi_ret_resp_i` | input | 2 | DFI return response |
| DFI return | `rd_dfi_ret_last_i` | input | 1 | DFI return last beat |

## What this layer does not know
- **DRAM timing.** No tRAS, tRCD, CAS latency, refresh, or power-state logic resides here.
- **Scheduling.** The layer produces descriptor pushes and accepts scheduler handshakes through the storage layer; it does not pick oldest entries or arbitrate banks.
- **DFI protocol generation.** All DFI command, data, and timing formatting is delegated to the DFI layers.
- **Write-data CAM internals.** The CAM fill, commit, and snarf datapaths are in `mc_storage_layer`; this layer exposes only the raw push, snarf probe, and completion ports.

## Open questions
- Whether `NUM_ENTRIES`, `N_SRAM_SLOTS`, `N_SCHED_LU`, and `AGE_WIDTH` are still consumed by `mc_axi4_layer` itself or are pass-through remnants from an earlier integration; they appear only in the parameter list and do not drive any local logic in the reviewed RTL (`macro/mc_axi4_layer.sv:52-55`).
- Whether `bank_lsb_i` is allowed to place the bank boundary inside the AXI beat; the intakes mask the beat-offset bits before address mapping, but the resulting column alignment behavior for data-width converters wider than the device word is not verified here.
