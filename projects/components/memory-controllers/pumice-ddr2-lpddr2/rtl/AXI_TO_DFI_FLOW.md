# AXI-to-DFI flow

End-to-end path from the host AXI4 bus to the DFI v2.1 PHY interface.
Each section lists what the FUB does + which queues / SRAMs / per-slot
arrays it owns. Read top-to-bottom for the write path then the read
path; the scheduler / timer FUBs sit in the middle and arbitrate.

```
HOST AXI4
   │
   ▼
[axi_frontend_macro]   axi_intake → addr_mapper → wr2rd_forward
                         → wr_cmd_cam / rd_cmd_cam + axi_id_side_table
   │
   ▼
[command_scheduler_macro]  scheduler → xbank_timers / global_timers
                            + refresh_ctrl + powerdown_ctrl
                            + mode_register + init_sequencer
                            + page_predictor
   │
   ▼
[data_path_macro]      wr_beat_sequencer (W)  ||  rd_cl_aligner (R)
   │
   ▼
[dfi_v21_interface_macro]  dfi_cmd_formatter → dfi_signal_pack
   │
   ▼
DFI v2.1 → PHY → DRAM
```

---

## 1. `axi_intake`  (axi_frontend_macro)

What it does
- Front door for s_axi_aw / w / b / ar / r.
- AW + W decoupled: AW path holds metadata; W path streams beats into wbuf.
- Generates B responses out of a per-id FIFO.
- AR fans to wr2rd_forward (snarf) or to rd_cmd_cam (DRAM-fetch path).
- Replays R beats either from wbuf (forwarded) or rd_inject (DRAM-served).

Queues / arrays it owns
- `r_w_buf [W_BUF_DEPTH]` — beat data buffer (128 deep × DRAM beat width).
- `r_strb_buf[W_BUF_DEPTH]` — per-beat byte strobes.
- `r_aw_pending` skid + FIFO (AW_PENDING_DEPTH = 4).
- `r_ar_pending` skid + FIFO (AR_PENDING_DEPTH = 4).
- `r_b_fifo` (B_FIFO_DEPTH = 4) — pending B responses per host id.
- AXI4 skid buffers per channel (SKID_DEPTH_AW/W/B/AR/R).
- `r_wbuf_outstanding` counter — AW-side flow control; gates awready
  when wbuf would overflow.

## 2. `addr_mapper`  (axi_frontend_macro)

What it does
- Translates AXI byte address to (rank, bank, row, col).
- Three schemes selected by `scheme_active_i`: ROW_MAJOR / BANK_INTERLEAVE
  / XOR_HASH.

Queues / arrays
- None (pure combinational).

## 3. `wr2rd_forward`  (axi_frontend_macro)

What it does
- For every incoming AR, comparator-array against every wr_cmd_cam slot.
- On (rank, bank, row, col, len, full_strb) match, intercepts the AR:
  drops the rd_cmd_cam push and emits a forwarded burst pointer into
  axi_intake's wbuf — the read is served from wbuf without ever
  touching DRAM.

Queues / arrays
- None — purely combinational against wr_cmd_cam snapshots.

## 4. `wr_cmd_cam`  (axi_frontend_macro)

What it does
- One slot per in-flight write burst (depth = WR_CAM_DEPTH = 16).
- Stores decoded tuple + wbuf pointer + strb pointer per burst.
- Tracks `r_issued` (scheduler picked it) and `r_b_pending` (waiting on
  B retirement).
- Exposes match vectors so scheduler can pick row-hit-first.

Queues / arrays
- Per-slot regs: `r_valid`, `r_id`, `r_rank`, `r_bank`, `r_row`,
  `r_col`, `r_len`, `r_w_buf_ptr`, `r_strb_ptr`, `r_issued`,
  `r_b_pending`, `r_qos`.
- `r_full_strb` bitmap — does this burst cover every beat with full
  byte strobes (needed by wr2rd_forward).

## 5. `rd_cmd_cam`  (axi_frontend_macro)

What it does
- One slot per in-flight read burst (depth = RD_CAM_DEPTH = 16).
- Allocates lowest-free slot on push.
- Per-slot age tag (push-order counter) so scheduler can pick OLDEST
  same-id read first — required for AXI4 in-order R semantics across
  slot reuse.
- Counts beats returned per slot; entry_complete fires on last beat.

Queues / arrays
- Per-slot regs: `r_valid`, `r_id`, `r_rank`, `r_bank`, `r_row`,
  `r_col`, `r_len`, `r_beats_returned`, `r_issued`, `r_qos`, `r_age`.
- `r_push_counter` — monotonic age tag generator.

## 6. `axi_id_side_table`  (axi_frontend_macro)

What it does
- Holds AXI id / awuser metadata per cam slot so the controller can
  reproduce id, awqos, awuser on the B and R responses without keeping
  them in the cam itself.

Queues / arrays
- Per-slot wr / rd metadata regs (16 each).

---

## 7. `scheduler`  (command_scheduler_macro)

What it does
- One slot picker per direction (wr_match_pending, rd_match_pending).
- Pick rule: highest QoS wins; tie-break by AGE (oldest first) — the
  age tie-break is the AXI4-correctness fix that prevents a freed +
  reused slot from jumping past older same-id ops.
- Direction arbiter: starvation-bounded age counters per direction,
  fairness toggle on age tie.
- Page-policy state machine (OPEN / CLOSE / HAPPY_HYBRID): decides
  ACT / PRE / READ / WRITE / RDA / WRA per pick.

Queues / arrays
- `r_w_age`, `r_r_age` (8-bit saturating) — direction starvation.
- `r_arb_prefer_rd` — fairness toggle.
- `r_pending_*` — currently-being-issued slot context.

## 8. `xbank_timers`  (command_scheduler_macro)

What it does
- Per-(rank, bank) micro-timers: tRCD, tRP, tRAS, tRC, tWR, tWTR, tRTP.
- Decides per-bank readiness for ACT / PRE / RD / WR.

Queues / arrays
- One counter array per timing, indexed by (rank, bank).
- `bank_row_active`, `bank_open_row`, `bank_act_ready` per
  (rank, bank).

## 9. `global_timers`  (command_scheduler_macro)

What it does
- Rank-level windows: tFAW (4-activate window), tRRD, refresh interval.
- Drives `tfaw_window_ok_i` consumed by the scheduler.

Queues / arrays
- Per-rank tFAW shift register of last-4-activate timestamps.
- Per-rank tRRD counter.

## 10. `refresh_ctrl`  (command_scheduler_macro)

What it does
- Tracks tREFI deadline. Asserts `refresh_req` when overdue.
- Postpone-by-N policy bounded by JEDEC.

Queues / arrays
- Refresh-due counter + deferral window.

## 11. `powerdown_ctrl`  (command_scheduler_macro)

What it does
- Idle-detection + power-down state machine.
- Issues `dfi_dram_clk_disable` and `dfi_cke` controls.

## 12. `mode_register`  (command_scheduler_macro)

What it does
- Holds MR0..MR3 live values (CL, CWL, BL, AL) for the data path.
- Handles MR-write commands from init_sequencer + CSR.

Queues / arrays
- 4 × 16-bit MR registers.

## 13. `init_sequencer`  (command_scheduler_macro)

What it does
- DDR2 / LPDDR2 init walk: PRE-ALL → MR loads → ZQ → DLL reset → REF.
- Drives `dfi_init_start`; waits for `dfi_init_complete` from PHY.
- Promotes `status_init_done` when the walk finishes.

Queues / arrays
- Init state machine + per-step delay counter.

## 14. `page_predictor`  (command_scheduler_macro)

What it does
- HAPPY_HYBRID page policy: predicts whether each (rank, bank) will see
  another row-hit within a window; biases the per-cmd RDA/WRA decision.

Queues / arrays
- Per-bank predict-keep-open bitmap.

---

## 15. `wr_beat_sequencer`  (data_path_macro)

What it does
- On scheduler write-op handshake, opens a per-slot pull pipeline:
  walks `wbuf` at the slot's `w_buf_ptr` for `bl_i` beats, with
  byte-strobe masking from `strb_buf`.
- Pads short AXI bursts to DRAM BL (e.g. 1-beat AXI to BL=4).
- Strobes `b_complete` + `b_complete_len` back to axi_intake's
  `wbuf_free` so wbuf flow control can decrement.

Queues / arrays
- Per-op active context (small: slot, ptr, beat counter, BL).

## 16. `rd_cl_aligner`  (data_path_macro)

What it does
- Three pipelines walking a per-op FIFO (MAX_CONCURRENT = RD_CAM_DEPTH
  = 16):
  - EN: drives `dfi_rddata_en` at the right cycle for the EN-head op.
  - CAP: latches `dfi_rddata` into a per-op staging buffer when
    `dfi_rddata_valid` fires for the CAP-head op.
  - EMIT: streams one DRAM beat per cycle out `rd_inject_*` to
    axi_intake, paced by host rready.
- Each pipeline has its own FIFO-position head pointer; heads advance
  past done / invalid ops so a slot-reuse new op at the tail can still
  receive EN and CAP.

Queues / arrays
- `r_stage [MAX_CONCURRENT] [MAX_DFI_CYC]` — per-op DFI-rate staging,
  16 × 128 × DFI_DATA_WIDTH bits at max BL.
- `r_op_valid / id / slot / len / wait_cnt / en_remaining /
  dfi_captured / beats_emitted` — per-op control regs (16 each).
- `r_fifo[MAX_CONCURRENT]` — order-of-arrival slot indices.
- `r_en_head_idx / r_cap_head_idx` — independent walks of `r_fifo`.

---

## 17. `dfi_cmd_formatter`  (dfi_v21_interface_macro)

What it does
- Translates scheduler `(op, rank, bank, row, col, len)` into DFI v2.1
  per-phase address / bank / cas_n / ras_n / we_n bus values.
- DDR2 vs LPDDR2 CA-bus encoding selected by `memtype_i`.
- Handles MRS, ZQCL/ZQCS, REF, PRE-ALL.

Queues / arrays
- 1-stage pre-formatted command register (combinational packing).

## 18. `dfi_signal_pack`  (dfi_v21_interface_macro)

What it does
- Final DFI-rate signal pack: DFI_RATE × per-phase command/data lanes.
- Drives `dfi_wrdata` / `dfi_wrdata_en` / `dfi_wrdata_mask`,
  `dfi_rddata_en`, and the per-rank `dfi_dram_clk_disable` lanes.
- DDR2 differential CKE / ODT handling.

Queues / arrays
- Output flop bank (strict-flop boundary to PHY).

---

## End of the path

The `dfi_v21_interface_macro` boundary is the system DFI port:
`dfi_address`, `dfi_bank`, `dfi_cas_n/ras_n/we_n/cs_n`, `dfi_cke`,
`dfi_odt`, `dfi_wrdata*`, `dfi_rddata*`, `dfi_init_*`. A PHY (or
DFISlavePHY BFM in DV) terminates this side, talks DDR2 / LPDDR2 wires
to the DRAM, and the loop closes by writing `dfi_rddata_valid` +
`dfi_rddata` back into `rd_cl_aligner`'s CAP pipeline.
