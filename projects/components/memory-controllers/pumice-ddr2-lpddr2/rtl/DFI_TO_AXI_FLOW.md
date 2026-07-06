# DFI-to-AXI flow (back path)

Companion to `AXI_TO_DFI_FLOW.md`. Two streams move data and metadata
back to the host:

1. **R path** — DFI read data arrives, gets aligned, becomes AXI R beats.
2. **B path** — internal write-commit strobe retires CAM slots, makes
   AXI B responses.

Plus a side path: the **forwarded R** (wr2rd snarf) where reads never
touch DFI at all.

```
                         DFI rddata + valid
                                │
                                ▼
[dfi_v21_interface_macro]  dfi_signal_pack (unpack) → DRAM beats
                                │
                                ▼
[data_path_macro]          rd_cl_aligner  CAP → r_stage → EMIT
                                │
                                ▼
[axi_frontend_macro]       axi_intake R-emit FSM (rd_inject OR fwd)
                                │
                                ▼
                           rd_cmd_cam.entry_complete (slot retire)
                                │
                                ▼
                            s_axi_r* to HOST


internal "write committed" strobe (from wr_beat_sequencer.b_complete)
                                │
                                ▼
[axi_frontend_macro]       wr_cmd_cam.entry_complete
                                │
                                ▼
                           axi_id_side_table (id/user lookup)
                                │
                                ▼
                           axi_intake b_fifo → drain
                                │
                                ▼
                            s_axi_b* to HOST
```

---

## R path

### 1. `dfi_signal_pack`  (dfi_v21_interface_macro)

What happens
- PHY drives `dfi_rddata` (DFI_RATE phases packed per DFI cycle) and
  `dfi_rddata_valid` for the cycles where the controller had earlier
  asserted `dfi_rddata_en`.
- Sub-FUB unpacks DFI-rate data into the DRAM-beat-wide signals the
  data path consumes.

No queues — output-flop boundary only.

### 2. `rd_cl_aligner.CAP`  (data_path_macro)

What happens
- CAP pipeline walks `r_fifo` with its own head pointer
  (`r_cap_head_idx`) and latches `dfi_rddata` into the per-op staging
  buffer when `dfi_rddata_valid` fires.
- The head advances past ops whose CAP is already done (or whose slot
  is no longer valid) so a slot-reuse new op at the FIFO tail still
  gets captured. This was the central wedge fix (task #205).

Queues / arrays touched on this leg
- `r_stage [MAX_CONCURRENT] [MAX_DFI_CYC]` — writes the DFI cycle into
  the staging cell indexed by `r_op_dfi_captured[w_cap_op]`.
- `r_op_dfi_captured[w_cap_op]` — increments per captured cycle.
- `r_cap_head_idx` — advances when the head op's CAP completes.

### 3. `rd_cl_aligner.EMIT`  (data_path_macro)

What happens
- EMIT pipeline reads `r_stage[r_fifo[0]]` at the DRAM-beat
  granularity, drives `rd_inject_valid_o / id_o / data_o / last_o` to
  axi_intake.
- One handshake per host R beat. On the last beat:
  - Pulses `rd_beat_we_o` with `rd_beat_slot_o` so rd_cmd_cam can
    retire the entry.
  - Pops the FIFO (shifts indices left, frees the slot).

Queues / arrays touched
- `r_op_beats_emitted[w_emit_op]` — beat counter.
- `r_fifo`, `r_fifo_count` — pop + shift on burst end.
- `r_op_valid[w_emit_op]` — cleared on last-beat handshake.

### 4. `axi_intake` R-emit FSM  (axi_frontend_macro)

What happens
- Selects between two R sources:
  - **rd_inject path** (from rd_cl_aligner) — normal DRAM-served read.
  - **forwarded path** (from wr2rd_forward) — read snarfed from wbuf;
    when `r_r_fwd_active`, the FSM drives R beats by indexing
    `r_w_buf[r_r_fwd_ptr]` for `r_r_fwd_remaining` cycles.
- Drives `s_axi_rid / rdata / rresp / rlast / ruser / rvalid`.
- Receives `s_axi_rready` from the host. `rd_inject_ready_o` echoes
  `s_axi_rready` (and is blocked while `r_r_fwd_active`).

Queues / arrays touched
- `r_r_fwd_active`, `r_r_fwd_id`, `r_r_fwd_ptr`, `r_r_fwd_remaining` —
  one forwarded-burst slot.
- `r_w_buf[]` (read side — same SRAM written by the W path).

### 5. `rd_cmd_cam.entry_complete`  (axi_frontend_macro)

What happens
- `rd_beat_we_i` from rd_cl_aligner increments `r_beats_returned[slot]`.
- When the next beat would equal `r_len[slot]`, asserts
  `entry_complete_o` with `entry_complete_slot_o` and
  `entry_complete_id_o`.
- Clears `r_valid[slot]` + `r_issued[slot]` → cam slot is free for the
  next AR push (the slot-reuse path).

Queues / arrays touched
- `r_beats_returned[slot]` — increments per rd_beat strobe.
- `r_valid[slot]`, `r_issued[slot]` — cleared on last beat.

---

## B path

### 6. `wr_beat_sequencer.b_complete`  (data_path_macro)

What happens
- After the wr op finishes draining wbuf into `dfi_wrdata` for that
  slot (BL beats, including any padding for short AXI bursts), strobes
  `b_complete_strb_o` with `b_complete_slot_o` and `b_complete_len_o`.
- This is the "DRAM write has committed" signal — does NOT wait for
  the host to actually receive B.

Queues / arrays touched
- Per-op pull pipeline (slot, ptr, beat counter) — finished at strobe.

### 7. `wr_cmd_cam.entry_complete`  (axi_frontend_macro)

What happens
- `b_complete_strb_i` from wr_beat_sequencer clears `r_valid[slot]` +
  `r_issued[slot]`, emits `wr_entry_complete_o` +
  `wr_entry_complete_slot_o` + `wr_entry_complete_id_o`.
- Also feeds `wbuf_free_strb` + `wbuf_free_len` back to axi_intake's
  flow-control counter so awready can re-open if it was gated.

Queues / arrays touched
- `r_valid[slot]`, `r_issued[slot]` — cleared.

### 8. `axi_id_side_table`  (axi_frontend_macro)

What happens
- On wr_entry_complete strobe, looks up the slot's saved
  `awuser / awqos / awid` and returns them so axi_intake can build
  a correct B packet (host expects its own id and user back).

Queues / arrays touched
- Per-slot side regs (read-only at this point).

### 9. `axi_intake` B-emit  (axi_frontend_macro)

What happens
- Push side: on `wr_entry_complete_strb_i`, enqueues
  `{bid, bresp, buser}` into `r_b_fifo` for that host id.
- Pop side: drives `s_axi_bid / bresp / buser / bvalid` from the FIFO
  head, handshakes against `s_axi_bready`.
- `r_wbuf_outstanding` decrements by `wbuf_free_len_i` (the freed beat
  count) — restores wbuf flow-control headroom.

Queues / arrays touched
- `r_b_fifo` (B_FIFO_DEPTH = 4) — pending B per host id.
- `r_wbuf_outstanding` — flow-control counter.

---

## Forwarded R side path (no DFI involvement)

When `wr2rd_forward` matches an AR against an in-flight write whose
wbuf still holds the data, the read NEVER goes to rd_cmd_cam /
scheduler / aligner / DFI. Instead:

- `wr2rd_forward` drives `fwd_valid_o` with the matching `w_buf_ptr`
  and `len` directly into axi_intake.
- axi_intake's R-emit FSM enters `r_r_fwd_active = 1`, blocks
  `rd_inject_ready_o` to the aligner, and streams `len` beats by
  reading `r_w_buf[r_r_fwd_ptr++]` each cycle into `s_axi_rdata`.
- On the last beat handshake, `r_r_fwd_active` clears and
  `rd_inject_ready_o` returns to track `s_axi_rready`.

Queues / arrays touched
- Same `r_w_buf[]` storage as the W path (no copy).
- `r_r_fwd_*` regs (single forwarded-burst slot).

---

## Where the loops close

- **R-channel host handshake** → `rd_beat_we_o` (in axi_intake) →
  `rd_cmd_cam.entry_complete` → slot freed → axi_intake can push the
  next pending AR into the now-empty cam slot. This is the AR_16
  slot-reuse case the wedge fix protects.
- **B-channel host handshake** → `r_b_fifo` pop. Note this does NOT
  free `wr_cmd_cam` — that already happened on `b_complete`. The B
  drain is a host-side concern only.
- **DFI valid / invalid alignment** is enforced by the EN pipeline's
  `dfi_rddata_en` schedule. CAP only latches when the controller's
  own EN said data should be coming back, so an unsolicited
  `dfi_rddata_valid` from the PHY is a protocol error, not a stall
  case.
