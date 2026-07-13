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

# Global Timers (`global_timers`)

**Module:** `global_timers.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_mem_cmd_scheduler`
**Status:** Implemented (per-rank tFAW/tRRD; global tWTR/tRTW/tCCD; strict-flop outputs)

> **Replaces the retired cross-bank timer block.** The original `xbank_timers`
> FUB owned a mix of per-bank AND cross-bank counters. That mix has been split:
>
> - **Per-bank** timing (tRCD, tRP, tRAS, tRC, tWR/tRTP) moved into
>   [`bank_timer`](09_bank_machine.md), stamped per (rank, bank) by
>   `pumice_bank_timers`.
> - **Cross-bank / channel-wide** turnaround (tFAW, tRRD, tWTR, tRTW, tCCD)
>   lives here in `global_timers`.
>
> The retired block's cross-rank extras (`tRTRS`, `tCS`, the `last_rd_rank` /
> `last_cmd_rank` chains, and the wide `blocks_*[NR][NB]` broadcast) are **not**
> in the live RTL. `global_timers` emits compact per-rank / global `*_window_ok`
> readiness bits that the arbiter ANDs with `bank_timer`'s `safe_*` outputs.

---

## Purpose

`global_timers` holds the controller-wide DRAM constraints that span banks and
therefore cannot live inside a single bank's timer:

- **tFAW** — no more than four ACT commands within a rolling `t_faw_i` window.
  Tracked **per rank** (each rank has its own 4-deep sliding window) so a
  multi-rank build enforces the device-local four-activate limit independently.
- **tRRD** — minimum cycles between any two ACTs, **per rank**.
- **tWTR** — cycles since the last WR (global; the DQ bus is shared).
- **tRTW** — cycles since the last RD (global; shared DQ bus).
- **tCCD** — cycles since the last column command (global; paces back-to-back
  RD/WR across banks on the shared DQ bus).

The arbiter reads five readiness outputs — `tfaw_window_ok_o[r]`,
`trrd_window_ok_o[r]` (per rank), and `twtr_global_ok_o`, `trtw_window_ok_o`,
`tccd_window_ok_o` (global) — and ANDs the relevant subset into its eligibility
decision alongside the per-bank `safe_*` bits.

---

## Constraint Scope

| Constraint | Scope            | Why                                                                 |
|------------|------------------|---------------------------------------------------------------------|
| `tFAW`     | per rank         | Four-Activate-Window — device-local thermal/power limit             |
| `tRRD`     | per rank         | Minimum ACT-to-ACT stagger inside one DRAM device                   |
| `tCCD`     | global (channel) | Column-to-column pacing on the shared DQ bus                        |
| `tWTR`     | global (channel) | Write → read turnaround on the shared DQ bus                        |
| `tRTW`     | global (channel) | Read → write turnaround on the shared DQ bus                        |

There is **no cross-rank (tRTRS / tCS) tracking** in the live module. `NUM_RANKS`
only sizes the per-rank tFAW/tRRD arrays; for `NUM_RANKS == 1` those arrays are a
single element and the per-rank outputs collapse to a single bit. The DQ-bus
turnaround counters (tWTR/tRTW/tCCD) are single global counters shared across all
ranks because the DQ bus is physically shared.

---

## Synthesis Parameters

| Parameter    | Default            | Effect                                                    |
|--------------|--------------------|-----------------------------------------------------------|
| `NUM_RANKS`  | 1                  | Number of per-rank tFAW windows and tRRD counters         |
| `NUM_BANKS`  | 8                  | Present for interface symmetry; not used to size counters |
| `RKW`        | `clog2(NUM_RANKS)` | Width of `evt_act_rank_i` (min 1)                         |
| `BKW`        | `clog2(NUM_BANKS)` | Bank-select width (interface symmetry)                    |

All timing reload values are runtime CSR-backed 8-bit inputs (`t_faw_i`,
`t_rrd_i`, `t_wtr_global_i`, `t_rtw_i`, `t_ccd_i`) — not parameters.

---

## Per-Rank Trackers

### tFAW window — `r_faw_slots[NUM_RANKS][4]`

Each rank owns a 4-deep pool of 8-bit down-counters (`logic
[NUM_RANKS-1:0][3:0][7:0]`). Every cycle each non-zero slot decrements. On an
ACT to a rank, the slot with the **smallest remaining count** is reloaded with
`t_faw_i`:

```systemverilog
if (evt_act_i) begin
    // pick the slot with the smallest remaining count for this rank
    automatic int unsigned slot_pick = 0;
    automatic logic [7:0] slot_min = 8'hFF;
    for (int unsigned i = 0; i < 4; i++) begin
        if (r_faw_slots[evt_act_rank_i][i] < slot_min) begin
            slot_min  = r_faw_slots[evt_act_rank_i][i];
            slot_pick = i;
        end
    end
    r_faw_slots[evt_act_rank_i][slot_pick] <= t_faw_i;
    r_trrd_cnt [evt_act_rank_i]            <= t_rrd_i;
end
```

The window is "OK" (an ACT may issue) when **at least one** of the rank's four
slots is at 0 — i.e. fewer than four of the most-recent ACTs are still inside the
tFAW window:

```systemverilog
w_tfaw_ok[k] = 1'b0;
for (int unsigned i = 0; i < 4; i++)
    if (r_faw_slots[k][i] == 8'd0) w_tfaw_ok[k] = 1'b1;
```

The "pick smallest count" load policy is equivalent to "replace the oldest
entry," which is the correct rolling-window behavior. It avoids a timestamp FIFO
(which would need a subtractor at check time); the check is a 4-way
compare-to-zero, one LUT layer.

### tRRD — `r_trrd_cnt[NUM_RANKS]`

One 8-bit down-counter per rank, reloaded with `t_rrd_i` on each ACT to that rank
(see the ACT block above). `trrd_window_ok_o[r]` is `(r_trrd_cnt[r] == 0)`.
An ACT on rank 0 does not affect `r_trrd_cnt[1]`.

---

## Global Trackers (channel-wide)

Three single 8-bit counters shared across all ranks:

| Counter      | Reload trigger        | Reload value       | Drives                |
|--------------|-----------------------|--------------------|-----------------------|
| `r_twtr_cnt` | `evt_wr_i` (WR event) | `t_wtr_global_i`   | `twtr_global_ok_o`    |
| `r_trtw_cnt` | `evt_rd_i` (RD event) | `t_rtw_i`          | `trtw_window_ok_o`    |
| `r_tccd_cnt` | `evt_wr_i` OR `evt_rd_i` (any column command) | `t_ccd_i` | `tccd_window_ok_o` |

```systemverilog
if (evt_wr_i) begin r_twtr_cnt <= t_wtr_global_i; r_tccd_cnt <= t_ccd_i; end
if (evt_rd_i) begin r_trtw_cnt <= t_rtw_i;        r_tccd_cnt <= t_ccd_i; end
```

Each `*_ok` output is asserted when its counter is 0. tCCD reloads on **either** a
read or a write, so it paces every column-to-column gap on the shared bus. tWTR
loads on writes and gates reads; tRTW loads on reads and gates writes.

At DDR2-800 tRTW is typically 0 cycles, but the counter is still synthesized for
parameter consistency and forward-compatibility with DDR3+ where tRTW matters.

> **Note on the tWTR trigger.** In the live RTL, tWTR reloads on the WR
> *command* event (`evt_wr_i`), not on a separate last-write-data-beat strobe.
> The CSR-supplied `t_wtr_global_i` value therefore carries whatever additional
> WL+BL/2 offset the timing programming folds in; there is no data-path
> `wr_last_beat` input to this module.

---

## Readiness Outputs (strict-flop)

The `*_window_ok_o` outputs are **registered** (strict-flop house style). Each
cycle the module computes the next-cycle window-ok values combinationally, then
flops them:

```systemverilog
// next-cycle tFAW-ok (combinational, per rank)
tfaw_window_ok_o <= w_tfaw_ok;
for (int unsigned k = 0; k < NUM_RANKS; k++)
    trrd_window_ok_o[k] <= (r_trrd_cnt[k] == 8'd0);
twtr_global_ok_o <= (r_twtr_cnt == 8'd0);
trtw_window_ok_o <= (r_trtw_cnt == 8'd0);
tccd_window_ok_o <= (r_tccd_cnt == 8'd0);
```

Out of reset, every `*_ok` output is driven to its permissive value (`'1` /
`1'b1`) so the arbiter is not spuriously blocked before any command has issued.

Because the outputs are flopped, the arbiter sees a one-cycle-registered view of
the counters — the same single-stage discipline as `bank_timer`'s combinational
`safe_*`, one flop deeper. The arbiter accounts for this uniform one-cycle
readiness latency across both timer FUBs.

---

## Observability

All observability outputs are combinational "counter non-zero" flags:

| Signal            | Width | Meaning                          |
|-------------------|-------|----------------------------------|
| `obs_faw_nz_o`    | NR    | Rank's tFAW window currently full (`!w_tfaw_ok[r]`) |
| `obs_trrd_nz_o`   | NR    | `r_trrd_cnt[r] != 0`             |
| `obs_twtr_nz_o`   | 1     | `r_twtr_cnt != 0`               |
| `obs_trtw_nz_o`   | 1     | `r_trtw_cnt != 0`               |
| `obs_tccd_nz_o`   | 1     | `r_tccd_cnt != 0`               |

---

## Interface

### Clocks / Reset

| Signal       | Direction | Description               |
|--------------|-----------|---------------------------|
| `mc_clk`     | input     | Controller clock          |
| `mc_rst_n`   | input     | Active-low async reset    |

### Timing config (CSR-backed)

| Signal            | Width | Constraint          |
|-------------------|-------|---------------------|
| `t_faw_i`         | 8     | tFAW                |
| `t_rrd_i`         | 8     | tRRD                |
| `t_wtr_global_i`  | 8     | tWTR                |
| `t_rtw_i`         | 8     | tRTW                |
| `t_ccd_i`         | 8     | tCCD (CAS-to-CAS)   |

### Events from the arbiter

| Signal            | Width | Description                       |
|-------------------|-------|-----------------------------------|
| `evt_act_i`       | 1     | ACT issued this cycle             |
| `evt_act_rank_i`  | RKW   | Rank of the ACT (selects tFAW/tRRD) |
| `evt_rd_i`        | 1     | RD issued this cycle              |
| `evt_wr_i`        | 1     | WR issued this cycle              |

### Readiness to the arbiter

| Signal               | Width | Description                          |
|----------------------|-------|--------------------------------------|
| `tfaw_window_ok_o`   | NR    | Per-rank: rank may issue another ACT |
| `trrd_window_ok_o`   | NR    | Per-rank: tRRD elapsed               |
| `twtr_global_ok_o`   | 1     | Global: tWTR elapsed (RD may follow WR) |
| `trtw_window_ok_o`   | 1     | Global: tRTW elapsed (WR may follow RD) |
| `tccd_window_ok_o`   | 1     | Global: tCCD elapsed (next column cmd OK) |

### Observability

`obs_faw_nz_o[NR]`, `obs_trrd_nz_o[NR]`, `obs_twtr_nz_o`, `obs_trtw_nz_o`,
`obs_tccd_nz_o`.

---

## Timing Budget

Event → readiness is single-cycle plus the output flop:

```
cycle T:   arbiter asserts evt_act_i, evt_act_rank_i = r
cycle T:   r_trrd_cnt[r] <- t_rrd_i; picked tFAW slot <- t_faw_i
cycle T+1: trrd_window_ok_o[r] = 0 (registered); another ACT to rank r blocked
```

The window-ok comparators are one LUT layer (compare-to-zero) feeding the output
flop, so the path is short. The arbiter combines these with the per-bank
`safe_*` bits; the aggregate eligibility AND is the arbiter's own critical path
(§2.7), not this module's.

---

## Verification Notes (cocotb test plan)

| Scenario                                                            | What it proves                                  |
|---------------------------------------------------------------------|-------------------------------------------------|
| Two ACTs to same rank, gap < tRRD                                   | Second blocked; `trrd_window_ok_o[r]` low       |
| Two ACTs to same rank, gap == tRRD                                  | Second issues exactly at tRRD                   |
| Five ACTs to one rank inside tFAW window                            | Fifth blocked; all four slots non-zero          |
| Five ACTs spanning the tFAW boundary (4 in + 1 aged out)            | Fifth issues; oldest slot returned to 0         |
| Multi-rank: ACTs on rank 0 do not block ACTs on rank 1              | Per-rank tRRD / tFAW isolation                  |
| WR then RD before tWTR elapses                                      | RD blocked; `twtr_global_ok_o` low              |
| RD then WR before tRTW elapses                                      | WR blocked; `trtw_window_ok_o` low              |
| Back-to-back column commands before tCCD elapses                    | Second column blocked; `tccd_global_ok_o` low   |
| Reset → all `*_ok` outputs assert permissively                      | Reset default correctness                       |
| tFAW "pick smallest" evicts the oldest slot                         | Rolling-window load policy                      |

---

## Open Questions / Future Work

- **Cross-rank turnaround (tRTRS / tCS).** The live module has no rank-switch
  DQ-handoff or chip-select-setup tracking. On the DDR2/LPDDR2 board targets
  (single rank, or same-rank streaming) these are met by IOB margin. A true
  multi-rank DDR3/DDR4 build would add a `last_rd_rank` / `last_cmd_rank` pair
  and cross-rank gate here — reserved but not implemented.
- **tWTR from data-path event.** tWTR currently reloads on the WR command event,
  relying on the CSR value to fold in WL+BL/2. A more precise implementation
  would load from the last-write-data-beat strobe; add a `wr_last_beat_i` input
  if characterization shows the command-relative approximation costs bandwidth.
- **Bank-group tCCD (DDR4).** DDR4 splits tCCD into same-group (tCCD_L) vs
  different-group (tCCD_S). DDR2/LPDDR2 have no bank groups, so the single global
  tCCD is exact here; the DDR4 family controller adds per-group tracking.
