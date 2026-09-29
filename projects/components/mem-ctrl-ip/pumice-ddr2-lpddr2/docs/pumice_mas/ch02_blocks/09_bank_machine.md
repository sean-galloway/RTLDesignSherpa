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

# Bank Timer (`bank_timer` + `pumice_bank_timers`)

**Module:** `bank_timer.sv` (per-bank) / `pumice_bank_timers.sv` (aggregator)
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_mem_cmd_scheduler`
**Status:** Implemented (FSM-free countdown-timer model)

> **Replaces the retired bank machine.** The original architecture placed a
> per-(rank, bank) seven-state FSM (`bank_machine_fub`) between the scheduler
> and the DFI encoder. That block **no longer exists**. Per-bank JEDEC timing
> is now enforced by `bank_timer.sv` — a set of preset/decrement countdown
> timers with a trivial row-open register and **no state machine at all**.
> `pumice_bank_timers.sv` stamps one `bank_timer` per (rank, bank) and fans the
> scheduler's command-event strobes to the addressed instance.
>
> The retirement was deliberate: the old FSM double-registered readiness (state
> register + next-state combinational + accepts flop), so the scheduler saw
> readiness two cycles stale. That staleness was the root cause of the
> refresh-vs-ACT and column-vs-PRE hazards observed during bring-up. The
> FSM-free model collapses the readiness path to a **single register stage**
> (the timers themselves), so the arbiter sees the just-issued command's effect
> exactly one cycle later.

---

## Purpose

`bank_timer` tracks one DRAM bank's JEDEC "safe" timing. For each JEDEC
per-bank constraint it holds a down-counter that is preset on the triggering
command and free-runs toward zero (saturating at 0). A constraint is "safe"
when its counter reads 0. The per-command readiness outputs (`safe_act`,
`safe_rd`, `safe_wr`, `safe_pre`) are a **combinational AND** of the relevant
timers plus a one-bit row-open flag — no FSM, no multi-stage lag.

The scheduler (`pumice_cmd_arbiter`, the single command issuer in the design)
drives one `set_*` strobe per issued command. Each timer reloads its config
value on its trigger; the `safe_*` outputs therefore reflect the just-issued
command one cycle later. The arbiter ANDs these per-bank `safe_*` signals with
the channel-wide turnaround windows from `global_timers` (§2.10) to decide
which command may fire.

`pumice_bank_timers` is a thin aggregator: it instantiates `NUM_RANKS ×
NUM_BANKS` copies of `bank_timer` and routes the arbiter's single command-event
bus (`evt_*` + `evt_rank_i` / `evt_bank_i`) to the one addressed instance. All
other instances see their `set_*` strobes deasserted that cycle and simply
continue counting down.

---

## Synthesis Parameters

### `bank_timer`

| Parameter    | Default | Effect on this FUB                                              |
|--------------|---------|-----------------------------------------------------------------|
| `ROW_WIDTH`  | 14      | Width of `open_row_o` register and the `row_i` input            |
| `TW`         | 8       | Timer width (bits) for all five countdown timers                |

### `pumice_bank_timers`

| Parameter    | Default             | Effect                                                          |
|--------------|---------------------|-----------------------------------------------------------------|
| `NUM_RANKS`  | 1                   | Rank dimension of the instance array; width of `evt_rank_i` sel |
| `NUM_BANKS`  | 8                   | Bank dimension of the instance array; width of `evt_bank_i` sel |
| `ROW_WIDTH`  | 14                  | Passed to each `bank_timer`                                     |
| `RKW`        | `clog2(NUM_RANKS)`  | Rank-select width (min 1)                                       |
| `BKW`        | `clog2(NUM_BANKS)`  | Bank-select width                                              |

There is **no per-instance rank/bank identifier parameter**. Identity comes from
the genvar position in `pumice_bank_timers`' nested generate loop; the arbiter
selects an instance by comparing `evt_rank_i` / `evt_bank_i` against that
position (`w_sel`). All five timers share the same `TW`-bit width; the
JEDEC cycle counts are supplied at runtime on the `t_*_i` ports (CSR-backed),
not fixed as parameters.

---

## Instantiation Pattern

From `pumice_bank_timers.sv` — the nested generate that stamps the array:

```systemverilog
for (genvar k = 0; k < NUM_RANKS; k++) begin : g_rank
    for (genvar b = 0; b < NUM_BANKS; b++) begin : g_bank
        // route the scheduler's command event to THIS bank only
        logic w_sel;
        assign w_sel = (evt_rank_i == RKW'(k)) && (evt_bank_i == BKW'(b));

        bank_timer #(.ROW_WIDTH(ROW_WIDTH)) u_bt (
            .clk(aclk), .rst_n(aresetn),
            .t_rcd_i(t_rcd_i), .t_rp_i(t_rp_i), .t_ras_i(t_ras_i),
            .t_rc_i(t_rc_i), .t_wr_i(t_wr_i), .t_rtp_i(t_rtp_i),
            .set_act_i(evt_act_i && w_sel),
            .set_rd_i (evt_rd_i  && w_sel),
            .set_wr_i (evt_wr_i  && w_sel),
            .set_pre_i(evt_pre_i && w_sel),
            .set_ap_i (evt_ap_i),
            .row_i(evt_row_i),
            .safe_act_o (bank_act_ready_o [k][b]),
            .safe_rd_o  (bank_rdwr_ready_o[k][b]),
            .safe_wr_o  (/* == safe_rd */),
            .safe_pre_o (bank_pre_ready_o [k][b]),
            .row_valid_o(bank_row_active_o[k][b]),
            .open_row_o (bank_open_row_o  [k][b]),
            .state_o    (bank_state_o     [k][b]),
            /* obs_* ... */
        );
    end
end
```

The per-(rank, bank) readiness outputs are 2-D-packed arrays
(`logic [NUM_RANKS-1:0][NUM_BANKS-1:0]`) consumed directly by
`pumice_cmd_arbiter`. There is no aggregation logic beyond the packing — pure
structural fan-out. Note that `safe_wr_o` is left unconnected in the aggregator
because inside `bank_timer` it is identical to `safe_rd_o` (see the RTL: `assign
safe_wr_o = safe_rd_o`); the arbiter uses the single `bank_rdwr_ready_o` bit for
both RD and WR column commands.

---

## The Timer Pool (per bank)

`bank_timer` holds five countdown registers (`r_rcd`, `r_ras`, `r_rc`, `r_rp`,
`r_preblk`), each `TW` bits, plus a one-bit `r_row_valid`, the `r_open_row`
register, and a single `r_ap_pending` auto-precharge bit. Every timer is a
down-counter: reload on its trigger, else decrement while non-zero (saturate
at 0).

| Timer      | JEDEC constraint | Reload trigger              | Reload value | Gates          |
|------------|------------------|-----------------------------|--------------|----------------|
| `r_rcd`    | tRCD (ACT → RD/WR) | `set_act_i`               | `t_rcd_i`    | `safe_rd/wr`   |
| `r_ras`    | tRAS (ACT → PRE min) | `set_act_i`             | `t_ras_i`    | `safe_pre`     |
| `r_rc`     | tRC  (ACT → ACT same bank) | `set_act_i`       | `t_rc_i`     | `safe_act`     |
| `r_rp`     | tRP  (PRE → ACT)   | `set_pre_i` OR auto-PRE fire | `t_rp_i`   | `safe_act`     |
| `r_preblk` | tRTP (RD) / tWR (WR) | `set_rd_i` / `set_wr_i` | `t_rtp_i` / `t_wr_i` | `safe_pre` |

The `t_*_i` reload values are supplied by the parent (`pumice_bank_timers`
forwards its own 8-bit `t_*_i` inputs, which are CSR-backed JEDEC timing
fields). They are sampled live on each reload — the timer does not stage them.

**Note:** the retired FSM's separate `t_cl_cnt` / `t_cwl_cnt` (column-busy
windows) are **gone**. Column-to-column pacing (tCCD) and the read-drives-DQ /
write-recovery windows are enforced globally in `global_timers` (tCCD/tWTR/tRTW)
and, for the write-recovery-before-precharge case, folded into the `r_preblk`
timer here. There is no per-bank "RD_BUSY / WR_BUSY" occupancy state anymore.

---

## Row-Open Register and Auto-Precharge (no FSM)

Row state is a two-element register — `r_row_valid` + `r_open_row` — plus one
`r_ap_pending` bit. There is no enumerated state; the priority in the RTL is
**ACT > explicit PRE > auto-PRE fire > column**:

```systemverilog
if (set_act_i) begin
    r_row_valid  <= 1'b1;
    r_open_row   <= row_i;
    r_ap_pending <= 1'b0;
end else if (set_pre_i) begin
    r_row_valid  <= 1'b0;
    r_ap_pending <= 1'b0;
end else if (w_ap_fire) begin
    r_row_valid  <= 1'b0;
    r_ap_pending <= 1'b0;
end else if (set_rd_i || set_wr_i) begin
    r_ap_pending <= set_ap_i;   // latch the RDA/WRA qualifier
end
```

**Auto-precharge** (RDA / WRA) is a single bit, not a state. `set_ap_i`
qualifies a RD/WR issue; if set, `r_ap_pending` latches. The auto-precharge
"fires" combinationally once the read/write recovery window and tRAS have both
elapsed:

```systemverilog
assign w_ap_fire = r_ap_pending && (r_preblk == '0) && (r_ras == '0);
```

When `w_ap_fire` asserts, the row closes internally (`r_row_valid <= 0`) and
`r_rp` reloads with `t_rp_i` — exactly as an explicit PRE would. No PRE command
is consumed from the scheduler and no extra state is entered. This is the same
degeneracy the old FSM's "auto-pre pending" trick achieved, but here it is one
flop and one AND gate.

**Open-page behavior.** A bare RD/WR (with `set_ap_i` low) only reloads
`r_preblk` and leaves `r_row_valid` set, so the row stays open. Successive
column commands to the open row stream at the channel-wide tCCD rate enforced by
`global_timers`; the bank timer imposes no additional per-column pacing.

---

## Combinational `safe_*` Outputs

The readiness outputs are pure combinational functions of the timer/flag
registers — one register stage behind the arbiter's issue decision:

```systemverilog
// ACT: bank precharged (row closed), tRP since PRE, tRC since last ACT.
assign safe_act_o = !r_row_valid && (r_rp == '0) && (r_rc == '0);
// RD/WR: row open, tRCD met, not auto-precharging.
assign safe_rd_o  = r_row_valid && (r_rcd == '0) && !r_ap_pending;
assign safe_wr_o  = safe_rd_o;
// PRE: row open, tRAS + tRTP/tWR met, not auto-precharging.
assign safe_pre_o = r_row_valid && (r_ras == '0) && (r_preblk == '0) && !r_ap_pending;
```

The `!r_ap_pending` term on `safe_rd_o` / `safe_pre_o` is what makes an
auto-precharging bank refuse further column commands and a redundant explicit
PRE while its internal auto-PRE is still pending — the arbiter naturally skips
the bank until the row closes and `safe_act_o` re-asserts.

Because these are combinational off single-stage registers, the arbiter's
per-cycle pick sees the effect of the command it issued on cycle *T* on cycle
*T+1*. There is no second flop between the timer and the arbiter, so a command
issued this cycle cannot be double-issued next cycle — the class of hazard that
motivated retiring the FSM.

---

## Derived State (observability only)

A `bank_state_e` (`state_o`) is produced **purely for observability** — no
downstream logic reads it. It is decoded combinationally from the row-valid flag
and the timers:

```systemverilog
if (r_row_valid) state_o = (r_rcd != '0) ? BANK_ACTIVATING : BANK_ACTIVE;
else             state_o = (r_rp  != '0) ? BANK_PRECHARGING : BANK_IDLE;
```

This gives waveform viewers and CSR telemetry the familiar IDLE / ACTIVATING /
ACTIVE / PRECHARGING names without the design actually implementing them as a
sequencer. It is a decode of the timers, not the source of truth.

The remaining observability outputs are single-bit non-zero flags on the timers
and the auto-pre bit: `obs_rcd_nz_o`, `obs_preblk_nz_o`, `obs_ras_nz_o`,
`obs_ap_pending_o` (per bank, fanned out to `obs_*` arrays in the aggregator).

---

## Interface (`pumice_bank_timers`)

### Clocks / Reset

| Signal     | Direction | Description                        |
|------------|-----------|------------------------------------|
| `aclk`     | input     | Controller clock                   |
| `aresetn`  | input     | Active-low async reset             |

### Timing config (CSR-backed, per-bank JEDEC cycle counts)

| Signal      | Width | Constraint |
|-------------|-------|------------|
| `t_rcd_i`   | 8     | tRCD       |
| `t_rp_i`    | 8     | tRP        |
| `t_ras_i`   | 8     | tRAS       |
| `t_rc_i`    | 8     | tRC        |
| `t_wr_i`    | 8     | tWR (WR cmd → earliest PRE, incl WL+BL/2) |
| `t_rtp_i`   | 8     | tRTP (RD cmd → earliest PRE) |

### Command-event strobes from the arbiter

| Signal        | Width | Description                              |
|---------------|-------|------------------------------------------|
| `evt_act_i`   | 1     | ACT issued this cycle                    |
| `evt_rd_i`    | 1     | RD  issued this cycle                    |
| `evt_wr_i`    | 1     | WR  issued this cycle                    |
| `evt_pre_i`   | 1     | PRE issued this cycle                    |
| `evt_ap_i`    | 1     | Auto-precharge qualifier (with RD/WR)    |
| `evt_rank_i`  | RKW   | Rank of the issued command (selects instance) |
| `evt_bank_i`  | BKW   | Bank of the issued command (selects instance) |
| `evt_row_i`   | ROW_WIDTH | Row operand (latched on ACT)          |

### Per-bank readiness to the arbiter (combinational, single-stage)

| Signal                       | Width           | Description                     |
|------------------------------|-----------------|---------------------------------|
| `bank_act_ready_o[NR][NB]`   | 1 each          | `safe_act` per bank             |
| `bank_rdwr_ready_o[NR][NB]`  | 1 each          | `safe_rd` (== `safe_wr`) per bank |
| `bank_pre_ready_o[NR][NB]`   | 1 each          | `safe_pre` per bank             |
| `bank_row_active_o[NR][NB]`  | 1 each          | `row_valid` per bank            |
| `bank_open_row_o[NR][NB]`    | ROW_WIDTH each  | Open row per bank               |
| `bank_state_o[NR][NB]`       | `bank_state_e`  | Decoded state (observability)   |

### Observability

`obs_act_cnt_nz_o`, `obs_preblk_nz_o`, `obs_ras_nz_o`, `obs_ap_pending_o` —
each a `[NR][NB]` bit array, mirroring the per-bank `obs_*` outputs.

---

## Timing Budget

The path from a command event to updated readiness is single-cycle:

```
cycle T:   arbiter asserts evt_act_i with evt_rank_i=r, evt_bank_i=b
cycle T:   w_sel picks instance (r,b); r_rcd/r_ras/r_rc load, r_row_valid <- 1
cycle T+1: safe_act_o[r][b] = 0 (r_rc/row_valid now block ACT),
           safe_rd_o[r][b]  gated by r_rcd countdown
```

`safe_*_o` is combinational from the registers, so the arbiter consumes the
post-event readiness on the very next cycle — no race allowing a second issue to
the same bank while its constraint is still counting. This one-cycle discipline
is the whole point of the FSM-free rework: readiness is exactly one register
stage deep, versus the retired FSM's two (state + accepts).

---

## Verification Notes (cocotb test plan)

| Scenario                                                                | What it proves                                            |
|-------------------------------------------------------------------------|-----------------------------------------------------------|
| ACT → wait tRCD → RD; RD blocked until `r_rcd == 0`                     | tRCD gate on `safe_rd`                                    |
| ACT → RDA; row auto-closes once `r_preblk` and `r_ras` clear            | `w_ap_fire` closes row, reloads `r_rp`; no scheduler PRE  |
| ACT → WRA; `r_preblk` loads tWR; auto-PRE waits for tWR AND tRAS        | Write-recovery folded into `r_preblk`                     |
| Bare RD (set_ap=0) keeps row open; second RD to same row allowed        | Open-page: `r_row_valid` stays set                        |
| ACT → PRE (explicit) → ACT; second ACT blocked until `r_rp == 0`        | tRP gate on `safe_act`                                    |
| Two ACTs same bank; second blocked until `r_rc == 0`                    | tRC gate on `safe_act`                                    |
| `safe_rd` deasserts while `r_ap_pending` set (mid auto-PRE)             | Auto-precharging bank refuses new column commands         |
| Aggregator: `evt_bank_i=b` only reloads instance b; others count down   | `w_sel` routing correctness                               |
| `state_o` decode matches timers (ACTIVATING while `r_rcd != 0`)         | Observability decode                                      |
| Reset during any countdown → all timers and row flag clear              | Reset behavior                                            |

---

## Open Questions / Future Work

- **Timer width.** `TW = 8` covers the DDR2/LPDDR2 board targets (tRC ≈ tens of
  cycles). A DDR3/DDR4 family part at a higher CK:MC ratio could need wider
  timers; `TW` is already a parameter, so this is a re-elaboration, not a rework.
- **Per-bank vs shared tRC.** tRC is enforced per bank here. If a future family
  needs same-bank-group tRC differentiation (DDR4 bank groups), that logic would
  land in `global_timers`, not here — `bank_timer` stays bank-local by design.
- **Auto-PRE vs explicit PRE priority.** The RTL priority is ACT > explicit PRE >
  auto-PRE. If the arbiter ever issued an explicit PRE to a bank with a pending
  auto-PRE, the explicit PRE wins and `r_ap_pending` clears. The arbiter does not
  do this today (it treats an auto-precharging bank as un-schedulable via
  `safe_*`), but the RTL is safe if it ever did.
