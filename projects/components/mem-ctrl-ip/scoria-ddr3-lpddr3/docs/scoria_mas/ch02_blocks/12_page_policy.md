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

# Page Policy (`scoria_page_policy`)

**Module:** `scoria_page_policy.sv`
**Location:** `rtl/fub/`
**Category:** scheduling policy / telemetry
**Parent:** `scoria_scheduler_layer`
**Status:** complete, sim-verified

---

## Purpose

`scoria_page_policy` watches the issued command stream and the per-bank row state, and produces two things: the auto-precharge decision fed back to the arbiter, and a set of page/row telemetry counters. It does not itself issue commands; it only tells the arbiter whether the current mode wants a bank closed, and it counts what happened.

The block is modeless in hardware — it has no FSM — and is selected by the `policy_mode_i` CSR at runtime.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_RANKS` | int | 1+ | 1 | ranks per channel |
| `NUM_BANKS` | int | 4..16 | 8 | banks per rank |
| `ROW_WIDTH` | int | — | 14 | row address width |
| `BKW` | int | derived | `$clog2(NUM_BANKS)` | bank index width |
| `RKW` | int | derived | `$clog2(NUM_RANKS)` if `NUM_RANKS > 1`, else 1 | rank index width |

: Table 2.12.1: Page policy parameters

## Interface

### Configuration and command tap

| Signal | Direction | Width | Description |
|---|---|---|---|
| `policy_mode_i` | in | 3 | page-policy mode select |
| `tr_init_i` | in | 8 | idle-timeout reload value |
| `cmd_valid_i` | in | 1 | arbiter accept strobe: `cmd_valid && cmd_ready` |
| `cmd_op_i` | in | `dram_op_e` | issued command opcode |
| `cmd_bank_i` | in | `BKW` | issued command bank |
| `cmd_row_i` | in | `ROW_WIDTH` | issued command row |
| `bank_row_active_i` | in | `NUM_BANKS` | per-bank row-valid flag from bank timers |
| `bank_open_row_i` | in | `NUM_BANKS*ROW_WIDTH` | per-bank open row from bank timers |
| `demand_i` | in | 1 | any CAM entry schedulable |

: Table 2.12.2: Page policy inputs

### Decisions and telemetry

| Signal | Direction | Width | Description |
|---|---|---|---|
| `ap_mode_en_o` | out | 1 | mode 1/2/3 override the legacy `w_ap` |
| `ap_close_o` | out | `NUM_BANKS` | per-bank auto-precharge close request |
| `timeout_pre_req_o` | out | 1 | background timeout-precharge request |
| `timeout_pre_bank_o` | out | `BKW` | bank selected for timeout precharge |
| `stat_page_hit_o` | out | 32 | every issued column op |
| `stat_page_miss_o` | out | 32 | ACT after a conflict close |
| `stat_page_empty_o` | out | 32 | ACT after a non-conflict close |
| `stat_act_o` | out | 32 | every issued ACT |
| `stat_pre_o` | out | 32 | every issued PRE/PREA |
| `stat_ref_o` | out | 32 | every issued REF |
| `stat_row_hit_o` | out | 32 × `NUM_BANKS` | column op with no pending ACT for that bank |
| `stat_ref_busy_o` | out | 32 | REFs issued while `demand_i` was high |

: Table 2.12.3: Page policy outputs

## Microarchitecture internals

### Modes

`policy_mode_i` selects among five live encodings; values 4-7 are retired and fall through to the build default.

| Mode | Name | `ap_mode_en_o` | `ap_close_o` | Close mechanism |
|---|---|---|---|---|
| 0 | default / legacy flat | 0 | 0 | legacy `page_policy_i` (`OPEN`/`CLOSE`) |
| 1 | static_open | 1 | all 0 | none — rows stay open |
| 2 | static_close | 1 | all 1 | auto-precharge on every column |
| 3 | fixed_open | 1 | all 0 | background idle timeout |
| 4-7 | retired | — | — | fall through to mode 0 |

: Table 2.12.4: Page-policy modes

Modes 4 and 5 (`adapt_time` and `adapt_access`) were retired after silicon measurements showed them equivalent to or worse than the fixed modes. Modes 6 and 7 (`rbl_static` and `rbl_dyn`) were retired after measurements showed them harmful or converging to mode 0. A write to 4-7 now behaves like the build default.

### Per-bank idle timeout

In `fixed_open` mode, each open bank runs an 8-bit down-counter:

```text
if (row closed or mode off):
    idle = 0; expired cleared
else if (command to this bank):
    idle = tr_init_i; expired = 0
else if (idle != 0):
    idle = idle - 1
    if (idle == 1 and tr_init_i != 0):
        expired = 1
```

`r_expired` is sticky: it raises at zero and holds until the row closes.

### Background close request

When `fixed_open` mode is on, the block scans the banks and requests a precharge on the lowest-numbered bank that is both open and expired. The arbiter issues the actual `PRE` at its lowest priority, gated by `bank_pre_ready_o` and the normal 2-cycle guards. This block never touches the command wires.

### Telemetry counters

The counters are free-running and cleared on reset; software subtracts two reads to form a window.

- `stat_page_hit_o` increments on every issued column op.
- `stat_page_miss_o` vs `stat_page_empty_o`: a single-bank precharge to a bank that is **not** timeout-closed sets `r_conflict_mark[bank]`. The next ACT to a marked bank is a miss; otherwise it is empty.
- `stat_row_hit_o[b]` counts a column op to bank `b` that arrives with no pending ACT for that bank.
- `stat_ref_busy_o` counts refreshes that fire while `demand_i` is high.

The conflict mark uses `w_is_pre1` (single-bank `PRE` only). `PREA` from refresh drain deliberately does **not** mark any bank, because its bank field is not an address and would otherwise make one arbitrary bank look like a conflict.

## FSM policy

No FSM. The mode is a CSR and the rest is combinational priority plus flop counters.

## Timing

All decision outputs are combinational from the registered bank state and the issued command. Telemetry counters update on the cycle the command is accepted.

## Notes

- **CSR encoding translation lives in `scoria_top`.** The legacy `REFRESH_TUNING.page_policy_or` CSR uses the software encoding `0=build default, 1=OPEN, 2=CLOSE, 3=HYBRID`, while `page_policy_e` inside the RTL is `OPEN=0, CLOSE=1, HYBRID=2`. A raw cast swapped OPEN and CLOSE and corrupted the entire open-page / reorder config axis (issue #42). `scoria_top` now performs an explicit `unique case` translation before driving `page_policy_i`. The `policy_mode_i` port of `scoria_page_policy` is already the translated enum.
- **Mode 0 is not mode 1.** Mode 0 means "use the legacy `page_policy_i` input"; mode 1 means "force open page". They produce the same result only when the legacy input already requests open page.
- **`tr_init_i == 0` disables the timeout.** That matches the CSR definition of 0 as build default.
