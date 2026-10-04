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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Scheduler and Command Arbiter (`andesite_mem_cmd_scheduler` + `andesite_cmd_arbiter`)

**Module:** `andesite_mem_cmd_scheduler.sv`, `andesite_cmd_arbiter.sv`
**Location:** `rtl/scheduler/`
**Category:** scheduling / arbitration
**Parent:** `andesite_core`
**Status:** specified — no RTL exists (HAS v0.1 posture)

---

## Purpose

The scheduler picks which ready command goes to the formatter each cycle. It inherits scoria's FR-FCFS arbiter and its maintenance request/grant channel. The andesite delta is L/S-aware issue: DDR4 bank groups add a same-group versus cross-group split to the command-spacing checks, and the global timers grow the `tCCD_L/S` and `tRRD_L/S` pairs. LPDDR4 has no bank groups, so the long and short checks collapse to one.

The scheduler never invents a new arbitration philosophy. It takes scoria's mechanism and teaches it about bank groups.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_BANK_GROUPS` | int | 1..4 | 4 for DDR4, 1 for LPDDR4 | bank-group count; `1` means ungrouped |
| `NUM_BANKS` | int | 8..16 | 16 for DDR4, 8 for LPDDR4 | total banks per rank |
| `CAM_DEPTH` | int | 8..32 | inherited | read and write command CAM depth |
| `MAINT_TAG_WIDTH` | int | 2..4 | 3 | distinguishes refresh, ZQ, ODT turnaround sources |

: Table 2.5.1: Scheduler parameters

`NUM_BANK_GROUPS = 1` is how LPDDR4 degenerates gracefully. There is no `if (memtype == LPDDR4)` branch in the issue check; the group index is constant and the L/S counters collapse by construction.

## Interface

### Host-side command ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `clk` | in | 1 | controller clock |
| `reset_n` | in | 1 | active-low reset |
| `init_done` | in | 1 | scheduler admits no host commands until high |
| `rd_cam_valid` | in | 1 | read command ready in the read CAM |
| `wr_cam_valid` | in | 1 | write command ready in the write CAM |
| `rd_cam_entry` | in | CAM entry | read candidate: bank, row, column, age |
| `wr_cam_entry` | in | CAM entry | write candidate: bank, row, column, age |
| `grant_to_rd` | out | 1 | read command wins this cycle |
| `grant_to_wr` | out | 1 | write command wins this cycle |
| `granted_entry` | out | CAM entry | the command being issued |

### Bank-group timing ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `tccd_l_csr` | in | timing width | `tCCD_L`, runtime CSR |
| `tccd_s_csr` | in | timing width | `tCCD_S`, runtime CSR |
| `trrd_l_csr` | in | timing width | `tRRD_L`, runtime CSR |
| `trrd_s_csr` | in | timing width | `tRRD_S`, runtime CSR |
| `last_cmd_group` | in/out | group width | bank group of the last-issued command |
| `outstanding_group_mask` | in/out | group count | groups with outstanding same-group spacing |

### Maintenance request/grant ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `maint_req` | in | 1 | any maintenance source wants the bus |
| `maint_tag` | in | `MAINT_TAG_WIDTH` | source tag: refresh, ZQ, ODT turnaround |
| `maint_grant` | out | 1 | bus granted to maintenance this cycle |
| `refresh_req` | in | 1 | from `refresh_ctrl` |
| `zq_req` | in | 1 | from `zq_ctrl` (DDR4 ZQCS/ZQCL or LPDDR4 MPC) |
| `odt_turn_req` | in | 1 | from `odt_ctrl` for RTT transitions |

: Table 2.5.2: Scheduler interface

## Microarchitecture internals

### FR-FCFS admission with L/S awareness

scoria's FR-FCFS arbiter is unchanged in spirit. Each candidate command is scored by age and readiness, and the highest scorer that passes the timing checks is granted. The andesite change is inside the timing check.

```text
issue_ok(cmd) = bank_timers.ok(cmd)
                AND global_timers.ok(cmd, group(cmd), group(last_cmd))
```

`group(cmd)` is the bank group of the candidate's bank. For a read or write command, the global-timer check now depends on whether the candidate targets the same bank group as the last-issued command:

- Same group: `tCCD_L` and `tRRD_L` apply.
- Different group: `tCCD_S` and `tRRD_S` apply.

The check also compares the candidate against outstanding same-group spacing tracked by `outstanding_group_mask`, because a burst of commands to one group can leave a trail of long-spacing obligations.

### Global timers

The global timer block inherits scoria's counters and adds four new ones. All are runtime CSRs.

| Counter | JEDEC symbol | Applies |
|---|---|---|
| `tCCD_L` | `tCCD_L` | same bank group |
| `tCCD_S` | `tCCD_S` | different bank groups |
| `tRRD_L` | `tRRD_L` | same bank group, activate-to-activate |
| `tRRD_S` | `tRRD_S` | different bank groups, activate-to-activate |

These join the inherited `tCCD`, `tRAS`, `tRC`, `tRP`, `tRCD`, `tWTR`, `tRTW`, `tWR`, and the read/write turnaround set. The values are runtime CSRs, initialised from the JESD79-4/JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

### Maintenance request/grant semantics

All maintenance traffic arrives as one `maint_req` with a `maint_tag`. The scheduler does not special-case refresh, ZQ, or ODT turnarounds; it sees one maintenance kind and a tag that the downstream formatter uses to pick the correct command encoding.

| Source | Tag value | Action when granted |
|---|---|---|
| `refresh_ctrl` | `MAINT_REF` | issue `REF` or LPDDR4 per-bank refresh |
| `zq_ctrl` | `MAINT_ZQ` | issue `ZQCS`, `ZQCL`, or LPDDR4 MPC ZQ calibration |
| `odt_ctrl` | `MAINT_ODT` | issue the ODT turnaround command or NOP-with-ODT |

The rule is inherited from scoria: request and wait, never preempt. A maintenance source raises `req` and holds it until `grant` arrives. It cannot yank the bus away from an in-flight host command.

### LPDDR4 degeneration

LPDDR4 has no bank groups, so `NUM_BANK_GROUPS = 1` and `group(cmd)` is always zero. The same-group and cross-group checks collapse into a single check per pair because there is only one group to compare against. The L/S counters still exist, but they are loaded with the same value. This must fall out of the parameterization, not out of an `if (memtype == LPDDR4)` branch.

This is worth stating plainly: LPDDR4 is not a special case in the arbiter. It is the `NUM_BANK_GROUPS = 1` corner of the same code.

## FSM policy

The arbiter is priority logic plus CAMs, not an FSM. That is inherited from scoria. The scheduler's grant sequencing — one command per cycle, maintenance highest, FR-FCFS among host commands — is the same mechanism with the L/S inputs added.

The global timers are counters, not a state machine. Each timer decrements every cycle and asserts its `ok` flag at zero.

## Timing

One grant per cycle, as inherited. The new counters add combinational delay to the admission check but no new pipeline stages. The critical path is:

1. Read CAM and write CAM produce candidates.
2. Bank timers check per-bank readiness.
3. Global timers check L/S spacing against `last_cmd_group` and `outstanding_group_mask`.
4. FR-FCFS priority selects the winner.
5. Grant is registered and the command is issued.

The counter values are runtime CSRs, initialised from the JESD79-4/JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

## Notes

- **Why the tag, not special-case ports:** scoria's ZQ design ended up with one maintenance request port and a source identifier. Refresh and ODT turnarounds join the same shape. The scheduler doesn't need to know what kind of maintenance it is granting; it only needs to know that maintenance beats host traffic and that only one source wins per cycle.
- **L/S vs the old `tCCD`:** The inherited `tCCD` is kept as a fallback for modes where bank-group information is not available, but the primary check is the L/S pair. DV must prove that `tCCD_L` and `tCCD_S` subsume the old `tCCD` correctly for DDR4 and collapse to it for LPDDR4.
- **Maintenance starvation:** Because maintenance never preempts, a pathological stream of host commands could delay refresh or ZQ. The refresh controller's credit window and the ZQ controller's overdue counter handle this at the source; the scheduler's only obligation is fair arbitration once the request is raised.
