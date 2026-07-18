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

# Page Policy (inline in `pumice_cmd_arbiter`)

**Live location:** `rtl/fub/pumice_cmd_arbiter.sv` (inline decision)
**Standalone module:** `rtl/fub/page_predictor.sv` — present but **not in the default build**
**Category:** FUB behaviour (arbiter-embedded)
**Parent:** `pumice_mem_cmd_scheduler`
**Status:** Inline OPEN/CLOSE decision implemented; HAPPY_HYBRID hook is a TODO

> **Rearchitected:** the SWAG planned a per-(rank, bank) HAPPY hybrid predictor
> as a distinct scheduler FUB feeding a `predict_open` / `predict_hit` hint into
> the scheduler's auto-precharge stage. In the live build there is **no
> standalone predictor instantiated** — the open-page vs auto-precharge decision
> is made **inline** in [`pumice_cmd_arbiter`](07_scheduler.md) from the
> `page_policy_i` CSR field. A `page_predictor.sv` file still exists in the repo
> (a 2-bit saturating counter, optional/reference) but is not wired into
> `pumice_mem_cmd_scheduler` or `pumice_core`; confirm against the filelists in
> `rtl/filelists/`.

---

## The live decision

The arbiter computes a single auto-precharge bit directly from the page policy:

```systemverilog
// pumice_cmd_arbiter.sv
logic w_ap;
assign w_ap = (page_policy_i == PAGE_POLICY_CLOSE);
```

and applies it to every column op it picks:

| `page_policy_i`        | Column op emitted | Effect                                          |
|------------------------|-------------------|-------------------------------------------------|
| `PAGE_POLICY_OPEN`     | `OP_RD` / `OP_WR`  | Rows stay open; the arbiter row-hit-schedules subsequent column ops to the open row |
| `PAGE_POLICY_CLOSE`    | `OP_RDA` / `OP_WRA`| Every column op auto-precharges (`w_ap_out = 1`) |
| `PAGE_POLICY_HAPPY_HYBRID` | (treated as OPEN in v1) | Predictor hook is a TODO; behaves as OPEN   |

`evt_ap_o` is driven from `w_ap_out`, which tells `pumice_bank_timers` to model
the auto-precharge (transition the bank toward precharged after the column op)
rather than leaving the row active. There is no per-bank hint, no saturating
counter, and no `HAPPY_HYBRID`-specific RTL in the live path — HAPPY currently
falls through to the OPEN branch.

`page_policy_i` originates at `pumice_top` from
`hwif_out.REFRESH_TUNING.page_policy_or` (see [ch02/01](01_top_integration.md)),
so page policy is a **runtime CSR** setting, not a build parameter.

## Why inline

Open-page management in this controller is not a prediction problem: the arbiter
already scans, every cycle, which banks have an open row (`bank_row_active_i` /
`bank_open_row_i`) and which pending CAM entries are a row hit to that open row
(the per-bank CAM lookups). Given that live row-hit visibility, the only remaining
choice is the static "leave open vs auto-precharge" policy bit, which is exactly
what the inline `w_ap` expresses. A separate predictor structure — a table, a
warmup counter, per-entry hysteresis, an outcome-training broadcast — would add
significant state for a marginal gain over the CSR-selected OPEN/CLOSE policy,
and none of that is in the shipping build.

## The retained `page_predictor.sv` file

For reference, the file that remains in the repo implements a per-(rank, bank)
**2-bit saturating "predict open" hint**:

| Counter | Meaning           |
|---------|-------------------|
| `00`    | strongly closed   |
| `01`    | weakly closed     |
| `10`    | weakly open       |
| `11`    | strongly open     |

It updates on the `evt_act_i` strobe: the first ACT on a bank records the row with
no update; a subsequent ACT to the same row saturates the counter up, a different
row saturates it down. `predict_open_o[r][b]` is the counter MSB, all
strict-flopped. This matches the module header and the two `ALWAYS_FF_RST` blocks
in `page_predictor.sv`.

If HAPPY_HYBRID is promoted from TODO to a real path, this module is the intended
building block: the arbiter would consult `predict_open_o[rank][bank]` to choose
`OP_RD/WR` (predict open) vs `OP_RDA/WRA` (predict closed) when `page_policy_i ==
PAGE_POLICY_HAPPY_HYBRID`, replacing the current OPEN fall-through. Until then it
is not instantiated.

## Notes / flags

- The elaborate SWAG predictor (4 K-entry hashed table, BRAM storage, warmup
  counter, per-entry hysteresis, outcome-training broadcast, accuracy telemetry,
  `PAGE_PREDICTOR_TABLE_BITS` / `HYSTERESIS_BITS` params) does **not** exist in
  any live RTL — that was SWAG only.
- The `page_predictor.sv` that *does* exist is the simpler per-bank 2-bit counter
  documented above; treat it as optional/reference, gated by the filelists.
- `powerdown_ctrl.sv` is likewise present-but-optional and not in the default top
  build.
