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

# ODT Control (absorbed — no standalone block)

> ## ABSORBED — No standalone FUB
>
> There is **no `odt_ctrl` module** in the live RTL. The dedicated ODT-control
> FUB the original architecture planned was never built as a separate block. ODT
> responsibility is split between two modules that already exist:
>
> - **`dfi_cmd_formatter.sv`** (see [the command-formatter chapter](14_cmd_encoder.md))
>   owns the `dfi_odt_o` output. ODT follows deterministically from the issued
>   command, so it belongs on the same output stage as the ras/cas/we truth table
>   rather than in a separate FSM.
> - **`mode_register.sv`** decodes the DDR2 ODT rule bits from the mode registers
>   into an `odt_o` field (see [the mode-register chapter](20_mode_register.md)).
>
> This chapter is retained only to explain where ODT lives and to record the
> current (minimal) state honestly.

**Status:** Absorbed / minimal — ODT is decoded but not yet actively driven

---

## Where ODT Lives Today

| Concern                          | Live location                    | State                                  |
|----------------------------------|----------------------------------|----------------------------------------|
| `dfi_odt_o` bus (per-rank, per-phase) | `dfi_cmd_formatter.sv` output | Driven to 0 in v1 (decode leaves `w_p0_odt` at the NOP default for every op) |
| `dfi_odt_o` reset value          | `dfi_signal_pack.sv`             | 0 (ODT off during reset / before init) |
| DDR2 ODT-rule decode from MRs     | `mode_register.sv` `odt_o[1:0]`  | Decoded from MR1 (`{w_mr1[6], w_mr1[2]}`); informational, not wired to the pin driver |
| LPDDR2 ODT                        | `mode_register.sv`               | `odt_o = 0` (LPDDR2 typically point-to-point) |

`mode_register` exposes `odt_o` as one of its live decoded outputs, but the RTL
comment marks it "informational; not used" — the value is computed from the DDR2
MR1 ODT bits but is not currently consumed to time a termination window.
`dfi_cmd_formatter` drives `dfi_odt_o` from `w_p0_odt`, which the DDR2 decode
never raises above its NOP default, so on the DDR2/LPDDR2 board targets (both
effectively single-rank point-to-point) ODT stays off.

---

## Why ODT Is Off on the Board Target

ODT is a JEDEC impedance-matching feature: a DDR2 device contains internal
termination resistors that the controller selectively enables to terminate the
DQ/DQS bus. The rule is asymmetric and only matters with more than one device on
the bus:

- **During a read**, the accessed rank drives DQ; *other* ranks should terminate.
- **During a write**, the controller drives DQ; the *target* rank should
  terminate.

For a single-rank point-to-point system there is nothing else on the bus, so ODT
serves no purpose and 0 is correct. The pumice board bring-up (Nexys A7, single
x16 DDR2 device) is exactly this case — which is why the v1 controller ships with
ODT decoded-but-not-driven and passes on silicon.

---

## What a Full ODT Implementation Would Add

If a multi-rank DDR2 target is brought up, the timed ODT window would be added
inside `dfi_cmd_formatter`'s output stage (not as a new block), consuming
`mode_register.odt_o` plus CL/CWL and burst length to compute per-rank turn-on/
turn-off. The JEDEC cross-termination pattern (ODT-high on the non-accessed rank
during a read, on the accessed rank during a write) would drive `w_p0_odt` per
target rank instead of the current constant 0. Because the rule follows
deterministically from the issued op and the MR-decoded termination value, it
stays in the formatter's truth table — the reason the standalone block was never
needed.

---

## Verification Notes (cocotb test plan)

| Scenario                                                        | What it proves                          |
|-----------------------------------------------------------------|-----------------------------------------|
| Single-rank DDR2: `dfi_odt_o` stays 0 for all traffic           | Current behavior (point-to-point board target) |
| Reset: `dfi_signal_pack` drives `dfi_odt_o = 0`                 | Reset-safe ODT-off                      |
| `mode_register` MR1 ODT bits decode into `odt_o`                | Decode present for future use            |
| LPDDR2: `mode_register.odt_o = 0`                               | No ODT on LPDDR2 point-to-point          |

---

## Open Questions / Future Work

- **Timed ODT window (multi-rank DDR2).** Not implemented. Would live in
  `dfi_cmd_formatter`'s output stage, driven by `mode_register.odt_o` + CL/CWL +
  BL. Add when a multi-rank DDR2 board is targeted.
- **Dynamic ODT (DDR3+).** DDR3 introduced Rtt_Wr vs Rtt_Nom; DDR2/LPDDR2 have
  only Rtt_Nom. A DDR3+ family controller would extend the decode.
- **ODT during refresh/precharge.** Some boards want ODT held during refresh to
  avoid a floating bus. Revisit only if signal-integrity characterization flags
  it on a multi-rank target.
