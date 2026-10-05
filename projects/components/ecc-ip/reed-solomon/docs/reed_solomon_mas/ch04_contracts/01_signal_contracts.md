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

# Signal Contracts and Golden Model

## What a contract is

A signal contract in this repo is a machine-checkable statement of what a
signal is allowed to do. Each contract has three parts, in order:

1. **Term list:** every signal or expression in play, with its defining
   expression and `file:line` citation.
2. **Invariants:** the strict relationships between terms, each cited, each
   stating which rows of the decision table it renders impossible.
3. **Decision table:** one row per combination of the terms. Rows the
   invariants forbid are marked `ILLEGAL`; legal rows carry the resulting
   output.

The canonical methodology is in `vault/handbook/design/signal-contracts-and-kmaps.md`;
the shared generator machinery is in `bin/kmaps/`.

## Which signals carry the contracts

The landed RTL concentrates the non-obvious control and qualifier decisions in
the decoder core, the solver interface, and the erasure unit. The contracts
for these areas are cited directly against the `.sv` source today.

| Contract area | Signals | RTL citation |
|---|---|---|
| Stage A boundary / frame error | `w_in_count`, `w_force_end`, `w_block_end`, `w_len`, `w_frame_err` | `rs_decoder_core.sv:228-232` |
| A->B descriptor valid | `w_dab_wr_valid`, `w_dab_wr_data` | `rs_decoder_core.sv:271-276` |
| Syndrome all-zero / frame-error bypass | `w_b_all_zero`, `w_b_frame_err`, `w_b_bypass` | `rs_decoder_core.sv:322-324`, `421` |
| Erasure mux into solver | `w_kes_synd` | `rs_decoder_core.sv:338-339` |
| Solver start and handshake | `w_kes_start`, `w_kes_done`, `w_kes_busy`, `w_kes_deg_err` | `rs_decoder_core.sv:330`, `443-446`; `key_equation_solver_ribm.sv:84-89`; `key_equation_solver_euclid.sv:94-99` |
| Solve-bypass bad verdict | `w_b_bad` (errors-only), `w_b_bad_final` (erasures) | `rs_decoder_core.sv:432`, `498-506` |
| B->C descriptor valid | `w_dbc_wr_valid`, `w_dbc_wr_data` | `rs_decoder_core.sv:449-458`, `514-535` |
| Final uncorrectable verdict | `w_uncorrectable_final` | `rs_decoder_core.sv:624`, `790-794` |
| Status hold / output pack | `r_st_data`, `out_status_ok`, `out_status_corrected`, `out_status_uncorrectable`, `out_status_frame_err` | `rs_decoder_core.sv:658`, `836-839`, `926-927` |
| Erasure unit transforms | `o_trans_done`, `o_comb_done`, `o_f_over`, `o_t_zero`, `o_kes_synd`, `o_lambda_c`, `o_omega_c`, `o_deg_c` | `rs_erasure_unit.sv:104-117`, `245-247` |

: Table 4.1: Contract areas in the landed RTL

## Citation posture

The RTL has already landed, so the contracts cite `.sv` file and line today;
no re-pointing is needed. There is no generated workbook for RS yet (unlike
BCH's `bch_signal_contracts.xlsx` produced by
`projects/components/ecc-ip/bch/docs/gen_bch_signal_contracts_kmaps.py`).
The natural follow-up is to clone that generator: the expressions are
concentrated and cited in Table 4.1, the shared machinery lives in `bin/kmaps/`,
and the BCH generator is the working pattern to adapt.

## The golden-model contract

`dv/tbclasses/rs_model.py` is the bit-exact reference for every decoder block.
It mirrors the RTL algorithms step for step (Horner syndromes in transmission
order, the riBM key-equation solver, Chien search from the first transmitted
position, Forney evaluation with first root `b`), and it is validated against
the `reedsolo` package before any RTL is scored against it. The area rule is
explicit: field arithmetic comes from `reedsolo` or `galois`, never a
hand-rolled GF table in a test (`CLAUDE.md`, `README.md`).

Two additional equivalence checks are part of the contract:

- **Dual-solver equivalence.** The decoder core is built with `KES_ALGO`
  selectable between `"RIBM"` and `"EUCLID"`. The Nexys A7 loop harness runs
  both solvers on the same injected stream and compares their Chien roots and
  Forney values per block; the measured result is bit-identical corrected
  output and identical verdicts across the error range (`CLAUDE.md`).
- **Erasures path.** With `ERASURE_SUPPORT = 1` the error injector can mark
  per-lane erasures through `INJ_CFG.mark` (PRD D5, TASK-002). The erasure unit
  transforms the syndromes, drives the solver window, and combines the erasure
  locator with the error locator so the Chien/Forney walk operates on the
  combined polynomial (`rs_decoder_core.sv:362-408`, `rs_erasure_unit.sv`).

## Where formal verification stands

No formal verification directory or `.sby` files exist under
`projects/components/ecc-ip/reed-solomon/` today. Coverage is by directed and
randomized cocotb tests against `rs_model.py`; formal contracts and SVA
assertions have not been added yet.
