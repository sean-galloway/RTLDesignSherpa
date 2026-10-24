# TASK-015: Evaluate matrix arbiters vs round-robin for small port counts

**Priority:** P3
**Status:** CLOSED 2026-10-24 (matrix policy shipped; measured on ASAP7; `rr` stays the default)
**Owner:** bridge
**Filed:** 2026-10-11 from the interconnect-literature deep review (bridge citations commit e0be98508)

## Motivation

The generated slave-side arbiters are round-robin (`crossbar_generator.py:608`,
grant locked through handshake). Dally & Towles, ch17 §18.5 describe the
matrix arbiter as their preferred choice for small arbiters: fast, cheap,
strongly fair, and often better timing than pointer-based RR encoders — the
relevant comparison for Bridge's typical 2–8 master port counts.

## What to do

1. Implement a matrix-arbiter variant behind the existing `arbitration`
   TOML knob (e.g. `arbitration = 'matrix'`), mirroring how `'qos'` was added.
2. Evaluate on a 2x2 and 4x4 config: timing (generated critical path),
   area, and fairness behavior vs `'rr'` under the TASK-014 traffic patterns.
3. Adopt as default only if it wins on timing without a fairness regression;
   otherwise keep `'rr'` default and document the measurement.

## Done when

- [x] `arbitration = 'matrix'` generates and passes the bridge FULL regression
- [x] timing/area/fairness comparison recorded in HAS ch05
- [x] default policy decision recorded in the PRD

## References

- `projects/components/fabric-gen-ip/bridge/references/README.md` (Dally &
  Towles ch17)

## Done (2026-10-24)

- `arbitration = "matrix"` in `crossbar_generator._generate_arbiter` beside
  `rr` and `qos`: one "i outranks j" flop per master pair (upper triangle),
  the requester outranking every other requester wins (a two-level pick, no
  pointer, no rotation mux), the winner drops below everyone at the slave-side
  handshake. Same lock-until-handshake wrapper. Validation in
  `config_loader`, `config.py`, GENERATOR_ARCHITECTURE. Regenerating every
  bridge left all 52 existing fixtures byte-identical.
- Fixtures `bridge_2x2_rw_matrix` and `bridge_4x4_rw_matrix` (batch manifest,
  generated tests and TBs). Generated tests 9/9 at FULL on both. Lint matches
  the rr baseline.
- Fairness: `test_bridge_{2x2,4x4}_rw_matrix_arb.py` with the shared
  `dv/tbclasses/bridge_arb_fairness.py` (grant order read off the slave
  port's AWID top bits, inside the contended window, against a slave that
  takes one AW per 13 cycles). 2x2: shares 0.50 / 0.50, worst wait 1 foreign
  grant, 1.000 W beats per cycle. 4x4 three-way on the 32-bit periph port
  (64-, 32- and 256-bit masters): shares 0.30 / 0.35 / 0.35, worst wait 2.
  The matrix bound `n-1` holds; it equals the round-robin's.
- Timing and area on ASAP7 (the asic-trials Yosys + ABC + OpenSTA flow,
  `projects/asic-trials/timing_characterization/work/synth_module.py`,
  crossbar module flattened, TT): at 4x4 the matrix arbiter takes 68 ps (11
  percent) off the worst register-to-register path at a 1000 ps target and 27
  ps (5 percent) at 400 ps, for +2.3 / -2.5 percent cells; at 2x2 the two are
  within 5 percent either way (one priority bit each -- mapper noise). QoS:
  821 ps on the same 2x2. Tables in HAS 5.3 and MAS 2.4. The FPGA
  out-of-context pair (Kintex-7 325T, 100 MHz) runs in `fpga/` and lands in
  HAS 5.3 when done.
- Decision (PRD FR-6): `rr` stays the default. The win is real only at four
  or more masters, every board build is tuned to round-robin timing, and the
  FPGA number was not in hand. `matrix` is the documented choice for a wide
  fabric on an ASIC target.
- Not covered: the per-master response arbiters and the shared-CDC-slave
  arbiter (`bridge_cdc_slave_arb.sv`, already `arbiter_matrix`).
