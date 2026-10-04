# TASK-005: Implement the BCH decoder stages (KES, Chien, decoder core)

**Status:** closed 2026-10-03
**Priority:** P3 — the component has no consumer yet; this completes the codec
whose encoder half landed 2026-10-03, the same posture RS TASK-002 had
**Owner:** TBD

The encoder half of the codec exists (`bch_encoder_core`, `bch_syndrome_unit`,
gate DV green). This task lands the decoder: the key-equation solver per PRD
D11, the bit-level Chien search, and the `bch_decoder_core` integration. The
MAS pages carry the per-block interfaces and FSM policy
(`docs/bch_mas/ch02_blocks/03..05`); the golden model is
`dv/tbclasses/bch_model.py` (already validated against `galois.BCH`), extended
only if a block needs a reference the model does not already provide.

## Scope

- `rtl/fub/bch_key_equation_solver.sv` — MAS table 2.5/2.6. Algorithm is PRD
  D11: `"RIBM"` lands first (the documented default when no consumer names a
  small-t profile), adapting the reed-solomon riBM per the MAS candidate table:
  the t odd syndromes expand to the full 2t sequence by the evenness shortcut
  (S_2j = S_j^2) and the imported `key_equation_solver_ribm` array runs
  unchanged — nothing BCH-specific moves into the RS tree (PRD D7). The
  `KES_ALGO` parameter exists so `"EUCLID"` / `"SMALL_T"` can land later;
  unimplemented values raise an elaboration error, they do not silently fall
  back. Interface carries the MAS ports plus the one qualifier the MAS text
  requires but its port table omits (the more-than-t / degree-error flag the
  decoder core needs for the R2 verdict); the MAS page is updated to match.
- `rtl/fub/bch_chien_search.sv` — MAS table 2.8/2.9. No FSM (streaming
  counters), no Forney stage (PRD §2: every error value is 1). Position/root
  convention is the golden model's: bit p (transmission order, p = 0 first) is
  an error position iff Lambda(alpha^-(n-1-p)) == 0 — the same cell math as the
  reed-solomon `chien_search` with the odd-sum/Forney output dropped and root
  counting added.
- `rtl/macro/bch_decoder_core.sv` — MAS table 2.10/2.11. The one minimal
  control FSM in the decoder datapath (IDLE/SYND/SOLVE/CHIEN/RELEASE per the
  MAS; wait-one-cycle states merge into their successor). Block buffer, the
  existing `bch_syndrome_unit`, KES, Chien, corrector XOR at the output, and
  the corrected-stream re-check syndrome unit that makes R2 ("never silently
  pass a failed block") true the same way `rs_decoder_core` does it.
- DV per block, model-first, mirroring the encoder/syndrome TBs:
  `dv/tbclasses/bch_key_equation_solver_tb.py` + `test_bch_key_equation_solver.py`,
  `bch_chien_search_tb.py` + `test_bch_chien_search.py`,
  `bch_decoder_core_tb.py` + `test_bch_decoder_core.py`; filelists
  (`bch_key_equation_solver.f`, `bch_chien_search.f`, `bch_decoder_core.f`)
  added to `rtl/filelists/` and into `bch_all.f`; gate level green on the
  three standing profiles (CCSDS (63,56) b=0, flash-class (4224,4120) t=8
  m=13, narrow-sense (63,51) t=2) plus the decoder-core error-count and
  beyond-t cases R4 requires.

## Definition of done

- `make -C rtl lint-all` clean for the new blocks.
- Gate suite green: every new test passes at REG_LEVEL=GATE on the standing
  profiles, including beyond-t blocks flagged uncorrectable with the received
  data passed through unchanged (R2) and corrected streams re-checked.
- `python3 bin/filelist_registry.py --check` still clean with the new filelists.
- The three MAS block pages say "landed" with the RTL paths instead of
  "target — no RTL exists", and the KES port table carries the degree-error
  qualifier.
- `python3 bin/check_task_ids.py --area projects/components/ecc-ip/bch/task` passes.

## Log

**2026-10-03 -- filed and activated**, as the recovery session picked up the
interrupted encoder/syndrome work. Decoder stages land in this session under
this task.

**2026-10-03 -- decoder stages landed and closed.** `bch_key_equation_solver`
(fub; RIBM: t odd syndromes expand to the full 2t sequence by S_2j = S_j^2,
the imported RS riBM array runs unchanged, `KES_ALGO` guards the unimplemented
candidates with an elaboration error), `bch_chien_search` (fub; the RS Chien
cell math minus the Forney path, raw root flags + running root count; the
flip-enable qualification the MAS prose described is a decoder-core output
function, documented in the MAS), and `bch_decoder_core` (macro; six-state
IDLE/SYND/SOLVE/CHIEN/RECHECK/RELEASE sequencer around the three fubs,
register block buffer, ENABLE_RECHECK second-syndrome re-check making R2 true,
release-on-verdict with corrections applied at the output exactly the way
rs_decoder_core does it). Model-first DV per block on the three standing
profiles; the core also runs the ENABLE_RECHECK=0 off-state and beyond-t
passthrough cases. Final clean gate: 16/16 configs; core also func 8/8 and
full 12/12; `make lint-all` clean (12 modules); registry check and audit
clean; MAS pages 03-05 record the landed RTL. Known limitation, named in the
RTL header: a block longer than N_BITS deadlocks the input (framing verified
for short and < N long blocks); inter-block pipelining stays open under PRD
D6.
