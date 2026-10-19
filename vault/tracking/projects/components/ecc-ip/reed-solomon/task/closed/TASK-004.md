# TASK-004: Author the RS math chapter for novices

**Priority:** P3
**Status:** closed 2026-10-08
**Owner:** TBD

The RS documentation stack (PRD, HAS, MAS, FUB catalog) assumes the reader
already knows finite fields and algebraic coding. It does not, and the
people the repo exists for (folks learning hardware design through
practice) keep hitting the wall: "why GF(2^m)?", "why is addition XOR?",
"what IS a syndrome?". This task writes the chapter that takes them from
zero to following the decoder math.

## Scope

- A math deep-dive written for a novice: no prior coding theory, no
  abstract algebra. Placement decided at execution — either a new
  introduction chapter in `docs/reed_solomon_has/ch01_introduction/` or a
  standalone primer in `docs/` linked from the HAS index; follow
  `vault/handbook/authoring/doc-placement.md` (one source per fact — do not
  restate parameter or port tables that the HAS owns).
- Content, in order, each step with hand-checkable numbers:
  1. What an error-correcting code is and why blocks (the k/n/t picture,
     intuition for 2t parity symbols).
  2. Fields, from the integers mod a prime to GF(2) to GF(2^m): what makes
     a number system closed and invertible, why the code math needs that.
  3. Polynomial arithmetic mod p(x): addition is XOR, multiplication
     wraps, every nonzero element has an inverse. Worked tables in GF(2^4)
     (small enough to check by hand).
  4. What a codeword is here: g(x), systematic encoding, the LFSR picture
     the RTL actually implements.
  5. Syndromes: why evaluating the received word at the generator roots
     detects errors, and why exactly 2t of them.
  6. The decoder chain as detective story: syndromes -> key equation ->
     Chien search -> Forney, each stage's input and output in plain words,
     then the math.
  7. Why GF and not integers (carries, wrap-around, the Wallace/Dadda
     irrelevance) — the two questions every newcomer asks.
- Voice: patient, zero jargon without definition, every symbol introduced
  before use. The stored BBC WHP031 paper already does worked RS(255,239) /
  RS(204,188) numbers — point there rather than duplicating; the NASA
  tutorial's RS(15,9) walkthrough is the model for pacing.
- Verify every worked number against `dv/tbclasses/rs_model.py` or the
  `galois` package before it lands (checkable-claims: a wrong example is
  worse than none).

## Log

**2026-10-03 -- filed**, alongside the matching bch TASK-004 (same chapter
for the binary codec; the two must cross-link and share the finite-field
foundation rather than restate it).
**2026-10-08 -- closed.** Landed as HAS ch07 `understanding_the_math` with
all five sections, including the later-requested n/k/t/m parameter
treatment and every-stage math-to-pseudocode. `ch07_math_trace.py`
verifies every worked number against the component model: ALL CHECKS
PASSED (GF(2^4) tables, RS(255,239) and RS(252,236) profile checks,
correction round-trip, post-correction syndromes zero). BCH's sister
chapter (bch TASK-004, closed same day) cross-links here for the shared
foundation.
