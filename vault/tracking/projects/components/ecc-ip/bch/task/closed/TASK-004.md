# TASK-004: Author the BCH math chapter for novices

**Priority:** P3
**Status:** closed 2026-10-08 — the chapter exists and is published: HAS
ch07 "Understanding the Math" with all five sections (fields/polynomials,
the code, decoding, the n/k/t/m parameters page, and the stage-by-stage
math-to-pseudocode page), worked numbers re-verified by
`ch07_math_trace.py` on 2026-10-08 (ALL CHECKS PASSED), and the chapter
carried through the publication ambiguity/voice passes.
**Owner:** TBD

The BCH documentation stack (PRD, HAS, MAS) assumes the reader already
knows finite fields and algebraic coding. It does not, and the people the
repo exists for (folks learning hardware design through practice) keep
hitting the same wall: "why GF?", "why is addition XOR?", "what IS a
syndrome?", "why doesn't BCH need a Forney stage?". This task writes the
chapter that takes them from zero to following the decoder math.

## Scope

- A math deep-dive written for a novice: no prior coding theory, no
  abstract algebra. Placement decided at execution — either a new
  introduction chapter in `docs/bch_has/ch01_introduction/` or a standalone
  primer in `docs/` linked from the HAS index; follow
  `vault/handbook/authoring/doc-placement.md` (one source per fact — do not
  restate parameter or port tables the HAS owns).
- The finite-field foundation (what a field is, GF(2), GF(2^m), polynomial
  arithmetic mod p(x), inverses) is shared with the reed-solomon component:
  write it ONCE there (reed-solomon TASK-004) and link it — this chapter
  adds the BCH-specific depth on top, not a second copy.
- BCH-specific content, in order, each step with hand-checkable numbers:
  1. Binary codes: codewords as bit polynomials, cyclic codes, why
     polynomial long division gives you parity.
  2. Minimal polynomials: why α^i's conjugates i·2^j mod 2^m−1 collapse the
     root list, and what g(x) = lcm of them looks like — worked in GF(2^4)
     (the CCSDS (63,56) generator from CCSDS 231.0-B-4 figure 3-2 as the
     fully worked example).
  3. The evenness shortcut: S_2j = S_j^2 (Freshman's dream in characteristic
     2), why only t syndromes are independent, and what that saves in
     hardware.
  4. Why no Forney stage: in a binary code every error value is 1, so
     Chien positions are just flipped — the fourth RS stage never exists.
  5. The decoder chain as detective story: odd syndromes -> key equation ->
     Chien search -> flip, each stage's input and output in plain words,
     then the math; the three D11 solver candidates explained at intuition
     level.
- Voice: patient, zero jargon without definition, every symbol introduced
  before use. The Massey 1969/1965 papers (stored in `References/`) are 6
  pages each and readable; the Guruswami-Rudra-Sudan draft chapters are the
  theory backup.
- Verify every worked number against `dv/tbclasses/bch_model.py` (or the
  `galois` package) before it lands (checkable-claims: a wrong example is
  worse than none).

## Log

**2026-10-03 -- filed**, alongside the matching reed-solomon TASK-004. The
two chapters cross-link: the finite-field foundation lives with RS, the
binary-code depth lives here.

**2026-10-08 -- closed.** One recorded deviation: the "write the foundation
once, link it" plan became two sister chapters — each component's ch07
carries its own fields/polynomials intro (the RS tree owns the `gf_*`
primitives and the BCH chapter says so inline; the math-to-pseudocode pages
cross-link each other). Same content authority, better novice continuity;
no second copy of any parameter or port table.
