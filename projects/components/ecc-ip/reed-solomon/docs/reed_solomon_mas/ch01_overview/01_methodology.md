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

# Methodology

## HAS to MAS relationship

The Hardware Architecture Specification (`../reed_solomon_has/`) records what
the RS codec is, where it sits, what it presents at its boundaries, and what
parameters configure it. This Micro-Architecture Specification carries that
architecture one level down: per-block signal tables, cycle behavior, FSM
policy, and the verification references a checker needs.

The rule in this repo is one source per fact. The MAS does not restate the
PRD decision table or the HAS block diagram; it cross-references them and adds
the implementation detail that belongs at this level. Parameters that remain
open are marked **TBD** and tied to the PRD decision ID that fixes them,
following the convention in
`../reed_solomon_has/ch06_integration/02_parameters.md`.

## Retroactive posture: the RTL is the ground truth

The BCH MAS was written before its RTL existed; its signal contracts cite MAS
pages with the promise to re-point them at `.sv` lines later. This MAS is
written retroactively, after the RS RTL landed and its gate DV went green, so
it takes the other posture from the start:

- every block page cites the `.sv` file it documents, and expressions in the
  text mirror the RTL rather than an intent the RTL must catch up to
- where the pre-RTL FUB catalog (`docs/rs_fub_catalog.md`) predicted a
  different decomposition — it planned an `erasure_locator` leaf, a
  `symbol_unpack`/`symbol_pack` pair, and a separate `parity_mux`; the landed
  tree routes those jobs differently — the block page says what actually
  happened and the inventory (chapter 1.2) collects the drift
- nothing here invents a numeric value; measured cycle counts come from the
  gate logs cited on the block pages

## FSM policy

The repo's datapath FSM rule, taken from the design handbook, is:

> **No FSM in the per-beat data path. Not a minimal one, not a two-state one.**
> FSMs belong to control: descriptor lifecycle, schedulers, init sequencers,
> error recovery. If a state machine can observe a data beat, it is in the
> wrong place.
> — `vault/handbook/design/streaming-no-fsm.md`

What replaces a datapath FSM in this block:

| Instead of a state that... | Write |
|---|---|
| counts beats, or waits N cycles | a counter plus a comparator |
| remembers "I am mid-burst" | a `r_valid` flag on the pipeline stage |
| serializes because a resource is shared | an arbiter and a qualifier, not a turn-taking machine |
| gates until a condition holds | a qualifier ANDed into the handshake |

Where a state machine is genuinely justified, the handbook requires:

> Fewest states that carry the real distinctions. A state that only waits one
> fixed cycle, or that differs from a sibling only by a datapath value, is a
> register, not a state. Merge states whose outputs and successors are
> identical. Idiom: `typedef enum logic [N-1:0] {...} state_t;` + two-process
> form - registered `r_state`, combinational `w_next_state` with a default-hold
> first line and a default arm. One FSM per module; nested/communicating FSMs
> are a smell that the block wants splitting. Outputs: prefer registered
> (Moore) at module boundaries; combinational decode of `r_state` internally is
> fine but belongs in the K-maps.
> — `vault/handbook/design/minimal-fsm.md`

Every block page in chapter 2 states its FSM policy explicitly and cites this
page. Most blocks are pure datapath and carry no FSM; the control FSMs that do
exist — the Euclid solver's iterate/normalise/swap loop and the standalone
tops' job engines — are documented with their state enumerations.

## Verification posture

Three layers, all live today:

1. **Golden-model equivalence.** Every block is bit-exact against
   `dv/tbclasses/rs_model.py`, which is itself validated against the
   `reedsolo` (and `galois`) packages — never a hand-rolled GF table in the
   test.
2. **Dual-solver cross-check.** `KES_ALGO` = `"RIBM"` (default) or
   `"EUCLID"`; both solvers decode the same injected stream and must produce
   identical Chien root sets and identical Forney values for every corrected
   block (`error_injector` feeds both, per `CLAUDE.md`).
3. **Contract discipline.** The repo's machine-checkable contract methodology
   (`vault/handbook/design/signal-contracts-and-kmaps.md`) has no generated
   workbook for RS yet; chapter 4 states what the contracts are, where they
   live in the RTL, and what generating a workbook would take. The BCH
   component's generator (`projects/components/ecc-ip/bch/docs/gen_bch_signal_contracts_kmaps.py`)
   is the pattern.

## Carrying open PRD decisions

Every undecided item in the PRD is carried as **TBD** with the decision ID
that resolves it. As of this revision:

| Parameter / choice | PRD decision | Where it lands in the RTL |
|---|---|---|
| erasure support (`ENABLE_ERASURES`) | D5 | `rs_erasure_unit`, generated only when enabled; default 0 leaves it out of the tree |
| first root / dual basis (`FIRST_ROOT`, `DUAL_BASIS`) | D8 | `gf_pkg` generator construction; defaults b = 0, no dual basis |
| encoder-only vs both cores | D4 | both cores built; a consumer instantiates what it needs |
| first consumer | D10 | none of the above changes until one appears |

Everything else — m, t, n (D1-D3), throughput architecture (D6), interface
mix (D9), the solver default (D11), the scrambler (D12) — is decided and
stated as fact on the block pages.

No numeric value is invented. Cycle-count formulas are stated in terms of the
parameters (for example, `n/S` cycles to absorb a block), and measured numbers
cite the gate log that produced them.
