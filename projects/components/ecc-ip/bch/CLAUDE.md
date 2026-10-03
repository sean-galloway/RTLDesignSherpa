# BCH Component -- Session Notes

Area facts for a session working in `projects/components/ecc-ip/bch/`.
Grown from the reed-solomon component's `CLAUDE.md`; extend this file as the
component grows, and keep it true -- a stale CLAUDE.md is worse than none.

## Status

Stood up 2026-10-03: references gathered (`References/`, six stored PDFs with
sources and licences), PRD at v0.1 draft (every design decision open except
the two carried over from the RS PRD: shared GF layer D7, valid/ready core
direction D9, deferred consumer D10). **No RTL, no DV, no docs tree yet.**

## Hard rules carried from the component's PRD and the repo

- The GF(2^m) primitives (`gf_pkg`, `gf_mul`, `gf_mul_const`, `gf_inv`) live
  in `projects/components/ecc-ip/reed-solomon/rtl/gf/` and are IMPORTED, never
  copied (RS PRD D7). BCH-specific logic -- binary syndromes, the evenness
  shortcut S_2j = S_j^2, bit-level Chien/flip -- lives only in this tree.
- No Forney stage exists in a binary decoder: error values are all 1. If you
  find yourself computing error magnitudes, the architecture has drifted into
  RS territory.
- No assertions in RTL; properties go in `formal/` blocks
  (`vault/handbook/design/`).
- Reuse survey before new RTL; GPL code is read for structure and never
  copied into this MIT-licensed repo.
- DV golden model: `galois` (Python) is the first candidate (`reedsolo` is
  RS-only); AFF3CT is the cross-check.

## Layout

| Path | What |
|---|---|
| `PRD.md` | the decisions table (D1-D12); it is the source of truth for what is decided vs open |
| `References/README.md` | papers/standards catalog with reading order |
| `docs/` | appears with the HAS; mirror the reed-solomon `docs/reed_solomon_has/` structure |

## House conventions this component follows

- Streaming interface: the house valid/ready contract; `in_last` /
  `out_last` mark the block boundary; the decoder verdict is a per-block
  sideband (`out_status`), valid with `out_last`.
- Parameters are elaboration-time unless a decision says otherwise (RS D2
  precedent): no run-time t, no run-time m.
- A parameter's OFF state gets its own test, never an assumption.
- The task tracker mirrors this path: `vault/Tasks/projects/components/ecc-ip/bch/`.
