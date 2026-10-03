# BCH Component -- Session Notes

Area facts for a session working in `projects/components/ecc-ip/bch/`.
Grown from the reed-solomon component's `CLAUDE.md`; extend this file as the
component grows, and keep it true -- a stale CLAUDE.md is worse than none.

## Status

Stood up 2026-10-03: references gathered (`References/`, six stored PDFs with
sources and licences), PRD at v0.1 draft (every design decision open except
the three carried over from the RS PRD: shared GF layer D7, valid/ready core
direction D9, deferred consumer D10). Same day the doc stack landed (HAS
v0.1, MAS v0.1, signal-contract workbook — TASK-002 closed, TASK-003 open
until the contracts re-point at RTL lines) and the full codec with gate DV
(TASK-001 umbrella for the encoder half, TASK-005 for the decoder):
`bch_pkg`; fubs `bch_syndrome_unit`, `bch_key_equation_solver` (RIBM via the
imported RS riBM; `KES_ALGO` guards the unimplemented candidates), and
`bch_chien_search`; macros `bch_encoder_core` and `bch_decoder_core`
(six-state sequencer, ENABLE_RECHECK second-syndrome re-check, release-on-
verdict the way `rs_decoder_core` does it). Gate-green on the three standing
profiles — CCSDS (63,56) t=1 b=0, flash-class shortened (4224,4120) t=8
m=13, narrow-sense (63,51) t=2. Known decoder-core corner: a block longer
than N_BITS deadlocks the input (named in the RTL header); inter-block
pipelining stays open under PRD D6.

## Hard rules carried from the component's PRD and the repo

- The GF(2^m) primitives (`gf_pkg`, `gf_mul`, `gf_mul_const`, `gf_inv`,
  `gf_syndrome_cell`) live
  in `projects/components/ecc-ip/reed-solomon/rtl/fub/gf/` and are IMPORTED, never
  copied (RS PRD D7). The whole-block imports extend to the RS riBM solver
  array (`reed-solomon/rtl/fub/key_equation_solver_ribm.sv`, instantiated by
  the BCH KES) — nothing BCH-specific ever moves into the RS tree.
  BCH-specific logic -- binary syndromes, the evenness shortcut S_2j = S_j^2,
  bit-level Chien/flip -- lives only in this tree.
- No Forney stage exists in a binary decoder: error values are all 1. If you
  find yourself computing error magnitudes, the architecture has drifted into
  RS territory.
- No assertions in RTL; properties go in `formal/` blocks
  (`vault/handbook/design/`).
- Reuse survey before new RTL; GPL code is read for structure and never
  copied into this MIT-licensed repo.
- DV golden model: `dv/tbclasses/bch_model.py` (on `galois`, validated
  against `galois.BCH` — re-prove with `python3 bch_model.py` before trusting
  a block test, the way `rs_model.py` works for RS); AFF3CT is the
  cross-check named in the PRD.

## Layout

| Path | What |
|---|---|
| `PRD.md` | the decisions table (D1-D12); it is the source of truth for what is decided vs open |
| `References/README.md` | papers/standards catalog with reading order |
| `docs/` | the HAS (`bch_has/`) and MAS (`bch_mas/`) trees + the signal-contract workbook generator |
| `rtl/fub/` | `bch_pkg` (constants, generator polynomial, syndrome roots), `bch_syndrome_unit`, `bch_key_equation_solver`, `bch_chien_search` |
| `rtl/macro/` | `bch_encoder_core`, `bch_decoder_core` |
| `dv/tbclasses/` | `bch_model.py` golden model + per-block TB classes |
| `dv/tests/` | cocotb test runners per block (`make run-all-gate-parallel` from here) |

## House conventions this component follows

- Streaming interface: the house valid/ready contract; `in_last` /
  `out_last` mark the block boundary; the decoder verdict is a per-block
  sideband (`out_status`), valid with `out_last`.
- Parameters are elaboration-time unless a decision says otherwise (RS D2
  precedent): no run-time t, no run-time m.
- A parameter's OFF state gets its own test, never an assumption.
- The task tracker mirrors this path: `vault/Tasks/projects/components/ecc-ip/bch/`.
- Running the DV (2026-10-03, hard-won): the repo venv AND the simulator
  choice are both required — `export PATH="$REPO_ROOT/venv/bin:$PATH"` and
  `export SIM=verilator`. The icarus path is broken on this machine
  (oss-cad-suite's libm vs the system libpython GLIBC). `dv/tests/fub/conftest.py`
  wires `bin/` (TBClasses) and the component `dv/` onto `sys.path`; without
  it pytest dies at import. A killed run leaves `.sim_busy` markers — clear
  with `python3 bin/sim_build_clean.py projects/components/ecc-ip/bch/dv/tests/fub`,
  never `rm -rf` (VAL-XDIST-INTERMITTENT, see the tool's docstring). And
  cocotb_test does NOT rebuild when RTL sources change — a bare pytest rerun
  executes the stale sim binary; after any RTL edit, clean the config's build
  dir first (the house `make clean-all && make run-all-...` exists for
  exactly this). Two encoder bugs hid behind that one: a gen-poly built from
  one factor per coset instead of per conjugate (bch_pkg, caught only
  because the encoder test finally ran), and an ALWCOMBORDER that lint's
  `-Wno-fatal` never flags.
- Filelists live in `rtl/filelists/` and the area is registered in
  `bin/filelists.toml` (registered 2026-10-03, the RS from-the-first-module
  posture); `python3 bin/filelist_registry.py --check` must stay green.
- The kmap workbook regenerates with
  `PYTHONPATH=bin python3 docs/gen_bch_signal_contracts_kmaps.py`
  (the `bin/` on PYTHONPATH is the invocation, matching the stream
  component's generator).
