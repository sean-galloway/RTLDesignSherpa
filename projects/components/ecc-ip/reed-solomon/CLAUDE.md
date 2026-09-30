# Reed-Solomon Component -- Area Facts

Read the root `CLAUDE.md` and `vault/handbook/INDEX.md` first; this file holds
only what is particular to this directory.

## State (2026-09-29)

- Stood up at Sean's request; `References/` is populated and `PRD.md` is a
  draft whose decision table is unresolved. There is NO RTL, NO DV and NO
  filelist yet. Do not create placeholder RTL, tests or a MAS skeleton.
- Tracker: `vault/Tasks/projects/components/ecc-ip/reed-solomon/` (task/bug/issue
  lanes). TASK-001 (stand-up) is active and logs what exists.

## Decisions this area is waiting on (see PRD.md section 3)

symbol width m; correctable symbols t; shortening; encoder-only vs full
decoder; erasures; throughput (symbols per cycle); the first consumer.
DECIDED: BCH is OUT -- its own component in `ecc-ip/bch/` (PRD D7, Sean
2026-09-29); keep the GF primitives general so it can reuse them. DECIDED: the key-equation solver is `KES_ALGO`-selectable, riBM
(default) or the modified Euclidean array (PRD D11, Sean 2026-09-29); only the
PE and the solver block differ, verified against one golden model. DECIDED: `SYMBOL_WIDTH` is a
top parameter, `DATA_WIDTH` must be a multiple of it, `SYMBOLS_PER_BEAT` is
derived (PRD D1, Sean 2026-09-29) -- never derive m from the bus width. DECIDED: the scrambler is behind
`ENABLE_SCRAMBLER` (PRD D12, Sean 2026-09-29). DECIDED: the deliverable is
the CORE with plain valid/ready at both ends (drops into a memory controller
or compute engine); `INTAKE_IF` / `OUTLET_IF` default `NONE` and may be
`AXIS` or `AXI4` independently for standalone use (PRD D9, Sean 2026-09-29).
It is an endpoint codec, never a mid-stream insert (PRD 4a). Until a consumer names them, nothing here should be
"designed" -- gather, compare, record.

## Conventions that already apply

- Interface: valid/ready streaming in the house style (`vault/handbook/design/valid-ready-contracts.md`),
  `aclk`/`aresetn` naming as in `rtl/amba`, reset through the `ALWAYS_FF_RST`
  macros with `RST_ASSERTED` (`vault/handbook/design/reset-and-clocking.md`).
- GF layer facts (`rtl/gf/`, 2026-09-30): combinational, no clock or reset
  port; data ports `i_*` / `ow_*` like `rtl/math`. `gf_pkg` is constant
  functions with (m, prim) as arguments -- there is NO parameterised package
  and NO generator; each module builds its own `localparam` tables. Verilator
  trips its replication limit on a `'0` fill of a 2^m x m vector at m >= 10,
  so `gf_inv` assigns every table entry instead of zero-filling. `$error`
  elaboration guards (range, primitivity) fire only in simulation; lint does
  not execute them. Lint: `make -C rtl lint-all`. Tests:
  `cd dv/tests && make clean-all && make run-all-<gate|func|full>-parallel`;
  golden model `reedsolo.gf_mult_noLUT(a, b, prim, 2**m)`, hex `PRIM_POLY`
  reaches the TB through the environment and is parsed with `int(x, 0)`
  (TBBase.convert_to_int is decimal-only).
- Encoder facts (2026-09-30): `rs_encoder_core` elaborates only at
  `SYMBOLS_PER_BEAT = 1` (an `$error` guard); the S > 1 datapath is the next
  step on it. `gf_lfsr_encoder` drains parity by shifting with zero feedback,
  so it is clear after 2t shifts and has no clear input -- do not add one. The
  golden model is `reedsolo.rs_encode_msg(data, 2t, fcr=b)`; call
  `reedsolo.init_tables(prim, 2, m)` first, and pass a `bytearray` only for
  m <= 8 (a list above). A full-length profile cannot test a block longer
  than k (the model has no room), so only shortened profiles exercise the
  long-block framing error.
- Decoder facts (2026-09-30): `dv/tbclasses/rs_model.py` is the bit-exact
  reference for every decoder block (Horner syndromes, riBM, Chien, Forney)
  on reedsolo's field arithmetic, and `python3 rs_model.py` re-proves it
  against reedsolo's decoder on six profiles -- run that before trusting a
  block test. Three facts it established: riBM's evaluator is the HIGH half
  of S*Lambda, so Forney's exponent is 1 - b - 2t (not 1 - b); the riBM
  array's top t cells are Lambda_{t+1..2t} and give the more-than-t-errors
  check for free; and degree + root-count checks still miscorrect some
  e > t blocks (seen on RS(15,11)), so the decoder core re-computes the
  syndromes of the corrected stream and reports uncorrectable if they are
  not zero -- that is what makes "never silently pass a failed block" true.
  `gf_alpha_pow` accepts negative exponents (the Chien/Forney load constants
  need them); SystemVerilog `%` keeps the sign, which is why it re-wraps.
- Decoder core facts (2026-09-30): three stages (receive, solve, correct)
  joined by `gaxi_skid_buffer` descriptor stages; the block FIFO and the
  output FIFO are `gaxi_fifo_sync` in mux mode. The output FIFO stores
  `{last, hit, correction, received}` and the block is released only when its
  status entry exists -- corrections are applied AT THE OUTPUT and skipped
  when the verdict is uncorrectable. Do not move the XOR back into the walk:
  the re-check verdict is not known until the last position, and applying
  corrections early is what emitted altered symbols on uncorrectable blocks
  in the first cut. Status is valid on every beat of the block, not only
  with `out_last`. A block reaching the FIFO depth without `in_last` is
  force-ended with frame_err (anti-deadlock). Mutation checks that must keep
  failing: invert the re-check term (12 mismatches in 20), suppress the
  correction at position 0 (seed-dependent: try two seeds).
- Euclid solver facts (2026-09-30): `key_equation_solver_euclid` keeps R, Q,
  lam~, mu~ TOP-ALIGNED and "multiply by x" moves coefficients UP one index
  (the model's first cut shifted the wrong way and terminated in 9 cycles
  on every block -- if Euclid ever "always finishes early", check the shift
  direction first). Its Omega is the textbook one, so `forney_evaluator`
  needs `OMEGA_HIGH_HALF = 0` with it; the core derives that from
  `KES_ALGO`. The string parameter reaches Verilator as `-GKES_ALGO="EUCLID"`
  (the runner passes `'"EUCLID"'` with the quotes) and the TB gets the same
  choice through the `KES_ALGO` environment variable, because cocotb cannot
  read a string parameter back from the DUT.
- Filelists in `rtl/filelists/` and registered in `bin/filelists.toml` from
  the first module (`vault/handbook/design/filelists.md`).
- DV: cocotb under `dv/tests/` with TB classes in `dv/tbclasses/` (Pattern B,
  `cocotb_test_*` prefixes). Golden model: `reedsolo` (MIT) or `galois` (MIT)
  from PyPI, driven through the same encode/decode calls the RTL sees -- never
  a hand-rolled GF table in the test.
- Docs: the HAS is `docs/reed_solomon_has/` (index + `ch00`..`ch06`, styles
  YAML, mermaid sources under `assets/mermaid/`), built by
  `docs/generate_has_pdf.sh` (flags as bridge's; `REPO_ROOT` is five levels
  up because the component sits under `ecc-ip/`). Every Markdown link in the
  index is inlined by the build, so companions are listed there as plain
  paths. A MAS under `docs/reed_solomon_mas/` follows when there is a design
  to describe.

## Reuse survey pointers

- `rtl/common/dataint_ecc_*` -- the house ECC (Hamming SECDED) interface shape.
- `rtl/common/math_*` -- adders and multiplier trees; GF(2^m) multipliers are
  NOT there and are the first new primitive.
- `References/README.md` lists open-source RS RTL (freecores RS(204,188),
  wyvernSemi eccExamples, ...) for comparison; licences differ (GPL among
  them) -- read before borrowing structure, never copy code.
