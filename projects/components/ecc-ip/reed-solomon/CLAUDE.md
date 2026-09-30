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
