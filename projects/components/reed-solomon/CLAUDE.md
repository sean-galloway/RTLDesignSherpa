# Reed-Solomon Component -- Area Facts

Read the root `CLAUDE.md` and `vault/handbook/INDEX.md` first; this file holds
only what is particular to this directory.

## State (2026-09-29)

- Stood up at Sean's request; `References/` is populated and `PRD.md` is a
  draft whose decision table is unresolved. There is NO RTL, NO DV and NO
  filelist yet. Do not create placeholder RTL, tests or a MAS skeleton.
- Tracker: `vault/Tasks/projects/components/reed-solomon/` (task/bug/issue
  lanes). TASK-001 (stand-up) is active and logs what exists.

## Decisions this area is waiting on (see PRD.md section 3)

symbol width m; correctable symbols t; shortening; encoder-only vs full
decoder; erasures; throughput (symbols per cycle); BCH in scope or not;
the first consumer. Until a consumer names them, nothing here should be
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
- Docs: a MAS under `docs/reed_solomon_mas/` through the Sherpa doc pipeline
  when there is a design to describe.

## Reuse survey pointers

- `rtl/common/dataint_ecc_*` -- the house ECC (Hamming SECDED) interface shape.
- `rtl/common/math_*` -- adders and multiplier trees; GF(2^m) multipliers are
  NOT there and are the first new primitive.
- `References/README.md` lists open-source RS RTL (freecores RS(204,188),
  wyvernSemi eccExamples, ...) for comparison; licences differ (GPL among
  them) -- read before borrowing structure, never copy code.
