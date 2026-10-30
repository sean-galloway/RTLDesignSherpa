# common-ip — the cache-ip shared home

The MESI L1 core that more than one cache IP instantiates. Created
2026-10-11 (owner directive) when jet-mesi-l1's inheritance contract made
"amber's core lives in amber's directory" the wrong home: anything two IPs
compile against belongs to neither of them.

## What lives here

- `rtl/includes/l1_pkg.sv` — the shared package (geometry defaults,
  state/snoop encodings, Table 3.0 decode).
- `rtl/fub/` — the twelve core leaf blocks: snoop kmap, tag/data arrays,
  replacement engine, snoop responder, control, pending-fill bypass, fill,
  drain, CPU frontend, monlite, victim.
- `rtl/top/l1_core.sv` — the core itself: pure structural integration of
  the twelve FUBs (MAS ch01 hierarchy).
- `rtl/filelists/` — the per-module closure lists for everything above.
  They resolve through `$CACHE_COMMON_ROOT` (exported by
  [`env_python`](../../../../env_python), mirrored in
  [`bin/TBClasses/shared/filelist_utils.py`](../../../../bin/TBClasses/shared/filelist_utils.py)
  and [`bin/filelist_registry.py`](../../../../bin/filelist_registry.py)).

## The sharing contract

Inherited by every consumer, as recorded in
[`../jet-mesi-l1/README.md`](../jet-mesi-l1/README.md) and its HAS: the
CPU-side front end, tag/data arrays, replacement engine, and snoop responder
come from here whole. What differs per IP — the fabric master stack and the
coherent-transaction issuer — lives in the consumer's own top wrapper
(amber's `amber_ace_issue`, tops, and fabric stay in
[`../amber-mesi-l1/`](../amber-mesi-l1/)). A consumer that needs to modify a
block here inherits the obligation to re-run the whole verification baseline
(proofs and golden-model parity), not assume it.

The blocks here carry the neutral `l1_*` module/file prefix — renamed from
`amber_*` on 2026-10-12 (commit 79dc18ccb) because anything two IPs compile
against belongs to neither of them; the unit-level modules each IP owns
(amber's `amber_top`/`amber_ace_top`/`amber_pair_fabric`/`amber_ace_issue`)
keep their codename prefix.

## The dv area (2026-10-30)

[`dv/`](dv/) holds the lowest-level checkout of everything in `rtl/` — the
unit TBs (moved from amber, where they were written), the test harnesses,
the testplans, the shared golden model ([`dv/golden/`](dv/golden/): the
gem5-derived FSM oracle and the cache_sim harness), and the trace corpus
([`dv/traces/`](dv/traces/)). Test names and harnesses carry the `l1_*`
prefix of the modules they pin; the TB class names keep their amber
heritage for now (a class rename is its own cleanup). Run from
`dv/tests/`: `SEED=1 REG_LEVEL=GATE python3 -m pytest test_l1_<unit>.py`.

## What deliberately does not live here (yet)

- Integration tops and IP-specific issuers — owned by each IP dir.
- onyx/basalt RTL — onyx is a coherency manager, not a cache; basalt is
  penciled only. Neither shares RTL with the L1 core today.

## References

- [`../amber-mesi-l1/`](../amber-mesi-l1/) — the proving IP: every block
  here was designed, verified, and documented in amber first (amber MAS ch01
  block hierarchy, ch05 verification).
- [`../jet-mesi-l1/`](../jet-mesi-l1/) — the inheriting IP: the contract
  above is its documented starting position.
- ACE coherency contract the snoop responder implements:
  [`../References/AMBA_ACE_Interface_Definition.md`](../References/AMBA_ACE_Interface_Definition.md).
