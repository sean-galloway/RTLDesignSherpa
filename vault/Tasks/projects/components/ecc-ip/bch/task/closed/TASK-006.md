# TASK-006: BCH top wrappers (AXIS + AXI4) and bit-error injector

**Status:** closed 2026-10-08 — wrappers and the shared bit-granular injector
landed 2026-10-04 (AXIS + AXI4 tops, beat packer, gate DV); close condition
re-verified today: Verilator + Verible + declaration-order lint green on all
22 modules, and the wrappers have been exercised end-to-end by the 14-test
UART harness suite and both boards' batteries since.
**Priority:** P3
**Owner:** TBD

The BCH cores speak plain valid/ready with per-bit keep; the RS component
shows the adapter shape (RS PRD D9, carried by BCH PRD D9): AXIS tops and
AXI4 job tops in `rtl/top/`, pure datapath, no register blocks. The board
loop (TASK-007) instantiates these tops, so they land first. The one block
with no RS reuse path is the error injector: RS corrupts whole symbols via
GF tables; a binary BCH code needs bit-granular flips.

## Scope

- `rtl/top/bch_encoder_axis4.sv`, `rtl/top/bch_decoder_axis4.sv` —
  `axis4_slave`/`axis4_master` around the cores, tid/tdest held across the
  block, decoder verdict re-registered to `m_axis_tlast`, tstrb/keep rule:
  byte-aligned keep drives `tstrb` (all standing profiles are byte-aligned);
  otherwise keep rides `tuser` low bits with `tstrb` all-ones (RS rule).
- `rtl/top/bch_encoder_axi4.sv`, `rtl/top/bch_decoder_axi4.sv` —
  memory-to-memory job engines around the cores, `-f`'ing
  `reed-solomon/rtl/filelists/rs_axi4_engines.f` (audit-clean cross-area
  reuse); beat geometry from `bch_pkg` helpers; decoder accumulates
  `stat_blocks_*` job counters like RS.
- `rtl/fub/bch_error_injector.sv` — bit-flip injector, RS mode semantics
  (NONE / COUNT / BURST / RATE), LFSR-seeded, keep-aware, position universe
  N_BITS, stats counters (bits flipped, blocks hit, blocks >t, last block).
- Model-first DV per top on the three standing profiles plus the board
  profile (13, 0x201B, 8, 4224, 1, BITS_PER_BEAT=32), mirroring
  `test_rs_axis4.py`, `test_rs_axi4_engines.py`, `test_rs_axi4_loop.py` and
  their TB classes/fixtures.

## Definition of done

- Gate suite green for every new test; `make -C rtl lint-all` clean.
- `bin/filelist_registry.py --check` and `--audit` clean with the new
  filelists.
- No BCH-specific logic lands in the RS tree; the engines are `-f`'d.

## Log

**2026-10-03 -- filed and activated**, as the board bring-up plan
(2026-10-03) entered Phase 1.
