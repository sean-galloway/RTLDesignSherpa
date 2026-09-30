# TASK-001: Stand up the Reed-Solomon component

> Migrated 2026-09-27 from `vault/Tasks/projects/components/ecc-ip/reed-solomon/open.md` as **RS-001** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** ACTIVE 2026-09-29 (was open 2026-08-09) (created when COMMON-009 was dropped — Sean's
call: R/S is component work, not rtl/common library work)
**Priority:** P3 — waits on a real consumer (NAND flash, comms, storage)

Library ECC is Hamming SECDED only. BCH/Reed-Solomon was tracked as a
common-library enhancement (COMMON-009) and dropped: an R/S codec brings a
GF(2^m) arithmetic layer, syndrome/Berlekamp-Massey/Chien machinery and
configuration surface that belongs in its own component with its own PRD,
DV area and task pages — the shape of `projects/components/fabric-gen-ip/bridge/` or the
dmas, not a single-file primitive.

When a consumer appears:
- PRD first: symbol width m, t (correctable symbols), shortened codes,
  encoder-only vs full decoder, throughput target — and whether BCH (the
  binary special case, previously tracked alongside R/S and also ended with
  COMMON-009) is in scope here or stays out.
- Location: `projects/components/ecc-ip/reed-solomon/` (rtl/, dv/, PRD.md),
  filelists registered per [[filelists]] from day one.
- Reuse survey per CLAUDE.md before any new RTL: `dataint_ecc_*` shows the
  house ECC interface conventions; the GF layer is new ground.

History: a docs-only `projects/components/bch/` placeholder (PRD/README/
TASKS, no RTL, no tests) was deleted 2026-07-23. Do not recreate
placeholder collateral — this task page IS the placeholder; the component
directory gets created when work actually starts.

---

## Log

**2026-09-29 -- area created at Sean's request; references gathered.**
`projects/components/ecc-ip/reed-solomon/` now holds `README.md`, `CLAUDE.md`, a
DRAFT `PRD.md` whose section 3 is the decision table this page asked for
(m, t, shortening, encoder-only vs decoder, erasures, throughput, BCH,
generator conventions, interface, first consumer) with four candidate profiles
(CCSDS RS(255,223), DVB RS(204,188), 802.3 RS-FEC, RAID erasure), and
`References/`: six stored public documents (NASA TM-102162 tutorial, CCSDS
131.0-B-5 and 130.1-G-3, BBC WHP031, Plank 1997 + 2003 correction) with
source and licence each, plus the cited classics, the standards that name RS
codes, open-access arXiv reading and the open-source implementations for the
reuse survey and the DV golden model (`reedsolo`, `galois`). Still true: no
RTL, no DV, no filelist -- those wait on the PRD decisions. The "do not
recreate placeholder collateral" rule above is superseded for the area shell
by Sean's request; it still holds for RTL/DV/MAS skeletons.

**2026-09-29 -- decision:** the key-equation solver is riBM (Sarwate-Shanbhag
reformulated inversionless Berlekamp-Massey); Sean, on the architecture sketch.
Recorded as PRD D11. `docs/rs_architecture_sketch.md` added the same day.

**2026-09-29 -- decision:** `SYMBOL_WIDTH` is its own parameter with an
elaboration check that `DATA_WIDTH` is a multiple; `SYMBOLS_PER_BEAT` is the
derived throughput factor (PRD D1/D6, Sean). Scramblers are a separate FUB.

**2026-09-29 -- decision:** the scrambler is behind `ENABLE_SCRAMBLER` (PRD D12,
Sean); off is a tested build. ETSI direct-PDF links added to References.

**2026-09-29 -- decision:** the boundary is selectable per end, `INTAKE_IF` and
`OUTLET_IF` each AXIS or AXI4 (PRD D9, Sean). AXI4 ends are a read engine / write
engine pair on STREAM's engine shape behind the `axi4_master_{rd,wr}` wrappers,
with jobs from the regblock or a descriptor stream; sketch rows added.

**2026-09-29 -- refinement of D9 (Sean):** the IP is a core with simple valid/ready
at both ends so it can be dropped into a compute engine or a memory controller;
the AXIS/AXI4 boundaries are optional adapters (`INTAKE_IF`/`OUTLET_IF` default
`NONE`). PRD 4a records that RS is an endpoint codec, not a mid-stream insert.

**2026-09-29 -- `docs/rs_fub_catalog.md`** (Sean's ask): every FUB bottom-up with
all instantiated components and counts; the sketch's FUB table now points at it.

**2026-09-29 -- D11 widened (Sean):** a Euclidean solver too, selectable by
`KES_ALGO` (riBM default). Affected blocks only: `euclid_pe` (L1),
`key_equation_solver_euclid` (L2), the decoder core's generate; catalog compares
the two; References gain Shao 1985 and Baek-Sunwoo 2006.

**2026-09-29 -- D7 (Sean):** BCH is out of this component; it will be its own
`ecc-ip/bch/`. GF primitives stay general for reuse.

**2026-09-29 -- HAS v0.1 (draft)** (Sean: "Are you ready for the HAS now?"):
`docs/reed_solomon_has/` on the bridge HAS layout -- 23 chapters in ch00..ch06,
three mermaid diagrams, styles YAML, `docs/generate_has_pdf.sh`; built to
`docs/Reed_Solomon_HAS_v0.1.{pdf,docx}` (100 pages). Reference profile for every
number is RS(255,239), t = 8, m = 8, one symbol per beat; open PRD items D2/D3/
D5/D10 carried as TBD parameters (table 6.3). Two build lessons: the cloned
script's `REPO_ROOT` needed one more `..` for the `ecc-ip/` depth, and the
index's Related Modules links inlined PRD + catalog + References as chapters
(150 pages) until they became plain paths.

**2026-09-30 -- first RTL: the GF(2^m) layer** (Sean: "start working on the
RTL"). `rtl/gf/gf_pkg.sv` (constant functions over m and PRIM_POLY, no
generator), `gf_mul_const.sv` (constant-multiply matrix, XOR network),
`gf_mul.sv` (Mastrovito: AND array + constant reduction), `gf_inv.sv` (log /
antilog tables, m <= 12, `ow_zero`). Filelists per top + `reed_solomon_all.f`,
area registered in `bin/filelists.toml`, `rtl/Makefile` on area.mk: Verilator
and Verible clean at m = 4, 8, 10, 12 (16 for the multipliers). DV: `GFTB` in
`dv/tbclasses/gf_tb.py` against `reedsolo` (pinned in requirements.txt), three
Pattern B runners under `dv/tests/fub/`; 12/24/36 cells pass at gate/func/full,
full is exhaustive at m = 4 and 8 (65536 pairs) and 65k random pairs at m = 10;
the multiplier checker was mutation-checked (dropping one reduction term gave
155 mismatches in 561). Tooling side effect: `projects/components/__init__.py`
now resolves hyphenated component dirs below the family level
(`reed_solomon` -> `reed-solomon`), which pumice and the other hyphenated
components could not do through the shim before. Reuse survey: no GF
arithmetic existed anywhere in the tree.

**2026-09-30 -- D2 and D3 decided (Sean: "All can be elaboration time"):**
t and n are elaboration-time parameters `T_SYMBOLS` (default 8) and `N_SYMBOLS`
(default 2^m - 1), k derived; no run-time programmability. This unblocks the
encoder core and the decoder core; D5 (erasures) and D10 (consumer) stay open.

**2026-09-30 -- encoder core.** `rtl/gf/gf_lfsr_encoder.sv` (Level 1: 2t
`gf_mul_const` taps, g(x) built at elaboration from t and b, parity drained by
zero-feedback shifts) and `rtl/rs_encoder_core.sv` (Level 3: valid/ready both
ends, `last` boundary, `frame_err`, output `gaxi_skid_buffer`; S = 1 only, guarded).
Lint clean at RS(255,239), RS(21,19), RS(15,11), RS(544,514). DV: `GFLFSRTB`
drives the LFSR directly (5 configs incl. the CCSDS field 0x187 with b = 112);
`RSEncoderTB` drives the core through GAXIMaster/GAXISlave on the `in_`/`out_`
prefixes with reedsolo `rs_encode_msg` as golden -- blocks, five valid/ready
profiles, short/long framing errors, and a throughput check that measures
exactly n cycles per n symbols under back-to-back timing. Area: 21/42/63 cells
green at gate/func/full. Mutation check: building g(x) with one root too few
gave 8 mismatches in 12 checks on RS(21,19). Next: the multi-symbol (S > 1)
encoder datapath, or the decoder's syndrome unit.

**2026-09-30 -- decoder sub-blocks.** `dv/tbclasses/rs_model.py`: the hardware
algorithms in Python on reedsolo's field, validated 900/900 against reedsolo's
decoder on six profiles (0..t+1 errors). It settled three things before RTL:
riBM's evaluator is (S*Lambda)[2t:3t] so Forney uses X^(1-b-2t); the riBM array's
top t cells are the degree check; and a post-correction syndrome re-check is
needed to match reedsolo's detection (RS(15,11), 3 errors, degree-1 locator with
one root, corrected word not a codeword). RTL: `gf_syndrome_cell` + `syndrome_unit`,
`ribm_pe` + `key_equation_solver_ribm`, `chien_search`, `forney_evaluator`, all
lint-clean at five profiles, each with a direct-drive TB in
`dv/tbclasses/rs_decoder_blocks_tb.py` scored bit-exact against the model
(five configs each, incl. CCSDS 0x187 b = 112 and RS(15,11)). Next: `rs_decoder_core`
(block FIFO, descriptor pipeline, corrector, re-check syndromes, status with out_last).

**2026-09-30 -- `rs_decoder_core`.** Receive / solve / correct stages behind two
descriptor skids; block FIFO and output FIFO on `gaxi_fifo_sync`; a second
`syndrome_unit` re-checks the corrected stream; the output FIFO carries
`{rx, correction, hit}` and a block is released only with its verdict, so an
uncorrectable block leaves as received (the first cut applied corrections in the
walk and emitted altered symbols on 2 of 20 checks -- fixed by moving the XOR to
the output). Runaway blocks are force-ended at the FIFO depth with frame_err.
`RSDecoderTB` through GAXI BFMs, scored against `rs_model.decode`: 0..t errors,
t+1 and more (verdict must match the model), short/long/one-symbol framing,
five timing profiles, throughput (measured 252-257 cycles per RS(255,239) block;
15.5, 22.0, 201.5 on the other profiles). Area 45/90/135 cells green. Mutations
caught: re-check inverted (12/20), correction suppressed at position 0 (3 of 4
seeded cells). HAS chapters 3.2, 4.1, 5.2, 5.3, 6.4 and the catalog updated for
release-on-verdict (first-symbol latency 2n + 2t, output FIFO 2k x (2m+2)).
Still open on the decoder: S > 1, erasures (D5), the Euclid solver variant.

**2026-09-30 -- Euclid solver (Sean: "work on 1/3").** `rs_model.py::euclid` in
the RTL's register form (top-aligned R/Q, shifted lam~/mu~ of 2t+3 symbols,
normalise / cross / swap), validated: identical decode to riBM on 900/900
blocks; cycles t+1..2t. `rtl/key_equation_solver_euclid.sv` bit-exact (5 configs,
56 checks each at gate); `forney_evaluator` gains `OMEGA_HIGH_HALF` (textbook
Omega for Euclid); `rs_decoder_core` gains `KES_ALGO` and two Euclid cells in the
decoder test decode identically (20/20 each). Item 1 (S > 1) next.

**2026-09-30 -- S > 1 on both cores (Sean: "work on 1/3").** `gf_lfsr_encoder`,
`gf_syndrome_cell`/`syndrome_unit`, `chien_search`, `forney_evaluator`,
`rs_encoder_core`, `rs_decoder_core` all take `SYMBOLS_PER_BEAT`; S single steps
unrolled with the state after the beat's count muxed; Chien/Forney evaluate S
lanes from one register set (S inverses). keep is low-aligned, partial only on a
block's last beat (a partial earlier beat is a framing error). Encoder output
carries partial beats at the end of the data and of the parity; decoder output
only at the end. Lint clean at S = 1, 2, 3, 4, 8. Gate cells green at S = 1/3/4/8
on both cores and all sub-blocks; measured encoder 32 cycles per RS(255,239)
block at S = 8, decoder 33. One TB bug on the way (a shadowed `vals` in ForneyTB).
HAS 3.2, 4.1, 5.1 (with a measured table), 5.2, 6.2 and the catalog updated.

**2026-09-30 -- Nexys A7 loop harness (Sean: "build this in the nexysa7 board").**
`projects/fpga-systems/NexysA7/reed-solomon/build-loop`: axis4_master_pattern_gen
-> rs_encoder_core RS(252,236) S=4 -> rs_error_injector -> rs_decoder_core x2
(RIBM, EUCLID) -> axis4_slave_pattern_check x2 + comparator + tallies, PeakRDL
CSRs (`rs_loop_regs.rdl`) behind the UART bridge via a new shared
`converters/rtl/axil4_to_peakrdl.sv`. Host: by-name driver, programs shared by
sim and board, sequences init/smoke/sweep, `run_smoke.py`. Six UART-equivalence
cocotb tests pass (smoke, bypass, clean, e=t, e=t+1, throttled). Profile
shortened to 252 because the shared checker compares whole 32-bit words. Two
tooling fixes on the way: `check_sv_decl_order.py` no longer treats struct
members as signals (PeakRDL output tripped it), and a RegisterMap trap -- an RDL
field named `count` breaks the regmap loader -- is in the handbook.
Synthesis on the A7 (100 MHz): first run WNS -16.2 ns, 41 logic levels from the
injector's selection-sampling DSP chain straight into decoder A's syndrome
unit; pipelining the injector (3 stages) gave -4.0 ns with the Chien -> Forney
-> re-check -> status chain (24 levels) next; the decoder's correct stage is now
split (C1 walk register, C2 emit). Regressions stayed green through both
(component 65/130/195, harness 6/6).
