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
