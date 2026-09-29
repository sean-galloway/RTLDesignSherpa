# TASK-001: Stand up the Reed-Solomon component

> Migrated 2026-09-27 from `vault/Tasks/projects/components/ecc-ip/reed-solomon/open.md` as **RS-001** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** ACTIVE 2026-09-29 (was open 2026-08-09) (created when COMMON-009 was dropped — Sean's
call: R/S is component work, not rtl/common library work)
**Priority:** P3 — waits on a real consumer (NAND flash, comms, storage)

Library ECC is Hamming SECDED only. BCH/Reed-Solomon was tracked as a
common-library enhancement (COMMON-009) and dropped: an R/S codec brings a
GF(2^m) arithmetic layer, syndrome/Berlekamp-Massey/Chien machinery and
configuration surface that belongs in its own component with its own PRD,
DV area and task pages — the shape of `projects/components/bridge/` or the
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
