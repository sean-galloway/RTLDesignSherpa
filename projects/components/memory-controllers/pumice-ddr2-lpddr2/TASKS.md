<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# pumice — Open Tasks

## TASK-GEAR: Generic AXI ↔ DRAM-beat width gearing

Decouple `AXI_DATA_WIDTH` from `DRAM_BEAT_WIDTH` (today `axi_intake.sv` hard-assumes
they're equal). Make AXI width a free parameter (32/64/128/256/512) via an internal
gearbox localized to `axi_intake` — everything below the AXI↔beat seam is already
beat-parameterized. Primarily for **future DDR\* IP** (each device/PHY pins its own
beat/rate; hosts want a fixed AXI width); the Nexys A7 a7ddrphy x16 bring-up
(beat=32, rate=4) is the first consumer.

**Full design + effort + risks + resource note:** `docs/AXI_DRAM_GEARING_SCOPE.md`

## TASK-ADDRMAP: CSR-programmable AXI-address → {bank, row, col} field placement

Today `addr_mapper.sv` runtime-selects among three *fixed* schemes (ROW_MAJOR,
BANK_INTERLEAVE, XOR_HASH via `scheme_active_i`). Extend it so the AXI-address
decomposition into bank/row/col is fully **CSR-programmable at runtime** — i.e. cfg
bits select which AXI address bits land in each field (field bit positions / order),
not just one of three hardwired layouts.

**Ordering (important):** the cfg field-placement mapping is the FIRST stage — it
defines the raw AXI-address → {bank, row, col} bit extraction. The runtime scheme
(interleave / XOR-hash) is applied AFTER, composed on top of the cfg mapping. So the
pipeline is `AXI addr → cfg field map → scheme transform → {bank,row,col}`, NOT the
scheme selecting a whole fixed layout up front.

- Add CSRs for per-field placement (e.g. bank/row/col base-bit + width, or a
  compact "map descriptor") in the pumice regmap; the three current fixed schemes
  become power-on presets of the cfg mapping, with the scheme transform layered after.
- `addr_mapper.sv` becomes a programmable shift/mask decode driven by those CSRs
  (still combinational, single stage), with the scheme transform as a second
  combinational stage downstream of it.
- Keep the DV-side `AddressMapping` decode bit-for-bit identical (the RTL comment
  contract) — extend the Python model in lockstep (same cfg-map-then-scheme order)
  and cover with the existing addr_mapper conformance test.
- Motivation: real controllers expose address-remap registers so a host can retune
  bank/row/col interleave for a given traffic pattern without a rebuild; also needed
  when device geometry (bank count / row / col width) varies across the DDR\* family.

## TASK-LPDDR2-INIT: full LPDDR2 mode-register init (wide MR index + JEDEC values)

The LPDDR2 CA command formatter (`dfi_cmd_formatter.sv`) and BFM (`lpddr_ca.py`) now
encode MRW bit-exactly (JESD209-2F Table 60), but `init_sequencer.sv` carries the MR
index on the 3-bit `init_cmd_bank_o`, so only MR0..MR7 are expressible — LPDDR2 needs
MR1/2/3/10/63 etc. To bring up LPDDR2 *init* (as opposed to traffic reads, which work
with the current shallow init):

- Widen the init MR-index path (bank port → dedicated 8-bit MA field) end-to-end
  (init_sequencer → scheduler → formatter `w_mr_ma`).
- Add the LPDDR2 JEDEC init sequence values (MR-reset via MR63, MR10 ZQ calibration,
  MR1/2/3 device config) to the init sequencer, gated by `memtype`.
- Verify against the BFM's decoded MR shadow (the slave already decodes MRW).

Prereq/relationship: independent of the LPDDR2 read bring-up (CA traffic encoding);
that path only needs init to *complete*, not to program correct MR contents.

## TASK-LPDDR2-WRPATH: LPDDR2 write-data commit drops writes under mixed cadence

With bit-exact CA encoding landed, LPDDR2 *reads* work (`smoke_lpddr2` +
`open_page_lpddr2` pass). But `workload_mix_lpddr2` (xfail) drops a write: under mixed
read/write traffic the DFI slave logs ~48 "wrdata_en asserted but no pending write —
stray data beat" warnings and a golden location reads back 0 (`WRITE path: golden
@ 0x77e350 = 0x0 != wrote 0x1`).

Key facts:
- DDR2 `workload_mix` passes with ZERO stray-beat warnings → LPDDR2-specific.
- The downstream write path (scheduler / `pumice_dfi_wr_serializer` / DFI CDC) is
  memtype-agnostic; only the command *encoding* in `dfi_cmd_formatter` differs. So the
  suspect is the WR command's cs_n / decode timing (LPDDR2 flat CA word, cs_n on
  phase 0) vs the pre-pulled `wrdata_en` cadence — the slave sees the data before a
  pending write is registered and drops it.
- `open_page_lpddr2` writes commit fine → it is a cadence/interleave effect (mixed
  profile), not a blanket write break.

Investigate with a waveform: compare, for a dropped write, the dfi cycle of the WR CA
command (cs_n phase-0 assert) against the `wrdata_en` window the serializer drives.
Likely fix is on the RTL/BFM boundary (write-data-vs-command alignment for LPDDR2) or
a slave-model pending-write ordering assumption. NOT a read-path or CA-encoding issue.
