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

## TASK-LPDDR2-WRPATH: LPDDR2 write-auto-precharge dropped writes — RESOLVED

RESOLVED (RDS-DV DFISlavePHY fix). `workload_mix_lpddr2` had dropped writes under
LPDDR2's HAPPY_HYBRID row-miss policy, which issues WRA (write-auto-precharge). Root
cause was NOT the CA encoding or write cadence: the DFI slave `_handle_command` had
branches for WR/RD but none for WRA/RDA. DDR2's decoder never returns WRA/RDA (it
returns WR/RD and carries auto-precharge in addr bit 10), but the bit-exact LPDDR2 CA
decoder folds AP into the opcode → returns WRA/RDA → fell through → no pending write →
wrdata_en became "stray data beats" and the write was silently dropped. Fix: fold
WRA→WR and RDA→RD in `_handle_command` (auto-precharge already carried in addr bit 10
for both paths). All LPDDR2 traffic tests now pass; xfail removed.
