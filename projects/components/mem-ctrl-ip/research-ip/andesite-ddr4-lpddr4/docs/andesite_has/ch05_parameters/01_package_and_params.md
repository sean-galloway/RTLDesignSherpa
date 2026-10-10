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

# andesite_pkg, and Build-Time vs Runtime

## The package

andesite carries its own `andesite_pkg` from day one. The shared-core design
— the family memtype enum, the shared timing-struct inventory, the migration
plan with its conditions — is owned by the family doc
[01_mem_ctrl_pkg.md](../../../../../common-ip/docs/01_mem_ctrl_pkg.md) and is **referenced
here, not restated**. What belongs to this chapter is only what andesite's
package owns.

**The memtype enum note.** andesite has no legacy CSR to disturb — the
shipping-design constraint that kept pumice and scoria at one bit does not
apply here. `andesite_pkg` therefore takes the family design as-is: one LP
axis bit plus the two-bit generation field, values assigned in the family
doc. The day-one note that matters for the register block: the memtype CSR
field in `andesite_csr.rdl` is three bits from birth, and the `PHY_TIMING`
shadow carries it without a width migration. When the family migration lands
(both shipping controllers moving together, per the family doc's conditions),
`andesite_pkg` folds into `mem_ctrl_pkg` with only an import change.

**The opcode set.** scoria's 4-bit internal `OP_*` encoding carries
(`scoria_pkg.sv:47-60` — NOP through the refresh and ZQ ops), and this tier
adds one member: `OP_MPC`, the LPDDR4 multipurpose command whose opcode
encoding on the 6-bit CA bus the formatter's new submodule owns. Gear-down is
a sequenced mode entry, not an opcode; the long/short timing pairs are
values, not opcodes. Nothing else in the command set changes shape.

## The rule: timings are runtime, geometry is build-time

Inherited from the family doctrine and restated because it is the single most
load-bearing convention here:

**Every enforced timing is a runtime CSR.** Not a parameter. A timing
compiled in cannot be swept, and a controller whose timings cannot be swept
cannot be characterized. This edition's additions — the tCCD_L/S and
tRRD_L/S pairs above all — follow the rule absolutely: they are the feature
DDR4 adds, and they are runtime like everything else.

**Build-time is reserved for what cannot be runtime:** bus widths, the DFI
gear ratio, CAM depths, bank and rank counts, and the geometry below. The
test is whether changing it changes the amount of hardware.

The design point of Chapter 2.4 fixes the geometry, and these two rows are
the book's canonical statement of it — repeated here byte-identical so a
reader of either chapter sees the same string:

| Side | Geometry | Source |
|---|---|---|
| DRAM, DDR4 side | DDR4-1600 x8, 4 bank groups × 4 banks = 16 banks, MT40A1G8-class | bootstrap spec §2 design point |
| DRAM, LPDDR4 side | LPDDR4-1600 x16, 8 banks per channel — ungrouped; the package offers two x16 channels | bootstrap spec §2; JESD209-4 |

: Table 5.0: The design-point geometry, byte-identical to Chapter 2.4

| Kind | Build-time or runtime | Examples |
|---|---|---|
| Bus and geometry | build | data width, address width, the Table 5.0 geometry, `NUM_RANKS = 1`, CAM depths |
| DFI gearing | build | the 1:4 frequency ratio, which must equal the PHY's phase count |
| Memtype | build | the family `memtype_e`, three bits |
| JEDEC timings | **runtime** | every command-spacing and recovery parameter |
| New DDR4 timings | **runtime** | tCCD_L/S, tRRD_L/S, the FGR-scaled tRFC family, the ODT latency family |
| LPDDR4 timings | **runtime** | the JESD209-4 command and training intervals |
| Policy selects | **runtime** | page policy, refresh policy (FGR factor, per-bank policy), ZQCS placement (inherited), ODT policy, DBI enables, gear-down select, CA-parity scope, and the carried-forward TASK-001 mode selects |

: Table 5.1: Build-time versus runtime

**Important — the frequency ratio must equal the PHY's phase count, set
identically on both sides.** Inherited from scoria, not negotiable: a
mismatch is a functional break that presents as data corruption, not as an
error.

## New CSR groups

The register set grows past scoria's. Exact offsets are not fixed in this
edition — they come from the RDL, authored with the RTL, and registers are
named, not offset-numbered, everywhere in the books (Ch 4.2). The content is
specified:

| Group | Contents |
|---|---|
| Init | the `tINIT*` family, `tDLLK`, `tZQinit`, `tMRD`, `tMOD` — named per JESD79-4 / JESD209-4, values recorded as open question Q1 until read from cold storage |
| Refresh | the FGR select (MR3 image), the per-bank refresh policy, and the inherited `REF_CTRL` elastic/TCR fields with their `REF_STATS` telemetry |
| ODT | RTT_NOM / RTT_WR / RTT_PARK programmed values, the ODT latency family, the policy select, and ODT telemetry |
| Training | the inherited write-leveling windows, the read-leveling (MPR) windows, the LPDDR4 CA/WDQ windows, per-chip-select results, and the four-state telemetry of Ch 3.3 |
| DBI / parity | read/write DBI enables (MR5 image), CA-parity enable and scope |
| LPDDR4 | channel configuration, MPC calibration interval, CA-training control |

: Table 5.2: New CSR groups

**Notes that carry.** `tWLMRD`'s open maximum stays a controller-defined CSR
timeout with a distinct status bit — the family rule, quoted in Ch 3.3. The
gear-down select programs a mode the datapath never sees; it exists so one
bitstream can run both CA rates. And the FGR select's CSR exists so the
retention re-derivation Ch 3.4 requires can be *swept*, not just asserted.

## The duplication, recorded again

`pumice_pkg`, `scoria_pkg` and `andesite_pkg` will carry near-identical type
definitions for a period. That is deliberate and time-boxed, owned by the
family doc's migration plan, and recorded here — as it was recorded in
scoria's Chapter 5 — so a later reader does not "fix" it by widening a
shipping CSR. That widening is precisely the thing the arrangement exists to
prevent.
