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

# Purpose and Scope

## Purpose

andesite is a unified, parameterized memory controller for DDR4 SDRAM and
LPDDR4 SDRAM, presenting an AXI4 slave to the host and a DFI v4.0 master to
the PHY. It is the third member of a family: pumice covers DDR2/LPDDR2 and is
built, measured and running on hardware; scoria covers DDR3/LPDDR3 with RTL
verified in simulation. andesite inherits from scoria the same way scoria
inherited from pumice.

This document specifies andesite's architecture. It is written to be *locked*
before RTL begins, so the implementation has a fixed target; the follow-on RTL
bootstrap plan is authored against this document. Success, per the bootstrap
spec, is that a reader can trace every block here block-by-block to scoria's
books, that the changed and new blocks are covered in depth by the MAS, and
that the DRAM command and mode-register encodings are pinned by the generated
kmap book.

## Why a delta specification

andesite is not a fresh design. scoria's architecture — itself pumice's,
carried through board bring-up, a read-path rebuild, and a formal campaign
that found two real bugs — is the starting point, and scoria's 26-FUB
inventory, books, CSR flow and verification apparatus are the immediate reuse
pool. Re-deriving any of that would discard its evidence.

So this specification is organised as a delta. Every block is marked
**INHERITED**, **MODIFIED** or **NEW** relative to scoria, and the marking
carries an obligation:

- **INHERITED** means the scoria block is used unchanged, and its verification
  evidence transfers. If an inherited block changes during implementation,
  the marking is wrong and this document must be corrected — not the marking
  quietly dropped.
- **MODIFIED** means a bounded change with a named cause, always a clause of
  JESD79-4, JESD209-4 or DFI v4.0.
- **NEW** means no scoria counterpart. The new blocks are named in Chapter 2.3
  and specified in the MAS.

## What is in scope

The controller between the AXI4 slave port and the DFI v4.0 master port: the
front end, the scheduler, bank and global timing enforcement, refresh, mode
registers and initialization, ZQ calibration, training, on-die-termination
control, the data paths, and the CSR block. LPDDR4's deltas are carried
per-chapter, the same one-book-both-memtypes shape scoria uses.

## What is out of scope

**The PHY.** DFI is the boundary, as it is for scoria, and for the same
reason: IOB serdes, bitslip and delay-line calibration are FPGA- or
process-specific and do not belong in a portable controller. This is a
deliberate architectural commitment, not an omission.

**Board bring-up.** Verification is against a DFI v4.0 bus functional model in
simulation, and that is the verification boundary. There is deliberately no
board named: the 7-series targets this repo's boards carry do not support
DDR4, so a board target would be a promise this generation can't keep.

**The training searches.** DDR4 adds read leveling alongside write leveling,
and LPDDR4 adds CA and WDQ training. andesite provides the interfaces — the
DFI handshakes, the MR paths, the timing windows, the telemetry — and the
search algorithms run in firmware, exactly as scoria's write-leveling search
does (decision D2 there, carried here).

**LPDDR4 DVFS and deep-sleep states.** Named, deferred, and recorded in
Chapter 6 with the condition that un-defers them.

**The DDR5 half of DFI v4.x.** Targeting v4.0 brings signals andesite has no
use for — the DDR5-oriented pieces of the 4.x revision family. They are named
in Chapter 4 so their absence is a decision on the record rather than an
oversight, and they are out of scope the same way scoria's DDR4/v3.1 surface
was: named, then deliberately left unimplemented.

**The PRD and the RTL.** The PRD rewrite and the RTL bootstrap are follow-on
work, tracked in the vault lane (`vault/Tasks/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/`). This
book is the first of three: the MAS and the kmap book follow it, each
owner-reviewed before the next starts.