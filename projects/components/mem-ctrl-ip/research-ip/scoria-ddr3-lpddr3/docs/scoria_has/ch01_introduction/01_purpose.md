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

scoria is a unified, parameterized memory controller for DDR3 SDRAM and LPDDR3
SDRAM, presenting an AXI4 slave to the host and a DFI v3.1 master to the PHY.
It is the second member of a family: pumice covers DDR2/LPDDR2 and is built,
measured and running on hardware; a DDR4/LPDDR4 controller is planned as the
third.

This document specifies scoria's architecture. It was written to be *locked*
before RTL began, so that the implementation had a fixed target; the RTL now
exists, and each edition since has reconciled the two. The PRD — which
explicitly waited on a locked HAS — is authored against this document.

## Why a delta specification

scoria is not a fresh design. The controller architecture it uses is pumice's,
and that architecture has been through board bring-up, a read-path rebuild that
took reads from 291.7 to 571.3 MB/s, and a formal campaign that found two real
bugs. Re-deriving it would discard that evidence.

So this specification is organised as a delta. Every block is marked
**INHERITED**, **MODIFIED** or **NEW**, and the marking carries an obligation:

- **INHERITED** means the pumice block is used unchanged, and its verification
  evidence transfers. If a block is marked inherited and then changed during
  implementation, the marking is wrong and this document must be corrected —
  not the marking quietly dropped.
- **MODIFIED** means a bounded change with a named cause, always a clause of
  JESD79-3F, JESD209-3C or DFI v3.1.
- **NEW** means no pumice counterpart. There are two, and both are small.

## What is in scope

The controller between the AXI4 slave port and the DFI v3.1 master port: the
front end, the scheduler, bank and global timing enforcement, refresh, mode
registers and initialization, ZQ calibration, the write-leveling interface, the
data paths, and the CSR block.

## What is out of scope

**The PHY.** DFI is the boundary, as it is for pumice, and for the same reason:
IOB serdes, bitslip and delay-line calibration are FPGA- or process-specific
and do not belong in a portable controller. This is a deliberate architectural
commitment, not an omission.

**The write-leveling search.** DDR3 adds write leveling, and scoria provides the
interface to perform it — the DFI handshake, the MR1 path, the timing windows
and the telemetry. The search algorithm itself runs in firmware. This was
settled as decision D2 and is argued in Chapter 3.

**The DDR4/LPDDR4 half of DFI v3.1.** Targeting v3.1 brings signals scoria has
no use for: `dfi_act_n`, bank groups, chip ID, CA parity and `dfi_alert_n`, Data
Bus Inversion, and CA training. They are named here so their absence is a
decision on the record rather than an oversight.

**Board bring-up.** Verification is against a DFI bus functional model in
simulation, and that remains the verification boundary. The board target is
no longer deferred — Genesys 2, K7DDRPHY, 2 x MT41J256M16 (Chapter 2.4) — a
board build flow exists, and the first out-of-context synthesis has been run
(scoria BUG-003: WNS -2.022 ns against a 10 ns constraint, which closes with
~+1.3 ns of slack against the restated 75 MHz design point; the owner
restated the clock 2026-10-10 — 100 MHz was never the target — and the bug
closed on that restatement). Bring-up itself remains outside this document's
scope.
