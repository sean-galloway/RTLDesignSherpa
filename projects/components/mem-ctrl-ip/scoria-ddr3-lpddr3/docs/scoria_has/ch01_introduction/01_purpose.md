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
It is the third member of a family: pumice covers DDR2/LPDDR2 and is built,
measured and running on hardware; a DDR4/LPDDR4 controller is planned.

This document specifies scoria's architecture. Its purpose is to be *locked*
before RTL begins, so that the implementation has a fixed target and the PRD —
which explicitly waits on a locked HAS — can be written.

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
simulation. The board target is deliberately deferred.
