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

# Init and ZQ: RESET#, MR0-MR6, Gear-Down

## The sequence is JEDEC's, verbatim

JESD79-4 specifies DDR4 power-up initialization as a numbered sequence, and
JESD209-4 specifies LPDDR4's own. Both are reproduced here as *requirements
on the sequencer*, in each spec's order, because the order is not ours to
choose. The timings are named with their JEDEC symbols; their values are
cited to the standards' initialization sections and land in the CSR
derivation (Chapter 5). What binds the sequencer is the order and the
dependencies, and those are stated fully.

DDR4:

| Step | Requirement |
|---|---|
| 1 | Power ramp, with the spec's voltage-ordering constraints. Board-level, not controller-level |
| 2 | Assert `RESET#` through its power-up window (`tINIT1`), then de-assert; keep CKE inactive |
| 3 | Wait the RESET#-deassertion-to-CKE interval (`tINIT3`), clocks stable per the spec's requirement |
| 4 | CKE active starts the internal init; wait `tINIT4` before the first MRS |
| 5 | MRS to **MR3** |
| 6 | MRS to **MR6** |
| 7 | MRS to **MR5** |
| 8 | MRS to **MR4** |
| 9 | MRS to **MR2** |
| 10 | MRS to **MR1** (DLL enable, and ODT/RTT_NOM programming per the board) |
| 11 | MRS to **MR0** (DLL reset, and CA parity latent mode set if parity is enabled later) |
| 12 | **ZQCL** to start ZQ calibration |
| 13 | Wait `tDLLK` and `tZQinit`; ready for normal operation |
| 14 | *If gear-down is used:* program gear-down in MR3, run the gear-down entry sequence, wait its sync time — then normal operation at half CA rate |

: Table 3.3: DDR4 initialization requirements, ordered per JESD79-4

LPDDR4:

| Step | Requirement |
|---|---|
| 1 | Power ramp with the spec's sequencing; MRW to the reset-related mode states per JESD209-4 |
| 2 | Reset (performed over the CA bus or the reset pin per the part), then the spec's initialization wait |
| 3 | Mode-register writes in JESD209-4's order — including the ODT, drive-strength and DQ ODT programming LPDDR4 carries in its MR set |
| 4 | ZQ calibration via **MPC** (the LPDDR4 path — see the ZQ section below) |
| 5 | Ready for normal operation; CA training before reliable operation if the board requires it (Ch 3.3) |

: Table 3.4: LPDDR4 initialization requirements, ordered per JESD209-4

Two recordings follow the tables, per the evidentiary rule. **First:** the
numeric init constants (the `tINIT*` family, `tDLLK`, `tZQinit`, `tMRD`,
`tMOD`) are cited to JESD79-4 §3 / JESD209-4's initialization sections and
are recorded as open question Q1 in Chapter 6 until read from cold storage at
CSR-derivation time — this book does not state them from memory. **Second:**
the MRS order above is MR3-MR6-MR5-MR4-MR2-MR1-MR0, and it is not sorted —
MR0 carries the DLL reset and goes last, so the order encodes a dependency
the way scoria's MR2-MR3-MR1-MR0 did. pumice's EMRS3-first correction is the
family precedent: the sequence is a citation, not a design choice.

## What the sequencer owns

**`RESET#` is a pin, not a command** — scoria already learned this shape, and
andesite inherits the pattern: the sequencer drives a reset output, holds it
through its timed window, and the output reaches the top level and the PHY.

**Gear-down entry.** DDR4 runs its CA bus at full rate for initialization,
then optionally halves it. The entry is a sequenced mode switch: program
gear-down in MR3, issue the entry sequence, wait the sync interval, then
operate at half rate. The DFI side has a matching controller/PHY handshake so
both sides of the boundary switch together `§TBC(TASK-005)`. Whether the
design point uses gear-down is a CSR-selectable choice; the FSM must support
both rates because initialization always happens at full rate.

**Parity enable.** CA parity is enabled through the MR sequence (MR4/MR5
carry parity's programming; the exact fields are the MAS's mode-register
chapter). The sequencer's obligation is ordering: parity may only be enabled
once the bus is stable, and the formatter's parity counter starts counting
from that point — a dependency between the sequencer and the formatter that
the FSM states must make explicit.

**The mode-register set becomes seven.** `mode_register` (MODIFIED) carries
MR0-MR6 for DDR4 — MR0 (burst, CAS latency, DLL reset, write recovery),
MR1 (DLL enable, additive latency, RTT_NOM, write leveling), MR2 (CAS write
latency, refresh-related selects), MR3 (**MPR access, FGR select, gear-down**),
MR4 (write CRC's mode bits — inert this edition — and CA parity), MR5 (read
and write DBI, RTT_PARK), MR6 (VrefDQ training) — and the LPDDR4 MR set
beside it. Field-level maps are the MAS's business; this chapter binds the
register count, the programming order, and which MRs couple to other blocks
(MR3 to refresh and training, MR5 to ODT and the DBI datapath, MR4 to the
parity machinery).

## ZQ calibration

DDR4's ZQ story is inherited. `ZQCL` closes initialization, `tZQinit` gates
readiness, `ZQCS` runs periodically as maintenance traffic with its interval
a runtime CSR, and the module requests the bus and waits — it never preempts
(family doctrine 2). scoria's `zq_ctrl` does exactly this and andesite uses
it for DDR4 unchanged, including the CSR-selectable placement policy scoria
landed as TASK-001 Mode C.

LPDDR4's is the new path. JESD209-4 carries calibration on the **MPC**
command — ZQCal start and latch as MPC opcodes on the CA bus — so `zq_ctrl`
grows a NEW submodule: an MPC issuer that sequences calibration through the
formatter's LPDDR4 CA path and reports the same way the inherited core does.
The maintenance shape is unchanged: interval CSR, request and wait, telemetry
count. What changes is only the bus the calibration rides.

**The scheduler consequence is one input, as it was in scoria.** Refresh
demand, ZQ demand (DDR4 or LPDDR4), and the new odt_ctrl's turnarounds all
arrive as maintenance-class requests; `mem_cmd_scheduler` arbitrates them
with the same request/grant machinery it inherited.
