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

# Definitions and Acronyms

## Interfaces

**AXI4**
The host-side slave interface. Inherited from pumice unchanged, including the
width-gearing converters that let the host bus width differ from the DRAM's.

**DFI**
DDR PHY Interface. scoria targets **v3.1** (decision D1). The boundary between
controller and PHY, and the same boundary the DV repo's bus functional model
drives in simulation.

**APB**
The CSR access interface, through a PeakRDL-generated register block.

## DRAM commands this document refers to

| Command | Present in DDR2? | Note |
|---|---|---|
| `ACT`, `RD`, `WR`, `PRE`, `REF` | yes | inherited handling |
| `PREA` | as PRE with A10 | DDR3 gives precharge-all its own encoding |
| `MRS` | yes | but DDR3 has MR0-MR3 where DDR2 had MR0-MR2 plus EMRS3 |
| `ZQCL` / `ZQCS` | **no** | ZQ calibration, long and short. New in DDR3 |
| `RESET` | **no** | DDR3 adds a hardware `RESET#` pin |
| `SRE` / `SRX` | yes | self-refresh entry and exit |
| `REFpb` | LPDDR2 has it | LPDDR3 keeps per-bank refresh |

: Table 1.2: Commands, and which are new to this family member

## Timing parameters new to scoria

| Parameter | Governs |
|---|---|
| `tZQinit` | ZQ calibration during initialization |
| `tZQoper` | a long ZQ calibration outside initialization |
| `tZQCS` | the short, periodic ZQ calibration |
| `tWLMRD` | delay from entering write-leveling mode to the first DQS pulse |
| `tWLDQSEN` | delay before the controller may drive DQS, by which point the DRAM has applied ODT |
| `tWLO` | write-leveling output delay: when the DRAM returns the result |
| `tWLOE` | DQ output uncertainty, allowing mismatch across DQ bits |

: Table 1.3: New timing parameters

All seven are runtime CSRs. `tZQinit`, `tZQoper` and `tZQCS` also gate command
issue alongside `tMRD`, `tMOD` and `tRFC` (JESD79-3F).

## Terms used with a specific meaning here

**Maintenance traffic**
Commands no host requested: refresh and ZQ calibration. Because it competes for
the command bus, it is the scheduler's concern and not only the sequencer's.

**Demand traffic**
Reads and writes originating from the AXI4 port.

**Prime DQ bit**
The DQ bit (or bits) carrying the write-leveling result back from the DRAM.

**Firmware-driven**
Performed by software over the CSR interface rather than by a hardware state
machine. Both PHY leveling on pumice's board and scoria's write-leveling search
are firmware-driven, deliberately.
