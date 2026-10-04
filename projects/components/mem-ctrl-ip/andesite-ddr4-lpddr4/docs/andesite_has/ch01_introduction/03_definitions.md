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
The host-side slave interface. Inherited from scoria unchanged, including the
width-gearing converters that let the host bus width differ from the DRAM's.

**DFI**
DDR PHY Interface. andesite targets **v4.0** — the DDR4-era revision that
adds `dfi_act_n`, the gear-down handshake, CA parity and `dfi_alert_n`, and
the DBI wires. Clause citations carry `§TBC(TASK-005)` until the spec is on
disk.

**APB**
The CSR access interface, through a PeakRDL-generated register block.

## DRAM commands this document refers to

| Command | In scoria's DDR3/LPDDR3? | Note |
|---|---|---|
| `ACT`, `RD`, `WR`, `PRE`, `REF`, `MRS`, `ZQCS`/`ZQCL`, `SRE`/`SRX` | yes | inherited handling; encoding moves to the ACT_n/BG form |
| `RDA` / `WRA` | yes | read/write with auto-precharge |
| `PREA` | yes | precharge-all; DDR4 keeps its own encoding |
| `REF` 1x/2x/4x | 1x only | fine-granularity refresh, selected in MR3 |
| `MRS` target set | MR0-MR3 (DDR3), MR0-MR11 (LPDDR3) | DDR4: MR0-MR6; LPDDR4: MR0-MR22 (used subset in Ch 3.2) |
| `MPC` | **no** | LPDDR4 multipurpose command — ZQ, training, and more over the CA bus |
| gear-down entry | **no** | DDR4 1/2-rate CA bus mode, entered after init |
| parity-aware commands | **no** | DDR4 CA parity; a parity error raises `alert_n` |

: Table 1.2: Commands, and which are new to this family member

## Terms new to andesite

**Bank group**
DDR4's partition of its 16 banks into 4 bank groups of 4 banks. Bank groups
exist to relax same-bank timing constraints: back-to-back commands to
different bank groups of the same bank number observe the short constraints,
and same-group observe the long ones. LPDDR4 has no bank groups — its 8 banks
per channel stand alone.

| Parameter | Governs |
|---|---|
| `tCCD_L` / `tCCD_S` | CAS-to-CAS delay: long, within one bank group; short, across bank groups |
| `tRRD_L` / `tRRD_S` | ACT-to-ACT delay, same split: long within a bank group, short across |

: Table 1.3: The long/short timing pairs bank groups introduce

Both pairs are runtime CSRs, like every other timing.

**Fine-Granularity Refresh (FGR)**
DDR4's choice of refresh density, 1x/2x/4x, selected in MR3 (JESD79-4). 1x is
scoria's inherited all-bank refresh; 2x and 4x trade more frequent, shorter
refresh bursts against the tREFI budget. andesite's `refresh_ctrl` is MODIFIED
to carry the selection; scoria's landed TASK-001 modes (elastic refresh, TCR,
ZQCS placement) remain the policy base.

**Gear-down**
DDR4's 1/2-rate command/address bus mode. The controller inits at full rate,
programs MR3, then switches; DFI v4.0 defines the controller/PHY handshake for
the switch `§TBC(TASK-005)`.

**CA parity**
DDR4 command/address parity. The controller counts commands and checks parity
on the DRAM's behalf of the bus; a parity error is signalled back on
`dfi_alert_n`. How much of the parity machinery lands in hardware versus
firmware is an open question (Chapter 6).

**DBI (Data Bus Inversion)**
Per-byte inversion of the data bus to limit switching. DDR4 puts read DBI in
MR5 with write DBI alongside; DFI v4.0 carries `dfi_dbi_*` wires
`§TBC(TASK-005)`. The DFI datapath block is MODIFIED to pass DBI through.

**MPC (Multipurpose Command)**
LPDDR4's single command opcode that carries what DDR4 spreads across several:
ZQ calibration, training steps, and feature mode entry, all addressed over the
6-bit CA bus (JESD209-4). andesite's `zq_ctrl` grows a NEW MPC path for it.

**Controller-directed refresh (LPDDR4)**
LPDDR4's per-bank refresh is directed by the controller — the controller
names the bank, unlike DDR4's FGR where the DRAM refreshes what it chooses
inside the all-bank command. scoria already handles per-bank refresh for
LPDDR3; the LPDDR4 delta is that per-bank becomes the commodity default, not
the option.

## Terms used with a specific meaning here

**Maintenance traffic**
Commands no host requested: refresh and ZQ calibration. Because it competes
for the command bus, it is the scheduler's concern and not only the
sequencer's. The family doctrine binds how it arbitrates: request/grant, and
it never preempts demand traffic.

**Demand traffic**
Reads and writes originating from the AXI4 port.

**Firmware-driven**
Performed by software over the CSR interface rather than by a hardware state
machine. scoria's write-leveling search is firmware-driven; andesite's read
leveling and LPDDR4 CA/WDQ training follow it, per the D2 precedent.
