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

# scoria DDR3/LPDDR3 — Design Requirements

**Status:** delta analysis, pre-HAS. Decisions D1-D3 SETTLED 2026-09-29. This document is the foundation the HAS is
written from, not the HAS itself. Every claim below is either cited to a spec
clause or marked as an open decision.

**Method:** scoria inherits the pumice DDR2/LPDDR2 architecture and changes only
what DDR3/LPDDR3 and DFI v3.1 force. This document is therefore organised as a
*delta*: what is inherited unchanged, what changes, what is new, and what is
deliberately out of scope. `../../pumice-ddr2-lpddr2/docs/design-requirements.md`
is the parent document and its Coding Guidelines, gear-ratio rules, bus-width
relationships and enforcement summary apply here unchanged unless contradicted.

## Sources

| Source | Where | Used for |
|---|---|---|
| JESD79-3F (DDR3) | `cold_storage/MemorySpecs/DDR3_JESD79-3F-2.pdf`, 226 pp | commands, mode registers, timings |
| JESD209-3C (LPDDR3) | `cold_storage/MemorySpecs/LPDDR3_JESD209-3C.pdf`, 158 pp | CA encoding, per-bank refresh |
| DFI v3.1 | `dfi-specs/DDR_PHY_Interface_Specification_v3_1.pdf`, 141 pp | the PHY boundary |
| DFI v2.1.1 | `dfi-specs/DDR_PHY_Interface_Specification_v2_1_1.pdf`, 102 pp | what pumice built to, for the diff |

**Important:** the JEDEC PDFs live outside the repo on purpose. They are not
redistributable (`dfi-specs/ddr3/index.md` says so explicitly). Cite them by
clause; never copy one into the tree.

---

## 1. The DFI boundary: v2.1.1 to v3.1

Measured across the two specs: 126 distinct `dfi_*` signal names in v2.1.1,
151 in v3.1.

### 1.1 What does NOT change

**Multi-phase signalling carries over intact.** v2.1.1 enumerates phase
variants explicitly (`dfi_address_p0..p3`, `dfi_cs_n_p0..p3`, and so on);
v3.1 generalises to `_pN` (`dfi_address_pN`, `dfi_cs_n_pN`, `dfi_odt_pN`,
`dfi_bank_pN`) and shows `_p0`/`_p1` only as examples. The 1:4 frequency ratio
is still a defined mode (v3.1 §3.2.4, §3.3.4).

**Note:** a naive signal-name diff reports `dfi_address_p2`, `dfi_cs_n_p3` and
their siblings as *removed in v3.1*. They are not removed; the notation was
generalised. pumice's DFI layer runs at `DFI_RATE = 4` with per-phase signals
and that design point is unaffected. This is recorded because the diff is
misleading in exactly the direction that would cause a needless rewrite.

### 1.2 What changes, and matters for DDR3/LPDDR3

| Area | v2.1.1 | v3.1 | Why it matters here |
|---|---|---|---|
| Leveling | `dfi_rdlvl_mode`, `dfi_rdlvl_load`, `dfi_rdlvl_delay*`, `dfi_rdlvl_gate_mode`, `dfi_wrlvl_mode`, `dfi_wrlvl_load`, `dfi_wrlvl_delay*`, `dfi_{rd,wr}lvl_cs_n` | **all removed**; replaced by a per-CS request/ack scheme: `dfi_phylvl_req_cs_n`, `dfi_phylvl_ack_cs_n`, `dfi_phy_wrlvl_cs_n`, `dfi_phy_rdlvl_cs_n`, `dfi_phy_rdlvl_gate_cs_n`, plus `dfi_lvl_pattern` and `dfi_lvl_periodic` | DDR3 **adds write leveling**, so this is the one DFI change scoria cannot avoid |
| Low power | one `dfi_lp_req` | split into `dfi_lp_ctrl_req` and `dfi_lp_data_req` | power-down / self-refresh entry is a scoria feature (see §3.4) |
| Initialization | — | `dfi_init` | DDR3 adds a hardware reset (see §2.2) |
| Error reporting | `dfi_parity_error` | `dfi_error` + `dfi_error_info` | a wider error surface; mostly carries DDR4 CA-parity information |

### 1.3 What v3.1 adds that scoria does NOT need

The bulk of v3.1's growth is DDR4/LPDDR4-era and is **out of scope**:

- **DDR4 command encoding** — `dfi_act_n` (and phase variants), `dfi_bg`
  (bank group), `dfi_cid` (chip ID, for 3DS stacks). DDR3 has no dedicated
  ACT pin, no bank groups and no chip ID.
- **CA parity, CRC and alert** — `dfi_alert_n*`, `dfi_parity_in_p*`.
- **Data Bus Inversion** — `dfi_rddata_dbi*`.
- **CA training** — `dfi_calvl_*`, `dfi_ca_capture`, `dfi_phy_calvl_cs_n`.

**Open decision D1: is v3.1 the right target at all?** The README commits to
DFI v3.1, and this analysis supports it, but the honest summary is that v3.1's
*gain* for a DDR3/LPDDR3 controller is the leveling rework plus the low-power
split and `dfi_init` — everything else new is DDR4. Building to v2.1.1 and
adding write leveling by hand would reuse pumice's DFI layer more directly.
Recommendation: **stay with v3.1**, because the leveling interface is the part
scoria needs and the per-CS scheme is also what the later DDR4 controller will
want; paying it once here is cheaper than paying it twice.

---

## 2. DDR3 device deltas vs DDR2

### 2.1 Mode registers

DDR3 defines **MR0, MR1, MR2 and MR3** — a clean four-register set. DDR2 used
MR0 through MR2 plus an EMRS3. The init sequencer's MR programming order is
therefore a rewrite rather than an edit, and the pumice lesson applies: the
order is JEDEC's, not ours.

### 2.2 New commands

| Command | What it is | Controller impact |
|---|---|---|
| `ZQCL` / `ZQCS` | ZQ calibration, long and short | new command encodings, plus a *scheduling* problem — see §3.5 |
| `RESET` | DDR3 adds a hardware `RESET#` pin | the init sequencer must drive a pin, not only issue commands |
| `PREA` | precharge all banks | an explicit encoding where DDR2 used PRE with A10 |
| `SRE` / `SRX` | self-refresh entry / exit | pairs with the DFI low-power split (§1.2) |

### 2.3 Write leveling

DDR3 adds write leveling, with its own timing parameters. From JESD79-3F:

| Parameter | Spec minimum | Meaning |
|---|---|---|
| `tWLMRD` | 40 nCK | controller must wait this long after entering write-leveling mode before driving the first DQS pulse. Its **maximum is controller-dependent** -- the spec declines to bound it, so it is ours to define |
| `tWLDQSEN` | 25 nCK | delay after which the controller may drive DQS low / DQS# high, by which point the DRAM has applied on-die termination to those signals |
| `tWLO` | per speed bin | write-leveling output delay: the DRAM returns the leveling result on the prime DQ bit(s) asynchronously, this long after the DQS edge |
| `tWLOE` | per speed bin | DQ output uncertainty, defined to allow mismatch across DQ bits. Matters if the controller samples more than the prime DQ bit |

Values other than the two `nCK` minimums are per speed bin in JESD79-3F's
timing tables; they belong in the CSR derivation, not restated here.

**Open decision D2: who owns the write-leveling procedure?** pumice
deliberately keeps PHY responsibilities out of the controller — the Nexys A7
board levels the PHY from *firmware*, over a CSR passthrough, with no hardware
leveling FSM. DDR3 write leveling is a device-and-PHY cooperative procedure
driven through MR1, and DFI v3.1 gives it a request/ack interface. Two options:

1. **Firmware-driven, as pumice does.** The controller exposes the DFI leveling
   request/ack and the MR1 writes; a host or boot sequence runs the algorithm.
   Keeps the controller free of PHY-specific search logic.
2. **Hardware FSM in the controller.** Self-contained, no host needed, but
   imports a calibration search into an IP block that has so far refused one.

Recommendation: **option 1**, for consistency with the family boundary, with the
DFI leveling signals exposed and a `*_STATS` surface so the search is
observable. This needs your call before the HAS fixes it.

### 2.4 Timings

ZQ adds `tZQinit` (init calibration), `tZQoper` (a long calibration outside init) and `tZQCS` (the short periodic one) -- all three confirmed present in JESD79-3F, and all three gate command issue alongside `tMRD`, `tMOD` and `tRFC`. The pumice rule carries over
unchanged and is worth restating because it was learned the hard way: **every
enforced timing is a runtime CSR**, not a parameter, and the derivation is
anchored on measurement rather than on a formula that happens to match one
point.

---

## 3. What scoria inherits from pumice

### 3.1 Inherited unchanged

The AXI4 front end (1:1 intakes, write-data and read-reorder CAMs, in-order
commit), the FSM-free split/aggregate, the scheduler layer (FR-FCFS arbitration,
open-page bank timers, the command stream into a FIFO), the read return ring,
the DFI datapath shape (one async-FIFO CDC, bubble-free, unit = a DFI word),
and the PeakRDL CSR discipline.

### 3.2 The package question

**Open decision D3: fork the package or share a family package?**
`pumice_pkg::memtype_e` is a **1-bit** enum (`MEMTYPE_DDR2 = 1'b0`,
`MEMTYPE_LPDDR2 = 1'b1`). A DDR3/LPDDR3 pair cannot be added to it without
widening the field, which touches pumice's RTL and its CSR.

pumice was written with this coming: `pumice_pkg.sv` pads the row field to
18 bits with the comment "DDR3 forward-compat". So the intent was a family, but
the memtype encoding was not widened to match.

Options: (a) scoria gets its own `scoria_pkg` with a 1-bit
`{DDR3, LPDDR3}` enum, duplicating the structure; (b) a shared
`mem_ctrl_pkg` with a 2-bit memtype covering all four, which pumice migrates to.
Recommendation: **(a) now, (b) when the DDR4 controller starts** — two members
is not yet a family, and widening pumice's CSR for a controller with no RTL
would change a measured, shipping design for a speculative benefit.

### 3.3 LPDDR3 comes almost free

JESD209-3C confirms the README's claim: LPDDR3 uses **CA0–CA9, a 10-bit
double-data-rate command/address bus** — the same encoding shape as LPDDR2. So
the LPDDR3 side is a timing and mode-register change, not a protocol break, and
pumice's LPDDR2 CA path is the starting point.

### 3.4 Per-bank refresh

JESD209-3C carries per-bank refresh (`REFpb`). scoria TASK-001 already records
that REFpb round-robin is the only per-bank scheme that is commodity at this
tier, and that the model-only schemes (out-of-order per-bank refresh,
write-refresh parallelisation, refresh pausing, SARP/DSARP) belong to the DDR4
area instead. That split stands.

### 3.5 ZQ calibration is a scheduling problem

Periodic `ZQCS` is maintenance traffic that has to be interleaved with demand
traffic, which makes it the scheduler's business and not just the init
sequencer's. TASK-001 lists it as a candidate selectable mode. The requirement
here is narrower: the baseline must be able to issue periodic ZQCS *at all*,
with the interval as a runtime CSR, before any cleverness about when.

---

## 4. Out of scope

- The PHY. DFI is the boundary, as it is for pumice.
- Board bring-up. Verification is against a DFI BFM in simulation; the board
  decision is deferred (Sean, 2026-09-29).
- Multi-rank beyond what pumice already parameterises.
- The DDR4/LPDDR4 DFI features listed in §1.3.

---

## 5. Open decisions, collected

All three were settled as recommended (Sean, 2026-09-29: "D1-3 all look good").
They are now binding on the HAS, not open questions.

| ID | Decision | Settled as |
|---|---|---|
| D1 | DFI revision | **v3.1.** The leveling rework is the part scoria needs, and the per-CS scheme is what the later DDR4 controller will want; paying it once here beats paying it twice. The DDR4/LPDDR4 surface of v3.1 (§1.3) stays unimplemented. |
| D2 | Write leveling ownership | **Firmware-driven.** The controller exposes the DFI leveling request/ack and the MR1 writes; the search algorithm runs off-chip. No hardware calibration FSM, matching pumice, whose board levels from firmware over a CSR passthrough. A `*_STATS` surface makes the search observable. |
| D3 | Package | **Own `scoria_pkg` now**, a shared `mem_ctrl_pkg` when the DDR4 controller starts. Two members is not yet a family, and widening pumice's 1-bit `memtype_e` would change a measured, shipping CSR for a controller with no RTL. |

**Consequence of D2 worth stating once:** because leveling is firmware-driven,
the HAS specifies an *interface and a procedure*, not a state machine. What
scoria owes the system is the DFI leveling handshake, the MR1 write path, the
timing windows (`tWLMRD` through `tWLOE`) enforced as runtime CSRs, and enough
telemetry to see the search converge. What it must not contain is a tap-search
loop.
