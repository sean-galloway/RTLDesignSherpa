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

# Scope and Goals

## High-Level Goals

This controller provides a single parameterized RTL implementation supporting both DDR2 and LPDDR2 memory devices via DFI v2.1. Primary design goals:

1. **Unified engine, swappable encoder.** DDR2 and LPDDR2 differ only at the wire-encoding layer (ras/cas/we vs CA bus); the bank machines, scheduler, refresh policy, init engine, and AXI frontend are shared between both targets.
2. **Embedded / mobile / mid-range SoC targets.** Not optimized for high-end server DRAM (DDR5, RDIMM, multi-rank). Optimized for power efficiency and area economy.
3. **Characterization-first parameterization.** Algorithmic choices with research-backed alternatives are exposed as build-time parameters so the design can be swept on real workloads before defaults are locked.
4. **Verification-friendly.** Mirrors the data structures and conventions of the DDR2 / LPDDR2 DFI BFM in the DV repository so the same address mapping, timing parameters, and command encodings can drive both RTL and simulation.

---

## In Scope

The following features are explicitly within scope for this controller:

- **AXI4 slave** with 64 / 128 / 256-bit data width, 1–16-bit ID width, INCR burst type
- **DFI v2.1 master** driving the command, write-data, and read-data sub-interfaces
- **APB CSR slave** for configuration and observation
- **DDR2 and LPDDR2 device support** via `MEMTYPE` build parameter
- **DFI frequency ratio** (gear) of 1, 2, or 4 phases via `N_PHASES` parameter
- **Multi-rank operation** — 1, 2, or 4 ranks via `NUM_RANKS` parameter; per-rank `CS_n`, `CKE`, `ODT`, and refresh tracking; rank-aware ODT cross-termination rules per JEDEC
- **Page policies:** OPEN, CLOSE, HAPPY hybrid predictor (parameterized)
- **Per-bank refresh** for LPDDR2 with DARP-style scheduling (parameterized)
- **All-bank refresh** for DDR2 (and as LPDDR2 fallback)
- **Elastic refresh deferral** up to JEDEC ceiling of 8× tREFI (parameterized)
- **Partial-array self-refresh (PASR)** for LPDDR2 with CSR-configurable mask
- **Temperature-compensated refresh** (LPDDR2 MR4 derating)
- **Cold-boot initialization** via microprogram step tables
- **Power state management** (Active, Active Power-Down, Self-Refresh, Deep Power Down)
- **Bring-up observability** via CSR-exposed counters (row-hit rate, refresh latency, queue depth)

---

## Out of Scope

Explicitly **not** addressed in this controller version:

| Feature                       | Reason                                                       |
|-------------------------------|--------------------------------------------------------------|
| Inline ECC                    | Out-of-controller responsibility (SoC sideband)              |
| DFI training sub-interface    | Not required for v2.1 DDR2 / LPDDR2 operation                |
| DFI frequency-change protocol | No use case for this generation                              |
| DFI low-power sub-interface   | Power-state FSM uses CKE only                                |
| AXI exclusive accesses        | Embedded targets don't require                               |
| Bank groups                   | Not present in DDR2 / LPDDR2 (introduced in DDR4 / LPDDR4)   |
| Command/Address parity        | Not present in DDR2 / LPDDR2 (introduced in DDR4 / LPDDR4)   |
| Write CRC                     | Not present in DDR2 / LPDDR2                                 |
| Data Bus Inversion (DBI)      | Not present in DDR2 / LPDDR2                                 |
| DDR3 write leveling           | Not present in DDR2 / LPDDR2 (LPDDR3 introduces)             |
| DDR3 ZQCS / ZQCL on column   | DDR2 uses OCD calibration; LPDDR2 uses MR10 ZQ               |
| Higher DDR / LPDDR generations | Will be addressed in DDR3-LPDDR3 and DDR4-LPDDR4 controllers |

---

## Target Performance Envelope

| Metric                          | Target                                    |
|---------------------------------|-------------------------------------------|
| DRAM data rate                  | Up to DDR2-800 / LPDDR2-1066              |
| AXI clock                       | Up to 200 MHz (typical embedded SoC)      |
| Sustained read bandwidth        | ≥ 70% peak on stream workloads            |
| 99th-percentile read latency    | ≤ 200 ns (typical)                        |
| Refresh blocking overhead       | < 5% (LPDDR2 with DARP); < 8% (DDR2)      |
| Area                            | < 50K gates (excluding HAPPY predictor)   |

These are target envelopes for v1; not guarantees. They will be validated and refined during the characterization sweep.

---

## Differentiating Features

This controller is informed by published memory-controller literature and the open-source memory-controller ecosystem (LiteDRAM in particular — used as the cross-validation reference; see §6.4), but it is not a re-implementation of any existing controller. The design's distinguishing features:

1. **Centralized FR-FCFS scheduler with full out-of-order issue.** A single scheduler scans the full transaction queue every cycle, considering all banks' readiness and row-hit state in one decision. This is closer to the commercial-vendor pattern (Synopsys, Cadence, Xilinx MIG) than to most open-source RTL controllers — open-source controllers typically expose OoO only at the cross-bank level (a per-bank FIFO model where bank parallelism is the only source of reordering). True per-port within-stream reordering — where a younger row-hit request bypasses an older row-conflict request — is uncommon outside vendor IP. AXI4 per-ID ordering is honored at the response side regardless. **For real-time / safety-critical / formally-verifiable systems**, OoO reordering can be disabled at build time via `SCHEDULER_MODE = INORDER` (§3.2); the scheduler degrades to a first-ready FIFO that preserves arrival order at the cost of 10–25% sustained bandwidth on streaming workloads.

2. **Multi-rank support with JEDEC-compliant cross-rank ODT.** Most open-source DDR2/3 controllers are single-rank only — LiteDRAM's default config, UberDDR3, and most academic prototypes assume one rank per channel. This controller supports 1, 2, or 4 ranks via the `NUM_RANKS` build parameter. Per-rank `CS_n`, `CKE`, and `ODT` signals are driven; the rank-aware refresh manager tracks `last_ref_age` per (rank, bank); and the cross-rank ODT termination rules (read from rank N → ODT-high on rank ≠N during the read window; write to rank N → ODT-high on rank N during the write window) are handled by an ODT-control sub-module per JESD79-2 §x.y. Multi-rank is what makes the controller usable on real DIMM-class platforms rather than just on-board point-to-point DRAM.

3. **Unified DDR2 + LPDDR2 engine with a swappable command encoder.** A single controller core supports both memtypes via the `MEMTYPE` build parameter. The LPDDR2 path includes the 20-bit CA bus encoder (DFI v2.1 §3.1 Table 1), PASR mask handling (MR16/17), per-bank refresh (REFpb), temperature-compensated refresh (MR4 derating), and Deep Power Down — none of which are present in the open-source DDR2/3/4 reference controllers.

4. **DARP-style per-bank refresh scheduling** — picks the *idle* bank with the longest time since last refresh, falling back to oldest-first when no banks are idle. Based on Chang et al. (HPCA 2014); not present in available open-source controllers.

5. **Two-stage page management** — exact lookahead first, history-based fallback second.
   - Stage 1: lookahead window over the transaction queue (`LOOKAHEAD_DEPTH ∈ {0, 1, 2, 4}`) provides exact auto-precharge decisions when the next same-bank request is already queued.
   - Stage 2: when lookahead is inconclusive (shallow queue or bursty traffic), the HAPPY hybrid page predictor (Ghasempour et al. 2015) uses address-bit-hashed saturating counters to predict the next access.
   Open-source controllers typically have either lookahead OR a fixed page policy. The two-stage combination is original to this design.

6. **Characterization-first parameterization.** Page policy, lookahead depth, refresh policy, refresh deferral, queue depth, address mapping scheme, and HAPPY table size are all build-time parameters with a defined sweep matrix (see §5 and §6.4). Most published controllers expose only a subset of these as parameters; few expose them all.

7. **Closed-page policy as an explicit option.** `PAGE_POLICY ∈ {OPEN, CLOSE, HAPPY_HYBRID}`. Most open-source controllers expose only on/off auto-precharge (effectively OPEN with optional lookahead). The CLOSE option is useful for adversarial / security-sensitive workloads where row-state side channels matter.

8. **Three-scheme parameterized address mapping** — `ADDR_MAP_SCHEME ∈ {ROW_MAJOR, BANK_INTERLEAVE, XOR_HASH}`. The XOR_HASH scheme defeats pathological row-conflict patterns and is rarely available out-of-the-box.

9. **AXI4-first frontend** with ID-aware out-of-order completion. The AXI integration is a first-class design constraint rather than a wrapper on a native protocol.

10. **Mirrored verification address-mapping object.** The `addr_mapper` mirrors a Python `AddressMapping` class used by the DFI BFM, so the same mapping function drives both RTL elaboration and simulation. This eliminates a common source of address-decode bugs between RTL and verification.

### Features Adopted from Standard Memory-Controller Patterns

These design patterns are widespread in the memory-controller literature and the open-source controllers we examined. Adopting them is the right call; they are noted here so the design rationale is transparent:

- **Per-bank state machines with local timing enforcement** + central cross-bank timer pool (tRRD / tFAW / tWTR / tCCD) — standard.
- **FR-FCFS scheduler baseline** (Rixner et al. ISCA 2000) — the academic baseline.
- **Elastic Refresh deferral** (Stuecheli et al. MICRO 2010) — postponer with deterministic back-to-back drain.
- **Refresh-grant handshake** (`refresh_req` / `refresh_gnt`) between refresh manager and bank machines — established pattern.
- **Periodic ZQCS piggybacked on the refresh window** — established pattern for systems with thermal drift.
- **Microprogram-driven init engine** with per-memtype step-table ROMs — established pattern.

The design rationale for adopting versus extending each is documented in the relevant section.
