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

# Verification Strategy

## Decision status

D10 is open but its direction is fixed in PRD v0.4. This chapter records the verification landscape as real content at 0.1 because the success criteria fix the proof obligations and the BFM family direction is concrete.

## Success criteria as verification exit criteria

The PRD success criteria become the verification plan's exit criteria:

1. **Three-block coherence.** Two `amber` instances (or `amber` + `jet`) plus `onyx` form a coherent system that passes the golden-model parity suite `amber` D9 defines.
2. **IHI 0022 conformance on the D2 subset.** A scoreboard checks AC/CR/CD behavior per transaction type; the CRRESP bits (`DataTransfer`, `IsShared`, `PassDirty`) of every gather are correct for the transaction and the caches' states.
3. **The serializer, proven.** Formal proofs of same-address serialization, no-deadlock under fair arbitration at N ∈ {2, 3, 4}, and a proven bound for the D4 response-gather mechanism.
4. **Observation.** Every D9 event class visible on MonBus in simulation and captured on at least one FPGA board.
5. **Cost.** Synthesis/implementation numbers (LUT/FF/RAM, fmax) on Nexys A7 and/or Genesys 2.

## Pattern-B cocotb

Tests follow the repo's Pattern-B cocotb gate/func/full structure. The testbench classes live under `bin/TBClasses/axi4ace/` per consumer.

## RDS-DV axi4ace BFM family

PRD D10 specifies a layered extension of the RDS-DV `axi4` BFM family:

1. **Field configs.** `AXI4ACEFieldConfigHelper` adds `ARSNOOP[3:0]` / `AWSNOOP[2:0]` to the AR/AW field configs.
2. **Signal-map patterns.** New `axi4ace_*` protocol patterns (framework-shipped vs user-loadable is a decision to make in RDS-DV).
3. **Transaction/packet layer.** The six D2 transaction types as an enum; `CRRESP` as a bitfield (`DataTransfer`, `Error`, `PassDirty`, `IsShared`, `WasUnique`).
4. **Four BFM classes:**
   - `AXI4ACEMasterRead` — subclass of the axi4 master-read BFM; drives coherent reads, with snoop type on commands; drives `RACK` when playing master against an onyx-port DUT.
   - `AXI4ACEMasterWrite` — subclass of the axi4 master-write BFM; drives coherent writes; drives `WACK` when playing master against an onyx-port DUT.
   - `AXI4ACESnoopSlave` — receives AC, drives CR/CD in issue order; programmable cache-state behavior producing the correct CRRESP; the golden-model hook that replays gem5 traces through `amber`.
   - `AXI4ACESnoopMaster` — drives AC, gathers CR/CD in order; drives onyx's fanout in DV.
5. **Compliance checker.** In-order CR/CD, no snoop to the requesting master, CD-before-CDLAST, CRRESP validity per snoop type.
6. **Main-repo TB classes** under `bin/TBClasses/axi4ace/` per consumer.

Build order: snoop-slave BFM first (amber's pair rig needs it), snoop-master BFM lands with onyx. RDS-DV implementation is tracked as RTLDesignSherpa-DV issue #86.

## Golden model

The Python reference model is derived from the gem5 Ruby `MESI_Two_Level` spec in `../../../References/gem5-ruby-protocols/`. It is phrased in messages rather than ACE signals, so the verification suite must map the ACE signal-level behavior to the message-level protocol.

## Formal proof obligations

SymbiYosys proofs target:

- **Same-address serialization.** No two same-address coherent transactions proceed incompatibly.
- **No-deadlock under fair arbitration at N ∈ {2, 3, 4}.**
- **D4 response-gather livelock bound.** A presumed-miss bound exists and is proven.
- **Named PRD scenarios:**
  - CU livelock absence at the PoS.
  - No WLU/WB-style deadlock in the fanout/gather path.
  - Fairness (no fixed-priority starvation) at N ∈ {2, 3, 4}.

WLU/WU scope growth is the N5 option; if N5 is promoted, the proof surface expands to include those transaction types.

## Informal cross-checks

`pulp-platform/culsans` (`ace_ccu_top` and the CVA6 coherent cache) is used as an informal cross-check, not an oracle. Its behavior is compared against the D2 subset and the in-repo ACE definition; discrepancies are resolved in favor of IHI 0022 and the PRD.

## What is open

D10 must close the BFM build order, compliance checker detail, and the exact directed-test matrix. The proof obligations listed above are fixed by success criterion 3.
