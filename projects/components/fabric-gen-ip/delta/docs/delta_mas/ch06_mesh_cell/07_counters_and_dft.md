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

# Observability Counters and DFT

> **IMPLEMENTED:** This chapter describes the `delta_mesh_cell` counter bank and DFT mode as built. The design is per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

## Ocelus Counter Bank

The cell exposes eleven 32-bit saturating counters through the config-read path. The counter bank is selected by setting `table_index[15] = 1`; indices 0..10 are defined and indices above 10 read back 0. Counters are frozen when `ENABLE_COUNTERS == 0` and clear on `aresetn`.

| Index | Name | What it counts |
|---|---|---|
| 0 | C_FLITS_IN | Flits received by the cell |
| 1 | C_FLITS_OUT | Flits transmitted by the cell |
| 2 | C_PKTS_IN | Packets received (`TLAST` handshakes) |
| 3 | C_PKTS_OUT | Packets transmitted (`TLAST` handshakes) |
| 4 | C_STALL_CYCLES | Output stall cycles |
| 5 | C_CREDIT_STALL | Cycles a granted output waited for downstream credit |
| 6 | C_ERR_DROP | Malformed-destination drops (mirrors `o_err_drop_cnt`) |
| 7 | C_MODE_ACKS | Broadcast mode-switch acks received (mirrors `o_mode_acks`) |
| 8 | C_BULK_STARVE | Cycles bulk reservation was due |
| 9 | C_SPEC_COMMITS | Speculative grants that committed |
| 10 | C_SPEC_REVOKES | Speculative grants that were revoked |

: Ocelus counter bank indices.

The suite is ahead of the NoC textbook literature, which says little about hardware observability, and is instead modeled on NPU practice [Q4][Q2][Q8].

## DFT Test Mode

DFT mode reconfigures each cell into one of three deterministic routing patterns so the mesh wiring behaves as a concatenated bus. Stuck-at and bridge faults become testable with approximately `ceil(log2(n))` patterns, where `n` is the number of cells in the fabric [N6]. The mode is entered through a DFT escape write on the config port (`table_index[15:12] = 4'hD`, payload bit 0 enables DFT, bits 2:1 select the pattern); each cell drives an `o_dft_active` output.

| Pattern | Routing behavior | Fault target |
|---|---|---|
| Pattern 0 | All cells route +X | Horizontal wiring |
| Pattern 1 | All cells route +Y | Vertical wiring |
| Pattern 2 | All cells route +Z | Depth wiring |

: DFT routing patterns

> **Design note:** DFT mode is mutually exclusive with normal traffic. The cell gates non-test flits while `test_active` is asserted; returning to normal mode requires a fabric-wide mode-switch sequence.

## References

- Jantsch & Tenhunen (eds.), *Networks on Chip*, Kluwer, 2003 — testing the communication infrastructure with three switch configurations [N6].
- Franklin et al. (eds.), *Network Processor Design: Issues and Practices, Vol. 1*, Morgan Kaufmann, 2002 — IXP2400 PMU, Toaster per-queue stats, Agere ASI RMON counters [Q4][Q2][Q8].
