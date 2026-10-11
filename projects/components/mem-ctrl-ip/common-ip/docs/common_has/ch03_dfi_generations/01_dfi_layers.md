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

# Why `dfi_2p1_layer` / `dfi_3p1_layer` / `dfi_4p0_layer` Are Separate Blocks

The DFI boundary layers are named for the DFI revision they implement —
`mc_dfi_2p1_layer`, `mc_dfi_3p1_layer`, `mc_dfi_4p0_layer` — and the naming
is deliberate: **the DFI revision is a family boundary, not a parameter.**
This chapter says why, and what is shared underneath.

## The reasoning

A controller's DFI revision is decided by the memory generation it serves
(DDR2/LPDDR2 → DFI 2.1, DDR3/LPDDR3 → DFI 3.1, DDR4/LPDDR4 → DFI 4.0) and
by the PHY it must talk to. It is not something a single bitstream flips at
runtime, and — per the parameter-sustainability doctrine (Ch 4) — a
parameter that changes protocol generation fails the test: the legal
combinations explode, and the DV cost is per-generation anyway. So each
revision is its own named block, a product picks exactly one, and the
product line maps one-to-one: granite → `dfi_2p1_layer`, gabbro →
`dfi_3p1_layer`, diorite → `dfi_4p0_layer`.

The parameter-sustainability rule applies *within* a generation: widths,
phase counts, FIFO depths are parameters; the protocol generation is not.

## What is shared

The blocks share the pipeline that is revision-independent, extracted once
as common FUBs and instantiated by whichever generation layer needs them:

| Shared FUB | Role |
|---|---|
| `mc_dfi_cdc` | the single `aclk` ↔ `dfi_clk` crossing (async FIFOs + init handshake) |
| `mc_dfi_cmd_path` | command pipeline from scheduler to formatter |
| `mc_dfi_wr_serializer` | write-data packing/serialization to the DFI bus |
| `mc_dfi_rd_aligner` | read-data capture/alignment from the DFI bus |

The revision-specific part is the command encoding and control surface: the
2.1 formatter, the 3.1 command path, the 4.0 command path (ACT_n, gear-down,
CA parity/alert_n, DBI). Those are the per-generation FUBs
(`mc_dfi_3p1_cmd_path`, `mc_dfi_4p0_cmd_path`) — and the reason the layer
exists at all is that the *combination* of shared pipeline plus generation
command surface is what a product instantiates.

The full clause-level lineage is
[03_dfi_boundary_lineage.md](../../03_dfi_boundary_lineage.md) and the
simplified-spec books; the per-layer microarchitecture is
[common_mas](../../common_mas/common_mas_index.md) ch7–ch9. This chapter fixes
only the naming and the family-boundary rule.

## What the layer never does

Per the family boundary doctrine, the DFI layer never absorbs PHY
responsibilities: no training search, no calibration algorithm, no IO
timing closure. The training layer speaks *to* the DFI layer through the
documented CSR/contract surface ([phy_cal_csr_contract.md](../../phy_cal_csr_contract.md));
the PHY owns the mechanism. A DFI layer that starts calibrating is the
boundary doctrine's defect case, and the review that catches it is this
chapter's reason for existing.
