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

# peregrine_hazard

**Module:** `peregrine_hazard.sv`

## Responsibility

merlin's forwarding and load-use unit, unchanged: purely combinational, no clock or reset.

## Ports

<!-- GEN:ports:peregrine_hazard -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `id_rs1_addr` | input | `[4:0]` | ID rs1 (load-use check) |
| `id_rs2_addr` | input | `[4:0]` | ID rs2 (load-use check) |
| `fwd_rs1_addr` | input | `[4:0]` | rs1 compared for forwarding |
| `fwd_rs2_addr` | input | `[4:0]` | rs2 compared for forwarding |
| `idex_rd_addr` | input | `[4:0]` | rd of the instruction in EX |
| `idex_is_load` | input | `1` | The instruction in EX is a valid load |
| `exmem_rd_addr` | input | `[4:0]` | Producer for the EX/MEM arm |
| `exmem_rd_wen` | input | `1` | Its write enable |
| `memwb_rd_addr` | input | `[4:0]` | Producer for the MEM/WB arm |
| `memwb_rd_wen` | input | `1` | Its write enable |
| `ex_flush` | input | `1` | EX redirect (mispredict) |
| `fwd_a` | output | `[1:0]` | rs1 forwarding select (FWD_*) |
| `fwd_b` | output | `[1:0]` | rs2 forwarding select (FWD_*) |
| `stall_ifid` | output | `1` | Load-use stall |
| `flush_ifid` | output | `1` | EX redirect flush of IF/ID |
| `flush_idex` | output | `1` | EX redirect flush of ID/EX |

: peregrine_hazard ports

<!-- /GEN -->

## Behavior

- **Forwarding select**, per source: `FWD_EXMEM` if the EX/MEM-arm producer writes that register, else `FWD_MEMWB` if the MEM/WB-arm producer does, else `FWD_IDEX` (the value read in ID). x0 never forwards.
- **Load-use:** `stall_ifid` when the instruction in EX is a valid load whose `rd` (not x0) matches either ID source.
- **Flush:** `flush_ifid = flush_idex = ex_flush`.

The core drives the producer inputs one stage early: the ID sources against the instructions now in ID/EX and EX/MEM, which are the ones that will be in EX/MEM and MEM/WB when the consumer reaches EX. It registers `fwd_a` / `fwd_b` beside ID/EX, so EX's forwarding mux selects from a flop.

---

**Last Updated:** 2026-11-25
