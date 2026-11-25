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

# Verification Hooks and Observability

peregrine carries no assertions in its RTL. Everything the TBs and the formal units check is observed at ports, through TB-only harness logic, or through properties spliced into a formal-only flat. The test list and results are in the HAS ("Verification Summary").

## Ports Built for Observation

| Port | Module | Used by |
|------|--------|---------|
| `rvfi_*` | core, top | Spike lockstep (pc, insn, trap kind and epc); the RVFI shadow register file; riscv-formal |
| `rvfi_trap_cause` | core, top | The trap directed suites: every trap's mcause against the expected cause |
| `rvfi_bp_pred_taken`, `rvfi_bp_pred_target`, `rvfi_bp_mispredict` | core, top | The predictor model check: every retired prediction held to the states pipeline timing allows, and the flag equal to "guess != outcome" |
| `dobs_valid`, `dobs_addr`, `dobs_wstrb`, `dobs_wdata` | top | The `tohost` detector on the cached build; the memory-side-effect count (accepted accesses against retired loads and stores) |
| `dc_clean_req`, `dc_clean_done` | top | `ArchSysTB` cleans amber after the `tohost` store, before reading the arch-test signature from memory |
| `tb_irq_software`, `tb_irq_timer` | top | The pin-driven interrupt suite on the cached build, and the aimed source of the `irq_lock` program |
| `mem_wait` | core | The cacheless TB drives random holds (the `mem_wait` variants) |

: Observation ports

## The Side-Effect Count

Every run counts data-memory requests (`dmem_req` on the cacheless TB, `dobs_valid` on the cached one) against loads and stores retired on RVFI. They must be equal: an interrupted or trapping access that still reached memory shows up as an extra request. The first mutant of TASK-001 (an interrupted load or store still accessing memory) gave 796 requests against 773 retired.

## TB Harnesses

| File (`dv/tb/`) | Wraps | Notes |
|-----------------|-------|-------|
| `peregrine_tb_top.sv` | `peregrine_core` at `CACHE_EN=0` | Behavioral word memory; combinational fetch read, registered data read gated by `dmem_req`; backdoor image load |
| `peregrine_sys_tb_top.sv` | `peregrine_top` | A behavioral AXI4 memory serving INCR bursts; the same port list as `peregrine_tb_top`; `RSP_SCRAMBLE` |
| `peregrine_axi4_arb_th.sv` | `peregrine_axi4_arb` | Three house AXI4 masters and one slave |

: peregrine TB harnesses

**`RSP_SCRAMBLE`** (parameter of `peregrine_sys_tb_top`, default 0; on in `test_peregrine_sys` and the cached `test_peregrine_arch` cells). amber keeps its last response on `cpu_rsp_rd_data`, so a wrapper that reads response data outside its valid cycle passes by luck. With the parameter set, the TB forces amber's whole response beat (`u_top.w_dc_rsp_data`) to an LFSR value on every cycle its valid is low, upstream of `peregrine_top`'s lane select, so every wrapper stage stays the RTL under test. In the valid cycle it passes amber's own value, re-derived from `l1_cpu_frontend`'s response mux because the port net itself is the forced one: **if amber's CPU-side response logic changes, that line in the TB must change with it.** A first version forced the lane-selected word instead, which replaced the lane mux and let the "response lane not selected" mutant survive.

## TB Classes and Models

Under `dv/tbclasses/peregrine/`: `peregrine_tb.py` and `peregrine_sys_tb.py` (run to `tohost`, the request contract, the side-effect count), `battery.py` (riscv-tests and spike lockstep), `bpred_model.py` (the predictor model with BHT counters as value sets), `predictor_streams.py` (the PRD §5 streams), `mext_program.py` (generated M hazard programs), and one class per block test.

## Waves

`dv/tests/GTKW/peregrine_tb_top` is the house GTKW save file for the cacheless TB, with a trap group.

## Formal Hooks

The formal units under `formal/peregrine/` use the ports above plus two splices that never reach a simulation or synthesis build:

- `peregrine_core_props.svh` and `peregrine_top_props.svh` are spliced into the sv2v flat of `peregrine_core` / `peregrine_top` by the unit's Makefile (no assertions in the RTL source). They see internal signals such as `ex_leaves` and `w_dhs`.
- `RISCV_FORMAL_ALTOPS` selects riscv-formal's stand-in M results in `peregrine_mdu`.

`top_props` replaces amber with a stub that has amber's CPU-port contract and drives a free response beat on every cycle, so a late read of held response data fails by construction.

---

**Last Updated:** 2026-11-25
