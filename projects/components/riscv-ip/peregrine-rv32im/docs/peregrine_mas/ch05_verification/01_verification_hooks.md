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

Every run counts data-memory requests (`dmem_req` on the cacheless TB, `dobs_valid` on the cached one) against loads and stores retired on RVFI, plus the load and store access faults (TASK-005: the one trap that did issue its request, the error being its response). They must be equal: an interrupted or trapping access that still reached memory shows up as an extra request. The first mutant of TASK-001 (an interrupted load or store still accessing memory) gave 796 requests against 773 retired.

## TB Harnesses

| File (`dv/tb/`) | Wraps | Notes |
|-----------------|-------|-------|
| `peregrine_tb_top.sv` | `peregrine_core` at `CACHE_EN=0` | Behavioral word memory; combinational fetch read, registered data read gated by `dmem_req`; backdoor image load |
| `peregrine_sys_tb_top.sv` | `peregrine_top` | A behavioral AXI4 memory serving INCR bursts; the same port list as `peregrine_tb_top`; `RSP_SCRAMBLE`; bus-error windows by address bits 27:24 (0xE DECERR, 0xD SLVERR, 0xC writes only SLVERR; TASK-005) |
| `peregrine_axi4_arb_th.sv` | `peregrine_axi4_arb` | Three house AXI4 masters and one slave |

: peregrine TB harnesses

**`RSP_SCRAMBLE`** (parameter of `peregrine_sys_tb_top`, default 0; on in `test_peregrine_sys` and the cached `test_peregrine_arch` cells). amber keeps its last response on `cpu_rsp_rd_data`, so a wrapper that reads response data outside its valid cycle passes by luck. With the parameter set, the TB forces amber's whole response beat (`u_top.w_dc_rsp_data`) to an LFSR value on every cycle its valid is low, upstream of `peregrine_top`'s lane select, so every wrapper stage stays the RTL under test. In the valid cycle it passes amber's own value, re-derived from `l1_cpu_frontend`'s response mux because the port net itself is the forced one: **if amber's CPU-side response logic changes, that line in the TB must change with it.** A first version forced the lane-selected word instead, which replaced the lane mux and let the "response lane not selected" mutant survive.

## TB Classes and Models

Under `dv/tbclasses/peregrine/`: `peregrine_tb.py` and `peregrine_sys_tb.py` (run to `tohost`, the request contract, the side-effect count), `battery.py` (riscv-tests and spike lockstep), `bpred_model.py` (the predictor model with BHT counters as value sets), `predictor_streams.py` (the PRD §5 streams), `mext_program.py` (generated M hazard programs), `csr_shadow.py` (the shadow trap-CSR model: `mepc`, `mcause`, `mtval` predicted from the trap beats and the CSR writes, and every CSR read of them held to it; TASK-005), and one class per block test. `battery.lockstep` also locks the `tval` of every access fault against spike, and matches an instruction access fault, which has no commit line in spike's log, against spike's exception record alone.

## Waves

`dv/tests/GTKW/peregrine_tb_top` is the house GTKW save file for the cacheless TB, with a trap group.

## Formal Hooks

The formal units under `formal/peregrine/` use the ports above plus two splices that never reach a simulation or synthesis build:

- `peregrine_core_props.svh` and `peregrine_top_props.svh` are spliced into the sv2v flat of `peregrine_core` / `peregrine_top` by the unit's Makefile (no assertions in the RTL source). They see internal signals such as `ex_leaves` and `w_dhs`.
- `RISCV_FORMAL_ALTOPS` selects riscv-formal's stand-in M results in `peregrine_mdu`.

`top_props` replaces amber with a stub that has amber's CPU-port contract and drives a free response beat on every cycle, so a late read of held response data fails by construction. Since TASK-005 the stub's error bit and write-back error status are free too, and so are the fabric slave's RRESP / BRESP: the D-side queue property then also requires that an access answered with an error retires as a load / store access fault of the right kind, and one answered OKAY never does.

---

**Last Updated:** 2026-11-27
