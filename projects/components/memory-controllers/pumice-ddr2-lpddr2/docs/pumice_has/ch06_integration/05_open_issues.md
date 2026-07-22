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

# Open Issues and TODOs

Items where design choices were made provisionally and should be reviewed before the HAS is promoted to formal status.

## Open Issues

### 1. AXI4 Narrow-Burst Handling Confirmation

AXI4 allows narrow transfers (data width less than bus width). The current plan is to handle them via byte-mask through `wrdata_mask`. **Confirm** the wstrb-to-wrdata-mask wiring honors the AXI partial-write semantics correctly, particularly for unaligned bursts.

### 2. AXI4 Read-Modify-Write Strobe Handling

Partial writes in DDR2 / LPDDR2 use `wrdata_mask` to mask byte lanes; this is straightforward. **Confirm** that per-byte masking is wired all the way through the write path (`pumice_wr_intake` -> `pumice_wr_data_cam` -> `pumice_dfi_wr_serializer`) and that `pumice_wr_intake` doesn't widen narrow writes implicitly.

### 3. CSR Address Space Allocation

The config bus is a PeakRDL passthrough cpuif on `aclk` (no APB slave, no separate `apb_pclk`). `CSR_ADDR_W = 12` provides a 4 KB register region. **Confirm** the SoC's address-map allocation has at least 4 KB available for the cpuif window, and that there's no conflict with adjacent peripherals.

### 4. Per-Bank Refresh Book-Keeping Cost

Keeping `last_ref_age` per bank costs one counter per bank. For 8 banks this is 8 small counters. **Confirm** the synthesis area impact is acceptable; we expect ~200 LUTs for the per-bank refresh tracking on a typical FPGA.

### 5. HAPPY Predictor Hash Function

Ghasempour 2015 suggests bank-XOR-low-row-bits as the hash function. **Confirm** with our typical workloads. If the workloads have systematic bank-row correlations, a different hash may be needed.

### 6. Self-Refresh Exit Latency

JESD79-2 requires `tXSNR` (~200 ns) before any command after SR exit. **Confirm** the optional `powerdown_ctrl` enforces this correctly and that the scheduler is gated for the full duration.

### 7. Init Sequencer Retry on Error

If ZQ fails, do we retry up to 3 times then halt, or just halt? Current plan: 3 retries (parameter `INIT_ZQ_RETRIES`) then raise `init_error`. **Confirm** with the system architect — some systems prefer fail-fast. (Note: DDR2 ZQ init differs from LPDDR2 — `init_sequencer` handles both JEDEC sequences.)

### 8. CSR Write Atomicity

Multi-register parameter changes (e.g., updating both `MR0` and a related timing) need a "config quiet period" to take effect atomically. Today the SoC owns the drain: software is expected to quiesce AXI traffic before reprogramming timing/mode CSRs. A dedicated `config_apply` strobe (hardware-enforced quiet period) is **not implemented** and is a possible future addition. **Document** the software drain protocol regardless.

### 9. Burst Splitting at Row Boundaries

AXI4 allows up to 256 beats per burst; a DRAM row contains `2^COL_WIDTH` columns. Burst splitting into fixed-BL commands happens in `pumice_wr_intake` / `pumice_rd_intake`. **Confirm** the split logic correctly tracks partial-burst completion for ID-based ordering.

### 10. Multi-Rank

Multi-rank scaffolding now exists: `NUM_RANKS` is a real build parameter (default 1), the DFI `dfi_cs_n_o` / `dfi_odt_o` buses are per-rank (width `NUM_RANKS * DFI_RATE`), and `addr_mapper` carries a rank field (`rank_o`) at the top of the address stack. The command path and bank timers are stamped per (rank, bank). **Remaining gap**: per-rank refresh coordination, PASR (partial-array self-refresh), and per-rank observation registers are not yet implemented. **Confirm** the multi-rank data path with a `NUM_RANKS > 1` build before relying on it.

### 11. ECC

Out of scope for this controller. ECC is expected to be handled at the SoC level or in a sideband wrapper, not the controller itself.

### 12. DFI Training Sub-Interface

Not driven in v1; the assumption is that the PHY handles its own training or training is not required for this DDR2 / LPDDR2 target. **Confirm** with the PHY vendor before silicon tape-out.

### 13. AXI Quality of Service (QoS)

Currently the `awqos` / `arqos` fields are forwarded to the scheduler as priority hints, but the scheduler does not implement explicit QoS classes. **Decide** whether to add proper QoS support (multi-class scheduler) or leave QoS as a future enhancement.

### 14. Multi-Master AXI

Currently single AXI port. **Decide** whether to add a multi-port AXI crossbar internally (simplifies SoC integration but adds area) or leave as a single-port with the SoC responsible for AXI arbitration upstream.

### 15. Observation Counter Overflow

Observation counters (row-hit, queue depth max, etc.) are 32-bit. At high traffic rates they could wrap. **Decide** on overflow handling: saturate, clear-on-read, or rely on SoC reading frequently.

### 16. Retired-Architecture Modules Still on Disk (`OLD/`)

The pre-rearchitecture modules still live under `rtl/fub/OLD/`, `rtl/macro/OLD/`, and `rtl/top/OLD/` (e.g. `scheduler.sv`, `wr_cmd_cam.sv`, `rd_cmd_cam.sv`, `xbank_timers.sv`, `axi_intake.sv`, the `*_macro.sv` blocks, `pumice_csr_slave.sv`). They are referenced only by retired sentinel tests in `dv/tests/` (`test_scheduler.py`, `test_wr_cmd_cam.py`, `test_xbank_timers.py`, `test_axi_intake.py`, and the `*_macro` tests). **Remove** the `OLD/` trees and their sentinel tests once the new architecture is fully signed off, so the live module set is the only thing that builds.

### 17. Open-Page Read-Fetches-Zero Under Gapped Reads

A known scheduler/CAM interaction: under open-page policy with gapped read traffic, a read can be fetched before its data is valid (returns zero) in a narrow timing window (reproduces at `PUMICE_SEED=2`, the burst-pause / hit-miss-oscillation pattern). **Root-cause and fix** the read-fetch gating in the open-page path before promoting the HAS to formal status. The `r_fdone` fill-complete gating in the CAMs is the relevant mechanism.

## TODOs Before v0.2

- Add bit-level pinout tables for the AXI, DFI, and cpuif (register) interfaces
- Add timing diagrams for the WR / RD command issue, including CWL / CL alignment
- Add sequence diagrams for `init_sequencer` (DDR2 and LPDDR2 MR init) and, where present, the optional `powerdown_ctrl`; document the FSM-free `bank_timer` countdown timers rather than an FSM diagram
- Add a draft of the Verilog package skeletons for `ddr2_init_steps_pkg.sv` and `lpddr2_init_steps_pkg.sv`
- Cross-reference each section to the corresponding pre-aspec.md bullet
- Add quantitative area / power estimates per module (synthesis pass needed)
- Add waveform examples for the canonical init sequences

## Feature Roadmap — planned advanced modes (ordered)

The full catalog of planned, config-bit-selectable advanced modes lives in
`docs/design-requirements.md` ("Advanced modes — selectable scheduling /
paging / refresh"); the family-level split (commodity-legal here vs
model-only parked for DDR3/DDR4) is in
`projects/components/memory-controllers/ADVANCED_MODES_ROADMAP.md`. Entry
gate (TASKS.md TASK-FEATURES): board reads validated at the bring-up tuple,
refresh-collision fix re-soaked on silicon.

Serial pre-silicon implementation order (each step OFF-by-default with its own
red-to-green model test):

1. **Foundation** — `SCHED_POLICY` / `PAGE_POLICY_CFG` / `REFRESH_MODE`
   mode-select CSRs + `*_STATS` telemetry + PHY capability straps (no behavior
   change; defaults bit-identical).
2. **Scheduling (Axis 1)** — `in_order` -> `fr_fcfs` (confirm current) ->
   `age_threshold` -> `most/fewest_pending` -> `ACCESS_PREF` ->
   write-batching -> **QoS** (AxQOS-aware pick, `QOS_EN`).
3. **Paging (Axis 2)** — `static_open/close` (confirm) -> `fixed_open` ->
   `adapt_time` -> `rbl_static` -> `rbl_dyn` -> `adapt_access`.
4. **Refresh (Axis 3, commodity)** — JEDEC pull-in/postpone sweep ->
   `refpb_rr`.

None of the mode-select CSRs above exist in the RDL yet; open issue 13 (QoS)
is subsumed by step 2 of this order.
