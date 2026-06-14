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

Partial writes in DDR2 / LPDDR2 use `wrdata_mask` to mask byte lanes; this is straightforward. **Confirm** that per-byte masking is wired all the way through `wdata_path` and that `axi4_slave` doesn't widen narrow writes implicitly.

### 3. APB CSR Address Space Allocation

12-bit `paddr` provides a 4 KB region. **Confirm** the SoC's APB address-map allocation has at least 4 KB available, and that there's no conflict with adjacent peripherals.

### 4. Per-Bank Refresh Book-Keeping Cost

Keeping `last_ref_age` per bank costs one counter per bank. For 8 banks this is 8 small counters. **Confirm** the synthesis area impact is acceptable; we expect ~200 LUTs for the per-bank refresh tracking on a typical FPGA.

### 5. HAPPY Predictor Hash Function

Ghasempour 2015 suggests bank-XOR-low-row-bits as the hash function. **Confirm** with our typical workloads. If the workloads have systematic bank-row correlations, a different hash may be needed.

### 6. Self-Refresh Exit Latency

JESD79-2 requires `tXSNR` (~200 ns) before any command after SR exit. **Confirm** the power-state FSM enforces this correctly and that the scheduler is gated for the full duration.

### 7. Init Engine Retry on Error

If ZQ fails, do we retry up to 3 times then halt, or just halt? Current plan: 3 retries (parameter `INIT_ZQ_RETRIES`) then raise `init_error`. **Confirm** with the system architect — some systems prefer fail-fast.

### 8. CSR Write Atomicity

Multi-register parameter changes (e.g., updating both `MR0` and a related timing) need a "config quiet period" to take effect atomically. **Document** the protocol the SoC software should follow; potentially expose a `config_apply` strobe.

### 9. Burst Splitting at Row Boundaries

AXI4 allows up to 256 beats per burst; a DRAM row contains `2^COL_WIDTH` columns. Burst splitting happens in `axi4_slave`. **Confirm** the split logic correctly tracks partial-burst completion for ID-based ordering.

### 10. Multi-Rank

Explicitly out of scope for v1. **Note for v2**: add a `RANK_WIDTH` parameter, rank-aware bank machines, and rank-coordinated refresh.

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

## TODOs Before v0.2

- Add bit-level pinout tables for the AXI, DFI, and APB interfaces
- Add timing diagrams for the WR / RD command issue, including CWL / CL alignment
- Add FSM state-transition diagrams for `bank_machine`, `power_state`, and `init_engine`
- Add a draft of the Verilog package skeletons for `ddr2_init_steps_pkg.sv` and `lpddr2_init_steps_pkg.sv`
- Cross-reference each section to the corresponding pre-aspec.md bullet
- Add quantitative area / power estimates per module (synthesis pass needed)
- Add waveform examples for the canonical init sequences
