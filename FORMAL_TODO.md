# Formal Verification TODO

**Last Updated:** 2026-03-24
**Total Proved:** 48 modules
**Tool Chain:** sv2v + SymbiYosys + yosys + z3 (OSS CAD Suite 0.62)

---

## Infrastructure

### DONE
- [x] SymbiYosys + z3 solver installed and working
- [x] OSS CAD Suite 0.62 installed at /mnt/data/tools/oss-cad-suite
- [x] sv2v transpiler installed at /mnt/data/tools/sv2v
- [x] Formal directory structure: formal/{common,amba,bridge,stream}/
- [x] Per-module pattern: formal_*.sv (wrapper) + *.sby (config) + Makefile (for sv2v modules)
- [x] Root Makefile targets: make formal, formal-common, formal-bridge, formal-quick
- [x] .gitignore for sby output directories
- [x] install_formal_tools.sh, setup_from_scratch.sh
- [x] env_python updated with OSS CAD Suite + sv2v paths
- [x] $display / $timeformat / ifndef SYNTHESIS stripped from all production RTL
- [x] CI workflow includes formal (make formal-common in coverage.yml)

### TODO
- [ ] Migrate ALL existing stripped-copy proofs to sv2v pipeline (eliminate ~15 *_formal.sv hand copies)
- [ ] Add formal to test_environments.toml for make test-formal-* targets
- [ ] Update formal/common/Makefile to include all 36 modules (currently partial)
- [ ] Create formal/stream/Makefile for STREAM proofs
- [ ] Create formal/amba/Makefile for AMBA proofs
- [ ] Add FORMAL_TODO.md findings to KNOWN_ISSUES/ directories

---

## Findings (Bugs Found by Formal)

### AXI Handshake Stability Violations
- **axi_read_engine**: AR address/length change while ARVALID held without ARREADY
- **axi_write_engine**: AW address changes while AWVALID held; WVALID drops before WREADY
- **Root cause**: Multi-channel arbiter can switch channels mid-AXI handshake
- **Impact**: Violates AMBA IHI0022E A3.2.1 — VALID must not deassert until READY
- **Status**: Marked as FINDING in formal wrappers, needs RTL fix
- **Affects**: axi_read_engine, axi_write_engine, axi_read_engine_beats, axi_write_engine_beats

---

## rtl/common/ — 36 of ~210 modules proved

### DONE (36 modules)

| Module | Properties |
|--------|-----------|
| arbiter_round_robin_simple | one-hot, subset, valid-iff-req, id match, id range, no-spurious |
| arbiter_round_robin | same + last_grant, reset (no-ACK mode) |
| arbiter_round_robin_weighted | same safety set (no-ACK, equal weights) |
| arbiter_priority_encoder | valid-iff-req, lowest-set-bit, range, masked/unmasked mux |
| counter_bin | reset, increment, MSB wrap, lower clear, hold, next preview, range |
| counter_bingray | reset, Gray formula, single-bit change, hold, increment, next |
| counter_johnson | reset, single-bit change, hold, shift structure |
| bin2gray | formula correctness, single-bit change, MSB preserved, zero |
| gray2bin | roundtrip identity (bin→gray→bin), MSB preserved |
| grayj2bin | Johnson-to-binary validity |
| glitch_free_n_dff_arn | reset, propagation with constant input, output stable |
| fifo_sync | ghost counter, empty/full flags, count range, reset, mutex, rw tracking |
| fifo_async | ghost counter, CDC single-clock model, quiescent flag settling |
| gaxi_skid_buffer | ghost counter, count range, reset, full/empty flags, rw tracking |
| gaxi_skid_buffer_dbldrn | reset, count consistency (conservative) |
| gaxi_fifo_sync | ghost counter, empty/full flags |
| gaxi_fifo_async | ghost counter, CDC model, quiescent settling |
| gaxi_drop_fifo_sync | cover-based (count range deferred) |
| gaxi_regslice | count 0/1, reset |
| monbus_arbiter | reset, no spurious output |
| axi_gen_addr | FIXED/INCR/WRAP burst, alignment, 4KB split |
| dataint_crc_xor_shift | all 4 feedback cases, structural, LSB |
| dataint_crc_xor_shift_cascade | 8-stage cascade matches reference model |
| dataint_ecc_hamming | encode-decode roundtrip, SECDED parity, no false errors |
| dataint_parity | per-chunk parity gen, error detection |
| encoder | one-hot to binary correctness |
| decoder | cover-based (multi-driver yosys limitation) |
| encoder_priority_enable | priority encoding with enable |
| find_first_set | lowest set bit correctness |
| find_last_set | highest set bit correctness |
| count_leading_zeros | CLZ correctness |
| icg | latch-based clock gate (minimal properties) |
| clock_divider | reset, counter tracking |
| clock_gate_ctrl | gating behavior |
| cam_tag | reset, empty/full mutex |
| sync_pulse | (directory exists, proof not implemented — dual-clock) |

### NOT DONE — Priority 2 (worth doing)

| Module | Notes |
|--------|-------|
| fifo_async_div2 | Johnson counter async FIFO — needs sv2v |
| fifo_control | Flag logic (indirectly proved via fifo_sync) |
| fifo_sync_multi | Multi-signal variant |
| counter_bin_load | Counter with load (used by gaxi_drop_fifo_sync) |
| counter_load_clear | Standard counter |
| counter_freq_invariant | Timeout timer |
| reset_sync | Reset synchronizer |
| cdc_handshake | Handshake CDC |
| cdc_synchronizer | Multi-bit CDC |
| leading_one_trailing_one | Bit scanning (used by grayj2bin) |
| shifter_barrel | Shift correctness |
| shifter_lfsr / fibonacci / galois | LFSR maximal length |
| dataint_crc | Full CRC polynomial |
| dataint_checksum | Checksum accumulation |
| sort | Sorting network |
| debounce | Debounce filter |
| pwm | PWM generator |

### NOT DONE — Priority 3 (math, do as needed)

| Category | Count | Notes |
|----------|-------|-------|
| Adders (brent_kung, han_carlson, kogge_stone, ripple, CLA) | ~20 | Prove output == a + b |
| Subtractors | ~5 | Prove output == a - b |
| Multipliers (wallace, dadda, CSA) | ~15 | Prove output == a * b (8/16-bit only) |
| BF16 operations | ~30 | IEEE correctness |
| FP16/FP32/FP8 operations | ~80 | Diminishing returns |
| Internal cells (prefix_cell, compressor, etc.) | ~10 | Internal building blocks |

### NOT NEEDED (0 priority)

- bin_to_bcd, hex_to_7seg (display conversion)
- counter, counter_ring (trivial wrappers)
- reverse_vector (trivial)
- math_adder_half, math_subtractor_half (trivial)
- All 32-bit multipliers (too large for BMC)
- All FP approximation functions (sigmoid, tanh, gelu, etc.)

---

## rtl/amba/ — 5 of ~90 modules proved

### DONE (5 modules)

| Module | Properties |
|--------|-----------|
| apb_master | PENABLE needs PSEL, reset, SETUP→ACCESS, addr/pwrite stable, ACCESS hold |
| apb_slave | reset PREADY |
| apb5_master | same APB protocol (parity disabled) |
| apb5_slave | reset PREADY |
| axi_split_combi | 4KB boundary split, beat conservation, split addr aligned |

### NOT DONE — Priority 1

| Module | Notes |
|--------|-------|
| apb_monitor | APB packet generation correctness |
| apb5_monitor | APB5 variant |
| apb_slave_cdc | CDC variant — prove safe crossing |
| apb5_slave_cdc | APB5 CDC variant |
| axis_master / axis_slave | AXI-Stream TVALID/TREADY/TLAST |
| axi_master_rd_splitter | No transaction loss through split |
| axi_master_wr_splitter | Same |
| arbiter_monbus_common | MonBus arbiter variant |
| arbiter_rr_pwm_monbus | PWM round-robin |
| arbiter_wrr_pwm_monbus | Weighted RR |
| axi_monitor_base | Core monitor (complex) |
| axi_monitor_trans_mgr | Transaction table — prove no slot leak |
| gaxi_skid_buffer_async | Async skid — CDC |
| gaxi_skid_buffer_struct | Struct variant |

### NOT DONE — Priority 2

| Module | Notes |
|--------|-------|
| axi4_master_rd / wr | AXI4 timing wrappers |
| axi4_slave_rd / wr | Same |
| axil4_master_rd / wr | AXI4-Lite wrappers |
| axil4_slave_rd / wr | Same |
| axi4_*_mon | AXI monitors |
| axi4_interconnect_2x2_mon | 2x2 crossbar |
| All *_cg variants | Clock-gated — prove base first |
| All AXI5 variants | Lower priority |

### NOT NEEDED

- All *_stub modules (test-only)
- All *_pkg modules (type definitions)
- amba_clock_gate_ctrl (utility)

---

## projects/components/stream/ — 7 of 22 modules proved

### DONE (7 modules)

| Module | Area | Properties |
|--------|------|-----------|
| stream_alloc_ctrl | fub | reset, rd_ready==!rd_empty |
| stream_drain_ctrl | fub | reset, rd_ready==!rd_empty |
| stream_latency_bridge | fub | reset, occupancy range, ghost counter, no underflow |
| axi_read_engine | fub | AXI AR protocol, reset, ARBURST==INCR, ARSIZE (**FINDING: addr stability**) |
| axi_write_engine | fub | AXI AW/W protocol, reset (**FINDING: valid stability**) |
| axi_read_engine_beats | fub_beats | Same as STREAM read (**FINDING**) |
| axi_write_engine_beats | fub_beats | Same as STREAM write (**FINDING**) |

### NOT DONE — Priority 1 (need sv2v)

| Module | Area | Notes |
|--------|------|-------|
| descriptor_engine | fub | 919 lines, uses stream_pkg enums — sv2v should handle |
| scheduler | fub | 771 lines, uses stream_pkg state enums — sv2v should handle |
| sram_controller | fub | 201 lines, parses OK — needs gaxi_fifo_sync dep |
| sram_controller_unit | fub | 306 lines, parses OK — needs gaxi_fifo_sync dep |
| apbtodescr | fub | 363 lines, uses stream_pkg — sv2v |
| perf_profiler | fub | 433 lines, uses stream_pkg — sv2v |
| descriptor_engine_beats | fub_beats | RAPIDS variant |
| scheduler_beats | fub_beats | RAPIDS variant |
| alloc_ctrl_beats | fub_beats | Should be trivial (same as stream_alloc_ctrl) |
| drain_ctrl_beats | fub_beats | Same as stream_drain_ctrl |
| latency_bridge_beats | fub_beats | Same as stream_latency_bridge |

### NOT DONE — Priority 2 (macro/top integration)

| Module | Area | Notes |
|--------|------|-------|
| scheduler_group | macro | Integration — orchestrates FUBs |
| scheduler_group_array | macro | Multi-channel scheduler |
| datapath_rd_test / wr_test | macro | Test harnesses |
| monbus_axil_group | macro | MonBus integration |
| stream_core / stream_core_mon | macro | Core integration |
| cmdrsp_router | top | Command/response routing |
| stream_config_block | top | APB config registers |
| stream_top_ch8 | top | Top-level (1648 lines) |

### NOT DONE — RAPIDS legacy fub/ (skip)

| Module | Notes |
|--------|-------|
| source_axi_read_engine | Has SV queues ($) — can't be synthesized or formally verified |
| sink_axi_write_engine | Same |
| ctrlrd_engine / ctrlwr_engine | Ambiguous package imports |
| sink_sram_control / source_sram_control | Legacy |

### NOT DONE — RAPIDS macro_beats (Priority 3)

All 13 modules — integration-level, lower value for formal.

---

## projects/components/bridge/ — 1 protocol model

### DONE

| Module | Properties |
|--------|-----------|
| bridge_1x2_rd | Address decode mutex, DDR/SRAM range, AXI handshake model (blackbox) |

### NOT DONE — Priority 1

| Config | Notes |
|--------|-------|
| bridge_1x2_wr | Write-only variant (AW/W/B channels) |
| bridge_2x2_rw | Multi-master — adds arbitration assertions |
| bridge_1x3_rd / wr | Mixed-width (width conversion correctness) |
| bridge_cam | CAM ID tracking (345 lines, should parse OK) |

### NOT DONE — Priority 2

| Config | Notes |
|--------|-------|
| bridge_1x4_rd / wr | AXI-to-APB protocol conversion |
| bridge_1x5_rd / wr | AXI-to-AXI-Lite conversion |
| bridge_5x3_channels | 5 master × 3 slave (largest config) |

### BLOCKED

All generated bridge RTL uses SV packages with struct-typed ports in submodules.
The top-level ports are plain logic (yosys-parseable) but submodules aren't.
Current approach: blackbox protocol models on external ports.
Future: sv2v on the full generated RTL (needs testing).

---

## projects/components/converters/ — 0 of 16 proved

### NOT DONE — Priority 1

| Module | Lines | Notes |
|--------|-------|-------|
| axi4_to_axil4_rd | 255 | Protocol conversion — good formal target |
| axi4_to_axil4_wr | 304 | Same |
| axil4_to_axi4_rd | 149 | Inverse conversion |
| axil4_to_axi4_wr | 174 | Same |
| axi4_dwidth_converter_rd | 441 | Width conversion |
| axi4_dwidth_converter_wr | 460 | Width conversion |
| uart_rx | 139 | Serial protocol — good formal target |
| uart_tx | 123 | Same |

### NOT DONE — Priority 2

| Module | Lines | Notes |
|--------|-------|-------|
| axi4_to_apb_shim | 355 | AXI→APB |
| axi4_to_apb_convert | 485 | AXI→APB |
| axi_data_upsize | 215 | Width up-conversion |
| axi_data_dnsize | 486 | Width down-conversion |
| peakrdl_to_cmdrsp | 305 | Register adapter |
| uart_axil_bridge | 454 | UART to AXI-Lite |
| axi4_to_axil4 | 262 | Combined rd+wr |
| axil4_to_axi4 | 276 | Combined rd+wr |

---

## Summary

| Area | Proved | Total | % |
|------|--------|-------|---|
| rtl/common/ | 36 | ~210 | 17% (90%+ of high-value modules) |
| rtl/amba/ | 5 | ~90 | 6% (APB + splitter done) |
| STREAM fub | 5 | 11 | 45% |
| STREAM/RAPIDS engines | 4 | 4 | 100% (with findings) |
| RAPIDS fub_beats | 2 | 7 | 29% |
| Bridge | 1 | 10+ | protocol model |
| Converters | 0 | 16 | 0% |
| **Total** | **48** | **~350+** | |

### Next priorities
1. **Fix AXI handshake findings** — arbiter grant locking during active handshake
2. **STREAM FUBs** — descriptor_engine, scheduler, sram_controller via sv2v
3. **Converters** — axi4_to_axil4, axil4_to_axi4, uart_rx/tx
4. **Bridge configs** — 1x2_wr, 2x2_rw, bridge_cam
5. **AMBA protocol** — APB monitors, AXIS, AXI splitters
6. **Migrate stripped copies to sv2v** — eliminate maintenance burden
