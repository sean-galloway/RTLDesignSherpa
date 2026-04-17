# Formal Verification Priority List

**Generated:** 2026-03-21 | **Updated:** 2026-04-17
**Purpose:** Prioritize modules for formal verification with SymbiYosys

Priority: 1 = highest value, 2 = high, 3 = medium, 0 = not needed
Status: PASSING = proved (prove+cover), PROVE = prove-only PASS, ERROR = prove failed, blank = not started

---

## rtl/common/ — Building Blocks

### Arbiters & Scheduling

| Module                       | Priority | Status  | Notes                                              |
| ---------------------------- | -------- | ------- | -------------------------------------------------- |
| arbiter_round_robin_simple   | 1        | PASSING | 6 safety + 6 cover                                 |
| arbiter_round_robin          | 1        | PASSING | 7 safety + 5 cover (no-ACK mode)                   |
| arbiter_round_robin_weighted | 1        | PASSING | Weighted fairness — high value, complex properties |
| arbiter_priority_encoder     | 1        | PASSING | Combinational — prove priority order correctness   |

### FIFOs & Buffers

| Module                 | Priority | Status  | Notes                                                       |
| ---------------------- | -------- | ------- | ----------------------------------------------------------- |
| fifo_sync              | 1        | PASSING | 9 safety + 4 cover (ghost counter)                          |
| fifo_async             | 1        | PASSING | CDC critical — Gray pointer sync, empty/full across domains |
| fifo_async_div2        | 1        | PASSING | Johnson counter variant of async FIFO                       |
| fifo_control           | 2        | PASSING | Flag generation logic, used by both sync/async FIFOs        |
| fifo_sync_multi        | 3        | PASSING | Multi-signal variant                                        |
| fifo_sync_multi_sigmap | 3        | PASSING | Signal-mapped variant                                       |

### Counters

| Module                 | Priority | Status  | Notes                                                |
| ---------------------- | -------- | ------- | ---------------------------------------------------- |
| counter_bin            | 1        | PASSING | 7 safety + 3 cover (FIFO pointer wraparound)         |
| counter_bingray        | 1        | PASSING | 7 safety + 3 cover (Gray code single-bit-change)     |
| counter_johnson        | 1        | PASSING | Johnson counter — used in non-power-of-2 async FIFOs |
| counter_load_clear     | 3        | PASSING | Standard counter, less critical                      |
| counter_freq_invariant | 3        | PASSING | Timeout timer — prove timeout bound                  |
| counter_bin_load       | 3        | PASSING | Counter with load                                    |
| counter_ring           | 0        | PASSING | Simple ring counter, low risk                        |
| counter                | 0        | PASSING | Basic wrapper                                        |

### Clock Domain Crossing

| Module                | Priority | Status | Notes                                          |
| --------------------- | -------- | ------ | ---------------------------------------------- |
| glitch_free_n_dff_arn | 1        | PASSING | CDC synchronizer — prove no glitch on output   |
| sync_pulse            | 1        |         | Pulse CDC -- no .sby yet |
| cdc_synchronizer      | 1        | PASSING | Multi-bit CDC sync                             |
| cdc_handshake         | 1        | PASSING | Handshake-based CDC — prove no data loss       |
| reset_sync            | 2        | PASSING | Reset synchronizer — prove clean deassertion   |

### Gray Code Converters

| Module    | Priority | Status | Notes                                                  |
| --------- | -------- | ------ | ------------------------------------------------------ |
| bin2gray  | 1        | PASSING | Prove: gray = bin ^ (bin >> 1), used everywhere in CDC |
| gray2bin  | 1        | PASSING | Prove: inverse of bin2gray, roundtrip correctness      |
| grayj2bin | 1        | PASSING | Johnson-to-binary, used in fifo_async_div2             |

### Data Integrity

| Module                            | Priority | Status | Notes                                                  |
| --------------------------------- | -------- | ------ | ------------------------------------------------------ |
| dataint_ecc_hamming_encode_secded | 1        | PASSING | Prove encode-decode roundtrip, single-error correction |
| dataint_ecc_hamming_decode_secded | 1        | PASSING | Prove SEC-DED capability formally                      |
| dataint_crc                       | 3        | PASSING | Polynomial correctness — high value but complex        |
| dataint_parity                    | 2        | PASSING | Simple parity — prove odd/even generation              |
| dataint_checksum                  | 3        | PASSING | Checksum accumulation                                  |
| dataint_crc_xor_shift             | 1        | PASSING | CRC variant                                            |
| dataint_crc_xor_shift_cascade     | 1        | PASSING | CRC cascade variant                                    |

### Encoders & Decoders

| Module                   | Priority | Status | Notes                                                 |
| ------------------------ | -------- | ------ | ----------------------------------------------------- |
| encoder                  | 2        | PASSING | Binary encoder — prove one-hot input → correct output |
| decoder                  | 2        | PASSING | Binary decoder — prove inverse of encoder             |
| encoder_priority_enable  | 2        | PASSING | Priority encoder with enable                          |
| find_first_set           | 2        | PASSING | Prove correct bit position found                      |
| find_last_set            | 2        | PASSING | Prove correct bit position found                      |
| count_leading_zeros      | 2        | PASSING | Prove count matches actual leading zeros              |
| leading_one_trailing_one | 3        | PASSING | Bit scanning                                          |
| bin_to_bcd               | 0        |        | Display conversion, low risk                          |
| hex_to_7seg              | 0        |        | Display conversion, low risk                          |

### Clock & Power

| Module          | Priority | Status | Notes                                   |
| --------------- | -------- | ------ | --------------------------------------- |
| clock_divider   | 2        | PASSING | Prove divide ratio correct, no glitches |
| clock_gate_ctrl | 2        | PASSING | Prove glitch-free gating                |
| icg             | 2        | PASSING | Integrated clock gate cell              |
| clock_pulse     | 3        |        | No .sby yet                             |

### Shifters

| Module                 | Priority | Status | Notes                                      |
| ---------------------- | -------- | ------ | ------------------------------------------ |
| shifter_barrel         | 2        | PASSING | Prove shift amount → correct output        |
| shifter_lfsr           | 2        | PASSING | Prove LFSR period = 2^N-1 (maximal length) |
| shifter_lfsr_fibonacci | 2        | PASSING | Fibonacci LFSR variant                     |
| shifter_lfsr_galois    | 2        | PASSING | Galois LFSR variant                        |
| shifter_universal      | 3        |        | No .sby yet                                |

### Miscellaneous

| Module         | Priority | Status | Notes                                                |
| -------------- | -------- | ------ | ---------------------------------------------------- |
| cam_tag        | 2        | PASSING | CAM lookup — prove match correctness                 |
| sort           | 3        | PASSING | Sorting network — prove output is sorted permutation |
| debounce       | 3        | PASSING | Debounce filter                                      |
| pwm            | 3        | PASSING | PWM generator                                        |
| reverse_vector | 0        |        | Trivial bit reversal                                 |

### Math — Adders (prove equivalence to reference)

| Module                            | Priority | Status | Notes                             |
| --------------------------------- | -------- | ------ | --------------------------------- |
| math_adder_full                   | 2        | PASSING | Reference: a+b+cin = {cout, sum}  |
| math_adder_half                   | 0        |        | Trivial                           |
| math_adder_ripple_carry           | 2        | PASSING | Prove matches full_nbit           |
| math_adder_carry_lookahead        | 2        | PASSING | Prove matches ripple_carry output |
| math_adder_brent_kung_008         | 2        | PASSING | Prove matches reference adder     |
| math_adder_brent_kung_016         | 2        | PASSING | Same                              |
| math_adder_brent_kung_032         | 3        | PASSING | Same, larger                      |
| math_adder_han_carlson_016        | 3        | PASSING | Prove matches reference           |
| math_adder_han_carlson_032        | 3        | PASSING | Same                              |
| math_adder_han_carlson_044        | 0        |        | Large, diminishing returns        |
| math_adder_han_carlson_048        | 0        |        | Large                             |
| math_adder_han_carlson_072        | 0        |        | Large                             |
| math_adder_han_carlson_022        | 0        |        | Odd size                          |
| math_adder_kogge_stone_nbit       | 3        | PASSING | Prove matches reference           |
| math_adder_carry_save             | 0        |        | Internal building block           |
| math_adder_carry_save_nbit        | 0        |        | Internal                          |
| math_adder_full_nbit              | 0        |        | Wrapper                           |
| math_addsub_full_nbit             | 3        | PASSING | Prove add/sub mode correct        |
| math_adder_brent_kung_bitwisepg   | 0        |        | Internal cell                     |
| math_adder_brent_kung_black       | 0        |        | Internal cell                     |
| math_adder_brent_kung_gray        | 0        |        | Internal cell                     |
| math_adder_brent_kung_pg          | 0        |        | Internal cell                     |
| math_adder_brent_kung_sum         | 0        |        | Internal cell                     |
| math_adder_brent_kung_grouppg_008 | 0        |        | Internal cell                     |
| math_adder_brent_kung_grouppg_016 | 0        |        | Internal cell                     |
| math_adder_brent_kung_grouppg_032 | 0        |        | Internal cell                     |
| math_prefix_cell                  | 0        |        | Internal cell                     |
| math_prefix_cell_gray             | 0        |        | Internal cell                     |
| math_compressor_4to2              | 0        |        | Internal cell                     |

### Math — Subtractors

| Module                          | Priority | Status | Notes                        |
| ------------------------------- | -------- | ------ | ---------------------------- |
| math_subtractor_full            | 2        | PASSING | Prove a-b-bin = {bout, diff} |
| math_subtractor_half            | 0        |        | Trivial                      |
| math_subtractor_ripple_carry    | 2        | PASSING | Prove matches full_nbit      |
| math_subtractor_carry_lookahead | 2        | PASSING | Prove matches reference      |
| math_subtractor_full_nbit       | 0        |        | Wrapper                      |

### Math — Multipliers (prove output = a * b)

| Module                               | Priority | Status | Notes                          |
| ------------------------------------ | -------- | ------ | ------------------------------ |
| math_multiplier_wallace_tree_008     | 2        | PASSING | Prove output = a * b for 8-bit |
| math_multiplier_dadda_tree_008       | 2        | PASSING | Same                           |
| math_multiplier_wallace_tree_016     | 3        | PASSING | 16-bit — larger state space    |
| math_multiplier_dadda_tree_016       | 3        | PASSING | Same                           |
| math_multiplier_wallace_tree_032     | 0        |        | 32-bit — too large for BMC     |
| math_multiplier_dadda_tree_032       | 0        |        | Same                           |
| math_multiplier_dadda_4to2_008       | 3        |        | 4:2 compressor variant         |
| math_multiplier_dadda_4to2_011       | 0        |        | Odd size                       |
| math_multiplier_dadda_4to2_024       | 0        |        | Large                          |
| math_multiplier_wallace_tree_csa_008 | 3        |        | CSA variant                    |
| math_multiplier_wallace_tree_csa_016 | 0        |        | Large                          |
| math_multiplier_wallace_tree_csa_032 | 0        |        | Too large                      |
| math_multiplier_carry_save           | 0        |        | Internal                       |
| math_multiplier_basic_cell           | 0        |        | Internal                       |

### Math — Floating Point (bf16/fp16/fp32/fp8)

| Module                         | Priority | Status | Notes                                                  |
| ------------------------------ | -------- | ------ | ------------------------------------------------------ |
| math_bf16_adder                | 2        | PASSING | Prove matches IEEE reference (small format)            |
| math_bf16_multiplier           | 2        | PASSING | Same                                                   |
| math_bf16_fma                  | 2        | PASSING | Fused multiply-add correctness                         |
| math_bf16_to_fp32              | 2        | PASSING | Lossless conversion — prove exact                      |
| math_fp32_to_bf16              | 2        | PASSING | Lossy — prove rounding correct                         |
| math_bf16_to_fp16              | 3        | PASSING | Format conversion                                      |
| math_fp16_to_bf16              | 3        | PASSING | Format conversion                                      |
| math_bf16_relu                 | 0        |        | Trivial: max(0, x)                                     |
| math_bf16_leaky_relu           | 0        |        | Simple threshold                                       |
| math_bf16_max                  | 0        |        | Comparator                                             |
| math_bf16_min                  | 0        |        | Comparator                                             |
| math_bf16_clamp                | 0        |        | Range check                                            |
| math_bf16_comparator           | 0        |        | Simple comparison                                      |
| math_bf16_sigmoid              | 0        |        | Approximation — hard to prove exactly                  |
| math_bf16_tanh                 | 0        |        | Approximation                                          |
| math_bf16_gelu                 | 0        |        | Approximation                                          |
| math_bf16_silu                 | 0        |        | Approximation                                          |
| math_bf16_softmax_8            | 0        |        | Complex pipeline                                       |
| math_bf16_exp2                 | 0        |        | Approximation                                          |
| math_bf16_log2                 | 0        |        | Approximation                                          |
| math_bf16_log2_scale           | 0        |        | Approximation                                          |
| math_bf16_reciprocal           | 0        |        | Iterative                                              |
| math_bf16_fast_reciprocal      | 0        |        | Approximation                                          |
| math_bf16_newton_raphson_recip | 0        |        | Iterative                                              |
| math_bf16_goldschmidt_div      | 0        |        | Iterative                                              |
| math_bf16_divider              | 0        |        | Complex                                                |
| math_bf16_scale_to_int8        | 0        |        | Quantization                                           |
| math_bf16_to_int               | 0        |        | Truncation                                             |
| math_int_to_bf16               | 0        |        | Conversion                                             |
| math_bf16_max_tree_8           | 0        |        | Tree reduction                                         |
| math_bf16_max_tree             | 0        |        | Tree reduction                                         |
| math_bf16_min_tree_8           | 0        |        | Tree reduction                                         |
| math_bf16_exponent_adder       | 0        |        | Internal                                               |
| math_bf16_mantissa_mult        | 0        |        | Internal                                               |
| math_bf16_to_fp8_e4m3          | 0        |        | Niche conversion                                       |
| math_bf16_to_fp8_e5m2          | 0        |        | Niche conversion                                       |
| math_fp16_* (all)              | 0        |        | Same pattern as bf16 — diminishing returns             |
| math_fp32_* (all)              | 0        |        | Same — too large for efficient BMC                     |
| math_fp8_e4m3_* (all)          | 0        |        | Small format but niche                                 |
| math_fp8_e5m2_* (all)          | 0        |        | Small format but niche                                 |
| math_ieee754_2008_* (all)      | 0        |        | Full IEEE — very complex, better tested via simulation |

---

## rtl/amba/ — Protocol Infrastructure

### GAXI FIFOs & Buffers (HIGH VALUE)

| Module                        | Priority | Status | Notes                                                   |
| ----------------------------- | -------- | ------ | ------------------------------------------------------- |
| gaxi_fifo_sync                | 1        | PASSING | Production FIFO — prove empty/full/count like fifo_sync |
| gaxi_fifo_async               | 1        | PASSING | Production async FIFO — CDC safety critical             |
| gaxi_skid_buffer              | 1        | PASSING | Skid buffer — prove no data loss, backpressure correct  |
| gaxi_skid_buffer_dbldrn       | 1        | PASSING | Double-drain variant — prove throughput properties      |
| gaxi_regslice                 | 2        | PASSING | Register slice — prove valid/ready protocol             |
| gaxi_drop_fifo_sync           | 1        | PASSING | Drop FIFO — prove drop-on-full behavior correct         |
| gaxi_skid_buffer_async        | 2        | PASSING | Async skid — CDC properties                             |
| gaxi_skid_buffer_struct       | 3        | PASSING | Struct variant                                          |
| gaxi_fifo_async_multi         | 3        | PASSING | Multi-signal variant                                    |
| gaxi_fifo_sync_multi          | 3        | PASSING | Multi-signal variant                                    |
| gaxi_skid_buffer_multi        | 3        | PASSING | Multi-signal variant                                    |
| gaxi_skid_buffer_multi_sigmap | 3        | PASSING | Signal-mapped variant                                   |
| gaxi_skid_buffer_async_multi  | 3        | PASSING | Multi + async variant                                   |

### AXI4 Timing Wrappers

| Module            | Priority | Status | Notes                                                  |
| ----------------- | -------- | ------ | ------------------------------------------------------ |
| axi4_master_rd    | 0        | PASSING | Prove AXI handshake protocol preserved through wrapper |
| axi4_master_wr    | 0        | PASSING | Same for write path                                    |
| axi4_slave_rd     | 0        | PASSING | Slave-side read wrapper                                |
| axi4_slave_wr     | 0        | PASSING | Slave-side write wrapper                               |
| axi4_master_rd_cg | 2        | PASSING | Clock-gated variant                                    |
| axi4_master_wr_cg | 2        | PASSING | Clock-gated variant                                    |
| axi4_slave_rd_cg  | 2        | PASSING | Clock-gated variant                                    |
| axi4_slave_wr_cg  | 2        | PASSING | Clock-gated variant                                    |

### AXI4-Lite Wrappers

| Module          | Priority | Status | Notes                                    |
| --------------- | -------- | ------ | ---------------------------------------- |
| axil4_master_rd | 0        |        | Lite protocol — simpler, easier to prove |
| axil4_master_wr | 0        |        | Same                                     |
| axil4_slave_rd  | 0        |        | Same                                     |
| axil4_slave_wr  | 0        |        | Same                                     |
| axil4_*_cg      | 3        |        | Clock-gated variants                     |
| axil4_*_mon     | 3        |        | Monitor variants                         |
| axil4_*_mon_cg  | 3        |        | Monitor + CG combo                       |

### AXI5 Wrappers

| Module                       | Priority | Status | Notes                                       |
| ---------------------------- | -------- | ------ | ------------------------------------------- |
| axi5_master_rd               | 0        |        | AXI5 — same pattern as AXI4, lower priority |
| axi5_master_wr               | 0        |        | Same                                        |
| axi5_slave_rd                | 0        |        | Same                                        |
| axi5_slave_wr                | 0        |        | Same                                        |
| axi5_*_cg / *_mon / *_mon_cg | 3        |        | Variants — do base first                    |

### AXI Monitors

| Module             | Priority | Status | Notes                                   |
| ------------------ | -------- | ------ | --------------------------------------- |
| axi4_master_rd_mon | 2        | PASSING | Prove monitor packet generation correct |
| axi4_master_wr_mon | 2        | PASSING | Same                                    |
| axi4_slave_rd_mon  | 2        | PASSING | Same                                    |
| axi4_slave_wr_mon  | 2        | PASSING | Same                                    |
| axi4_*_mon_cg      | 0        |        | CG variant — prove base first           |
| axi5_*_mon         | 0        |        | AXI5 monitors — lower priority          |

### AXI Monitor Infrastructure

| Module                | Priority | Status | Notes                                   |
| --------------------- | -------- | ------ | --------------------------------------- |
| axi_monitor_base      | 2        | PASSING | Core monitor — complex, high value      |
| axi_monitor_trans_mgr | 2        | PASSING | Transaction table — prove no slot leak  |
| axi_monitor_reporter  | 3        | PASSING | Packet formatting                       |
| axi_monitor_timeout   | 3        | PASSING | Timeout detection                       |
| axi_monitor_timer     | 0        | PASSING | Simple timer                            |
| axi_monitor_filtered  | 0        | PASSING | Filter wrapper                          |
| axi_gen_addr          | 1        | PASSING | Address generation — prove 4KB boundary |

### MonBus Arbiters

| Module                 | Priority | Status | Notes                                       |
| ---------------------- | -------- | ------ | ------------------------------------------- |
| monbus_arbiter         | 1        | PASSING | Already has assertions — extend with formal |
| arbiter_monbus_common  | 2        | PASSING | Common arbiter for monitor bus              |
| arbiter_rr_pwm_monbus  | 2        | PASSING | PWM round-robin — prove fairness            |
| arbiter_wrr_pwm_monbus | 2        | PASSING | Weighted RR — prove weight distribution     |

### AXI Splitters

| Module                 | Priority | Status | Notes                                   |
| ---------------------- | -------- | ------ | --------------------------------------- |
| axi_master_rd_splitter | 2        | PASSING | Prove no transaction loss through split |
| axi_master_wr_splitter | 2        | PASSING | Same                                    |
| axi_split_combi        | 2        | PASSING | Combinational split logic               |

### APB Modules

| Module             | Priority | Status | Notes                                   |
| ------------------ | -------- | ------ | --------------------------------------- |
| apb_master         | 2        | PASSING | Prove APB setup/access phase sequencing |
| apb_slave          | 2        | PASSING | Prove correct response timing           |
| apb_monitor        | 2        | PASSING | Prove packet generation                 |
| apb5_master        | 2        | PASSING | APB5 variant                            |
| apb5_slave         | 2        | PASSING | APB5 variant                            |
| apb5_monitor       | 2        | PASSING | APB5 variant                            |
| apb_slave_cdc      | 2        | PASSING | CDC variant — prove safe crossing       |
| apb5_slave_cdc     | 2        | PASSING | APB5 CDC variant                        |
| apb_*_cg / *_stub  | 0        |        | CG/stub variants                        |
| apb5_*_cg / *_stub | 0        |        | CG/stub variants                        |

### AXIS (AXI-Stream)

| Module                 | Priority | Status | Notes                              |
| ---------------------- | -------- | ------ | ---------------------------------- |
| axis_master            | 2        | PASSING | Prove TVALID/TREADY/TLAST protocol |
| axis_slave             | 2        | PASSING | Same                               |
| axis5_master           | 3        |        | AXIS5 variant                      |
| axis5_slave            | 3        |        | AXIS5 variant                      |
| axis_*_cg / axis5_*_cg | 0        |        | CG variants                        |

### CDC Modules

| Module           | Priority | Status  | Notes                           |
| ---------------- | -------- | ------- | ------------------------------- |
| cdc_synchronizer | 1        | PASSING | Already listed under common CDC |
| cdc_handshake    | 1        | PASSING | Already listed under common CDC |

### Stubs (test-only)

| Module              | Priority | Status | Notes                          |
| ------------------- | -------- | ------ | ------------------------------ |
| axi4_master_rd_stub | 0        |        | Test stub — not production RTL |
| axi4_master_wr_stub | 0        |        | Same                           |
| axi4_slave_rd_stub  | 0        |        | Same                           |
| axi4_slave_wr_stub  | 0        |        | Same                           |
| axi4_master_stub    | 0        |        | Same                           |
| axi4_slave_stub     | 0        |        | Same                           |
| axi5_*_stub         | 0        |        | Same                           |
| apb_*_stub          | 0        |        | Same                           |
| apb5_*_stub         | 0        |        | Same                           |

### Packages (no formal needed)

| Module              | Priority | Status | Notes                 |
| ------------------- | -------- | ------ | --------------------- |
| axi_pkg             | 0        |        | Type definitions only |
| apb_pkg             | 0        |        | Type definitions only |
| apb5_pkg            | 0        |        | Type definitions only |
| monitor_pkg         | 0        |        | Type definitions only |
| monitor_amba4_pkg   | 0        |        | Type definitions only |
| monitor_amba5_pkg   | 0        |        | Type definitions only |
| monitor_arbiter_pkg | 0        |        | Type definitions only |
| monitor_common_pkg  | 0        |        | Type definitions only |

---

## Summary (Updated 2026-04-17)

| Status | Count | Notes |
|--------|-------|-------|
| PASSING (prove+cover) | 300 | Full formal verification |
| PROVE-only | 19 | Prove PASS, no cover task defined |
| ERROR | 9 | 7 math complexity + counter_freq_invariant + stream_core |
| Not started | ~3 | sync_pulse, clock_pulse, shifter_universal (no .sby) |
| Skipped (Priority 0) | ~120+ | Stubs, packages, trivial modules |

**Remaining actionable work:**
1. Fix `counter_freq_invariant` yosys syntax error
2. Fix `icg` and `axi_split_combi` cover depth
3. Add cover tasks to 19 prove-only modules
4. `sync_pulse` -- create formal proof (Priority 1 CDC)
