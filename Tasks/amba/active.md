<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. Move a task between open/active/closed by cutting its block, do not copy. -->

# AMBA tasks — active (in progress)

### TASK-013: Create Integration Examples
**Priority:** P2
**Status:** 🟢 Near Complete (2025-10-12)
**Owner:** Claude AI
**Effort:** Medium (3-4 days)
**Completion:** ~90% (2 examples complete, 1 planned)

**Description:**
Create example designs showing how to integrate monitors in real SoC environments. Focus on working APB-based examples.

**Work Completed:**

1. **Comprehensive Integration Guide** ✅
   - rtl/integ_amba/examples/README.md (600+ lines)
   - Monitor packet format specification (64-bit structure)
   - Arbiter selection guide (round-robin, weighted, priority)
   - Downstream handling patterns (direct, FIFO, hierarchical)
   - Configuration strategies (functional, performance, production)
   - Agent ID assignment scheme
   - Integration checklist
   - Common pitfalls and solutions
   - Resource utilization estimates

2. **Example 1: APB Crossbar with Monitors** ✅
   - File: rtl/integ_amba/examples/apb_xbar_monitored.sv (400+ lines)
   - 3 masters × 4 slaves = 7 monitors total
   - Based on tested apb_xbar_thin variant (PASSED)
   - Complete monitor coverage (every interface)
   - Round-robin arbiter for aggregation
   - Parameterized agent ID assignment
   - Full documentation with usage examples
   - Architecture diagrams and monitor table

3. **Example 2: Simple APB Peripheral Subsystem** ✅
   - File: rtl/integ_amba/examples/apb_peripheral_subsystem.sv (350+ lines)
   - Educational example for beginners
   - 3 peripherals: Register File (functional), Timer (stub), GPIO (stub)
   - 3 monitors with simple round-robin arbiter
   - Address decoding demonstration
   - Full documentation with extension guide
   - Minimal complexity, easy to understand

**Examples Planned:**
- [ ] Example 3: AXI4-to-APB Bridge with dual monitors (protocol conversion)
  - Demonstrates monitoring across protocol boundaries
  - AXI4 master monitor + APB slave monitor
  - Two separate monitor buses (one per clock domain)

**Examples Deferred to Future:**
- AXI4 crossbar with monitors (needs crossbar RTL completion - see TASK-022)
- AXI4-Lite register file with monitor
- Mixed protocol system (AXI4 + APB + AXIS)
- Created FUTURE_axi4_crossbar_monitored.sv as reference for when AXI4 crossbar is functional

**Documentation Deliverables:**
- ✅ Comprehensive README.md with integration patterns (600+ lines)
- ✅ Example 1 detailed documentation (architecture, usage, testing)
- ✅ Example 2 detailed documentation (learning guide, extension patterns)
- ✅ Arbiter usage and selection guide
- ✅ Monitor bus aggregation strategies
- ✅ Best practices for packet type configuration
- ✅ Resource utilization estimates
- ✅ Integration checklist
- ✅ Common pitfalls with solutions

---

### TASK-023: Complete RTLAmba Documentation and Waveform Integration
**Priority:** P0
**Status:** 🟡 In Progress (2025-10-23)
**Owner:** Claude AI
**Effort:** High (2-3 weeks)
**Task File:** `TASK-023-complete_rtlamba_documentation.md`

**Description:**
Complete comprehensive markdown documentation for all AMBA modules with integrated WaveDrom timing diagrams. Fill gaps in docs/markdown/RTLAmba/ structure.

**Current Status Assessment:**
- ✅ **Main Modules Documented:** 41 markdown files (axi4, axil4, apb, axis4, gaxi, shared)
- ⚠️ **Documentation Gaps:** 56 modules lack individual docs (97 total - 41 documented)
- ⚠️ **Waveforms Exist:** 14 modules have waveforms in docs/markdown/assets/WAVES/
- ⚠️ **Waveform Integration:** Only 5/41 docs reference waveforms (12% integration)
- ❌ **Empty Directories:** adapters/, components/, testcode/ have no documentation

**Documentation Gaps by Category:**

1. **Clock-Gated Variants (Priority 1):**
   - [ ] axi4_master_rd_mon_cg.md
   - [ ] axi4_master_wr_mon_cg.md
   - [ ] axi4_slave_rd_mon_cg.md
   - [ ] axi4_slave_wr_mon_cg.md
   - [ ] axil4_*_mon_cg.md (4 modules)
   - [ ] apb_master_cg.md, apb_slave_cg.md, apb_slave_cdc_cg.md
   - **Approach:** Reference base module, document CG-specific parameters

2. **Monitor Variants (Priority 1):**
   - [ ] axi4_master_rd_hp_mon.md (high-performance variant)
   - [ ] axi4_master_rd_lp_mon.md (low-power variant)
   - [ ] Document variant differences and use cases

3. **Stub Modules (Priority 2):**
   - [ ] axi4_master_stub.md, axi4_master_rd_stub.md, axi4_master_wr_stub.md
   - [ ] axi4_slave_rd_stub.md, axi4_slave_wr_stub.md
   - [ ] apb_master_stub.md, apb_slave_stub.md
   - **Approach:** Explain stub purpose, testing usage

4. **Shared Infrastructure (Priority 1):**
   - ✅ docs/markdown/RTLAmba/shared/README.md exists (comprehensive)
   - [x] Individual module pages now exist under docs/markdown/RTLAmba/monitor/:
     - axi_monitor_base.md
     - axi_monitor_filtered.md
     - axi_monitor_trans_mgr.md
     - axi_monitor_reporter.md
     - axi_monitor_timeout.md
     - arbiter_monbus_common.md
     - monbus_arbiter.md
     - cdc_handshake (covered in docs/markdown/RTLAmba/cdc/cdc.md)

5. **Adapters/Shims (Priority 2):**
   - ✅ docs/markdown/RTLAmba/shims/README.md exists
   - ✅ Individual shim docs exist (axi4_to_apb_convert, axi4_to_apb_shim, peakrdl_to_cmdrsp)
   - [ ] Update shims documentation with usage examples

**Waveform Integration Tasks:**

1. **Generate Missing Waveforms (Priority 1):**
   - [ ] AXIL monitors (8 modules) - Similar to AXI4 but simpler
   - [ ] APB crossbar - Address decode and routing
   - [ ] Arbiters (monbus, round-robin, weighted) - QoS visualization
   - [ ] Shims (axi4_to_apb) - Protocol conversion timing

2. **Integrate Existing Waveforms (Priority 1):**
   - ✅ apb_slave.md already includes waveforms (reference pattern)
   - [ ] apb_slave_cdc.md - Add waveform references
   - [ ] apb_master.md - Add waveform references
   - [ ] axi4_master_rd_mon.md - Add waveform references
   - [ ] axi4_master_wr_mon.md - Add waveform references
   - [ ] axi4_slave_rd_mon.md - Add waveform references
   - [ ] axi4_slave_wr_mon.md - Add waveform references
   - [ ] gaxi_skid_buffer.md - Add waveform references

3. **Waveform Generation Infrastructure:**
   - ✅ WaveDrom test pattern exists (val/amba/test_*_wavedrom.py)
   - [ ] Create wavedrom tests for missing modules
   - [ ] Follow pattern: pytest test generates .json → Include in markdown

**Integration Pattern (from apb_slave.md):**
```markdown

### TASK-025: Update formal proofs for the monitor logic

**Priority:** Medium
**Status:** [~] In progress (2026-07-18) — infrastructure fixed, **all 12 pass**;
the real RTL bug the proofs surfaced (active_count underflow) is FIXED and
functionally re-validated; some extensions + a val/amba path sweep still pending.

**Context:** The monitor modules moved from `rtl/amba/shared/` (and the per-protocol
dirs) to **`rtl/amba/monitor/`**, and the monitor RTL gained new logic since the
formal proofs were last exercised (perfmon window/counters, `cam_clear`, the
`cfg_compl/threshold/debug` enables, `ENABLE_*_LOGIC` synthesis cones, always-on
CAM pipelining). The `formal/amba/*` Makefiles + `.sby` files were path-updated to
`monitor/` and verified to resolve, but the **SymbiYosys proofs were not re-run**.

**Checklist:**
- [x] Run `make` in each `formal/amba/{...}` and confirm they pass after the move.
      **10/12 pass.** The stale DEPS lists (the reporter split into six
      `axi_monitor_reporter_*` sub-modules + the `monitor_trans_cam` extraction +
      `apb_monitor_addr_check`) broke yosys elaboration everywhere; fixed by a new
      `tools/gen_formal_deps.py` that regenerates each Makefile's DEPS from the
      transitive module closure and derives the sv2v file list from `$(DEPS)` so the
      two can't drift again. Also fixed: `axi_monitor_base` `block_ready` polarity
      assertion (RTL fix flipped it to positive-enable; old assert encoded the
      pre-fix inverted polarity), `axi_monitor_trans_mgr` pipeline-latency staleness
      of `ap_alloc_from_empty` (always-pipelined CAM), and `apb5_monitor`'s stale
      128-bit-packet protocol assertion (apb5 emits the compact 64-bit monbus word;
      protocol is at `[59:57]`, not `[108:105]`).
- [x] **Real RTL bug found AND FIXED.** `axi_monitor_trans_mgr` + `axi_monitor_base`
      failed `ap_count_bounded`/`ap_no_overflow`: `active_count` (the alloc-minus-
      cleanup accumulator) **underflowed to 0xFF** ~8 cycles after reset under a
      broadly-legal AXI sequence, corrupting `busy`/`block_ready`. Fix: derive
      `active_count` as the registered pop-count of `cam_entry_valid` (structurally
      `[0, N]`, cannot underflow); a saturate-at-0 attempt passed the bound but a
      formal accuracy probe showed it still under-reported, so the pop-count form
      was adopted. All 12 monitor proofs now pass; `axi4_master_rd_mon` cocotb test
      passes at MAX_TRANSACTIONS=16. Added a port-only `ap_clear_zeroes_count`
      (cam_clear) property to trans_mgr. See
      `rtl/amba/KNOWN_ISSUES/axi_monitor_active_count_underflow.md`.
- [ ] **val/amba monitor-test path sweep (NEW, pending).** The monitor move left
      ~75 val/amba tests building monitor source paths via
      `os.path.join(rtl_dict['rtl_shared'], "...")` where `rtl_shared='rtl/amba/shared'`
      — the earlier string-based sweep missed these because the path is assembled at
      runtime. `test_axi4_master_rd_mon.py` fixed (repointed to `rtl/amba/monitor`);
      the rest still need the same repoint.
- [ ] Extend the proofs to cover the new perfmon window state machine + the four
      utilization / beat-byte-burst counters (`axi_monitor_base`). *(pending)*
- [ ] Add a `cam_clear` synchronous-clear property to the trans-CAM proofs. *(pending)*
- [ ] Confirm the `ENABLE_*_LOGIC=0` cone-drop configurations still prove (or are
      excluded intentionally). *(pending)*
- [ ] `axi_monitor_timer` has a `formal/amba/` dir but **no Makefile/harness** — it
      was never set up. Decide whether to author one (net-new proof) or drop it from
      the list.
- [x] Update any formal filelist/`.sby` that still assumes the old `shared/` layout —
      all Makefiles regenerated against `rtl/amba/monitor/`; all 12 flatten cleanly.

---

