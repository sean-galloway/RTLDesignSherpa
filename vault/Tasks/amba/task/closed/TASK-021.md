# TASK-021: Complete rtl-amba Documentation and Waveform Integration

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-023** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P0
**Status:** Complete (2026-07-22) — rtl-amba doc set rebuilt from 41 to 182 markdown files; the CG-variant, stub, and monitor-module pages this task listed as gaps now exist and render into the RTL library PDFs. Original marker: In Progress (2025-10-23).
**Owner:** Claude AI
**Effort:** High (2-3 weeks)
**Task File:** `TASK-023-complete_rtlamba_documentation.md`

**Description:**
Complete comprehensive markdown documentation for all AMBA modules with integrated WaveDrom timing diagrams. Fill gaps in docs/markdown/rtl-amba/ structure.

**Current Status Assessment:**
- **Main Modules Documented:** 41 markdown files (axi4, axil4, apb, axis4, gaxi, shared)
- **Documentation Gaps:** 56 modules lack individual docs (97 total - 41 documented)
- **Waveforms Exist:** 14 modules have waveforms in docs/markdown/assets/WAVES/
- **Waveform Integration:** Only 5/41 docs reference waveforms (12% integration)
- **Empty Directories:** adapters/, components/, testcode/ have no documentation

**Documentation Gaps by Category:**

1. **Clock-Gated Variants (Priority 1):**
   - [ ] axi4_master_rd_mon_cg.md
   - [ ] axi4_master_wr_mon_cg.md
   - [ ] axi4_slave_rd_mon_cg.md
   - [ ] axi4_slave_wr_mon_cg.md
   - [ ] axil4_*_mon_cg.md (4 modules)
   - [ ] apb4_master_cg.md, apb4_slave_cg.md, apb4_slave_cdc_cg.md
   - **Approach:** Reference base module, document CG-specific parameters

2. **Monitor Variants (Priority 1):**
   - [ ] axi4_master_rd_hp_mon.md (high-performance variant)
   - [ ] axi4_master_rd_lp_mon.md (low-power variant)
   - [ ] Document variant differences and use cases

3. **Stub Modules (Priority 2):**
   - [ ] axi4_master_stub.md, axi4_master_rd_stub.md, axi4_master_wr_stub.md
   - [ ] axi4_slave_rd_stub.md, axi4_slave_wr_stub.md
   - [ ] apb4_master_stub.md, apb4_slave_stub.md
   - **Approach:** Explain stub purpose, testing usage

4. **Shared Infrastructure (Priority 1):**
   - docs/markdown/rtl-amba/shared/README.md exists (comprehensive)
   - [x] Individual module pages now exist under docs/markdown/rtl-amba/monitor/:
     - axi_monitor_base.md
     - axi_monitor_filtered.md
     - axi_monitor_trans_mgr.md
     - axi_monitor_reporter.md
     - axi_monitor_timeout.md
     - arbiter_monbus_common.md
     - monbus_arbiter.md
     - cdc_handshake (covered in docs/markdown/rtl-amba/cdc/cdc.md)

5. **Adapters/Shims (Priority 2):**
   - docs/markdown/rtl-amba/shims/README.md exists
   - Individual shim docs exist (axi4_to_apb4_convert, axi4_to_apb4_shim, peakrdl_to_cmdrsp)
   - [ ] Update shims documentation with usage examples

**Waveform Integration Tasks:**

1. **Generate Missing Waveforms (Priority 1):**
   - [ ] AXIL monitors (8 modules) - Similar to AXI4 but simpler
   - [ ] APB crossbar - Address decode and routing
   - [ ] Arbiters (monbus, round-robin, weighted) - QoS visualization
   - [ ] Shims (axi4_to_apb4) - Protocol conversion timing

2. **Integrate Existing Waveforms (Priority 1):**
   - apb4_slave.md already includes waveforms (reference pattern)
   - [ ] apb4_slave_cdc.md - Add waveform references
   - [ ] apb4_master.md - Add waveform references
   - [ ] axi4_master_rd_mon.md - Add waveform references
   - [ ] axi4_master_wr_mon.md - Add waveform references
   - [ ] axi4_slave_rd_mon.md - Add waveform references
   - [ ] axi4_slave_wr_mon.md - Add waveform references
   - [ ] gaxi_skid_buffer.md - Add waveform references

3. **Waveform Generation Infrastructure:**
   - WaveDrom test pattern exists (val/amba/test_*_wavedrom.py)
   - [ ] Create wavedrom tests for missing modules
   - [ ] Follow pattern: pytest test generates .json → Include in markdown

**Integration Pattern (from apb4_slave.md):**
```markdown
