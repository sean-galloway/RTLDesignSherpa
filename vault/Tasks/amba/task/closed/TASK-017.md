# TASK-017: Add WaveDrom Support to AXI4 Monitor Tests

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-018** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** Complete (2025-10-11)
**Owner:** Claude AI
**Task File:** `TASK-018-wavedrom_axi4_monitors.md`
**Depends On:** TASK-016 (complete)

**Description:**
Add minimal WaveDrom timing diagram generation to AXI4 monitor tests. Generate waveforms showing single-beat transactions from both master and slave perspectives.

**Completed Work:**
- Added WaveDrom tests for all 4 AXI4 monitor types
- Generated 8 WaveJSON files (2 per monitor type)
- Created comprehensive documentation with READMEs
- All tests passing with regression protection

**Deliverables:**
- AXI4 Master Read Monitor: 2 waveforms (single_beat_read_001.json, single_beat_read_002_001.json)
- AXI4 Master Write Monitor: 2 waveforms (single_beat_write_001.json, single_beat_write_002_001.json)
- AXI4 Slave Read Monitor: 2 waveforms (single_beat_read_001.json, single_beat_read_002_001.json)
- AXI4 Slave Write Monitor: 2 waveforms (single_beat_write_001.json, single_beat_write_002_001.json)
- Documentation: docs/markdown/assets/WAVES/{monitor_name}/README.md for each

**Generated Waveforms:**
- Master monitors: Show m_axi_* signals (master interface) + monbus
- Slave monitors: Show s_axi_* signals (slave interface) + monbus
- All waveforms: Complete transaction flow with multi-channel timing

**Success Criteria:**
- 8 WaveJSON files generated (2 per monitor)
- Multi-channel AXI4 timing clearly shown
- Labeled groups for AR/R or AW/W/B channels
- Constraint-based generation for regression testing
- Comprehensive documentation created

**Key Implementation Details:**
- Manual signal binding used (not auto-bind) for all channels
- SignalTransition constraints on arvalid/awvalid (0→1) triggers
- 80-cycle capture window with 20 post-match cycles for monbus
- Tests use appropriate APIs: master uses single_*_test(), slave uses single_*_response_test()

---
