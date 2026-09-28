# TASK-016: Add WaveDrom Support to APB Monitor Tests

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-017** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** Complete (2025-10-06)
**Owner:** Claude AI
**Task File:** `TASK-017-wavedrom_apb4_monitors.md`
**Depends On:** TASK-021 (APB monitor must be functional first)

**Description:**
Add minimal WaveDrom timing diagram generation to APB monitor tests, following the GAXI pattern. Generate clean waveforms showing key APB protocol scenarios.

**Completed Work:**
- Created APB constraints file (bin/TBClasses/wavedrom_user/apb.py) with comprehensive protocol support
- Added WaveDrom test functions to test_apb4_master.py, test_apb4_slave.py, test_apb4_slave_cdc.py
- Generated 17 WaveJSON files across 3 APB test types
- Created documentation (docs/markdown/assets/WAVES/*/README.md)
- All tests passing with WaveDrom generation enabled

**Deliverables:**
- APB Master: 3 waveforms (basic write, read, back-to-back)
- APB Slave: 7 waveforms (write, read, back-to-back writes/reads, write-to-read, read-to-write, error)
- APB Slave CDC: 7 waveforms (dual clock domain showing APB + GAXI interfaces)
- Documentation: README.md files in docs/markdown/assets/WAVES/{apb4_master,apb4_slave,apb4_slave_cdc}/

**Success Criteria:**
- 17 clean WaveJSON files generated (exceeded 3 minimum)
- APB protocol timing clearly shown (PSEL/PENABLE/PREADY)
- Original functional tests still pass
- APB slave WaveDrom test: PASSED (7 scenarios, 1690ns)

---
