# TASK-019: Identify Tests That Would Benefit from WaveDrom

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-020** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P3
**Status:** Complete (2025-10-11)
**Owner:** Claude AI
**Task File:** `TASK-020-identify_wavedrom_candidates.md`

**Description:**
Survey the entire test suite to identify additional tests that would significantly benefit from WaveDrom timing diagram generation.

**Completed Work:**
- Surveyed all 139 test files across 5 test directories
- Categorized tests by value (5-tier system) and implementation effort
- Created comprehensive WAVEDROM_CANDIDATE_SURVEY.md document
- Identified 38 candidate tests with detailed analysis
- Provided implementation recommendations with ROI analysis

**Survey Results:**
- **Current Coverage:** 11 tests with wavedrom (~8%)
- **High-Priority Candidates:** 8 modules identified
- **Medium-Priority Candidates:** 23 modules identified
- **Low-Priority:** 7 modules (not recommended)

**High-Priority Recommendations (Tier 1-2):**
1. **AXI-to-APB Bridge** - Protocol converter (highest value)
2. **RR PWM Arbiter + MonBus** - Arbitration visualization
3. **CDC Handshake** - Safety-critical CDC patterns
4. **APB Crossbar** - Address decode and routing
5. **Weighted RR Arbiter** - QoS scheduling
6. **APB HPET** - Complete peripheral example
7. **AXI Splitters** - Transaction management
8. **AXI4 Address Generator** - Burst patterns

**Survey Document Contents:**
- Executive summary with key findings
- Current wavedrom coverage (11 tests documented)
- Detailed analysis of 38 candidates across 5 tiers
- Implementation effort estimates (0.5 to 4 days per module)
- 3-phase implementation roadmap (quick wins → high-impact → comprehensive)
- Cost-benefit analysis with ROI rankings
- Technical implementation guidelines with code examples
- Success metrics and next steps

**Key Findings:**
- **Protocol converters** highest value (AXI-to-APB, crossbars)
- **Arbiters** excellent educational value (round-robin, weighted, PWM)
- **CDC components** safety-critical but higher effort
- **Math/combinational logic** not recommended (better as truth tables)
- **Estimated effort for all high-priority:** 4-6 weeks

**Implementation Roadmap:**
- **Phase 1 (1-2 weeks):** Quick wins - crossbar, address gen, counters, GAXI
- **Phase 2 (2-3 weeks):** High-impact - bridge, arbiters, CDC, HPET, splitters
- **Phase 3 (2-3 weeks):** Comprehensive - all arbiter variants, AXI4 family

**Success Criteria:**
- Complete survey document (WAVEDROM_CANDIDATE_SURVEY.md)
- 8 high-priority candidates identified (exceeded target of 5)
- Clear recommendations with effort estimates and ROI
- Implementation guidelines and code examples provided
- Prioritized roadmap for follow-up tasks

**Deliverable Location:** `docs/design/WAVEDROM_CANDIDATE_SURVEY.md (removed 2026-07-22 in the docs cleanup; survey content superseded by the per-book WAVES assets)`

---
