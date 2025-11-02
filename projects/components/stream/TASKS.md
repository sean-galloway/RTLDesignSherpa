# STREAM Component - Task List

**Component:** STREAM (Simplified Tutorial REference Accelerator Module)
**Last Updated:** 2025-10-19
**Version:** 1.0

---

## Task Status Legend

- 🔴 **Blocked** - Cannot proceed due to dependencies or issues
- 🟠 **In Progress** - Currently being worked on
- 🟡 **Planned** - Scheduled for upcoming work
- 🟢 **Complete** - Finished and verified

## Priority Levels

- **P0** - Critical path, blocks other work
- **P1** - High priority, needed for v1.0
- **P2** - Medium priority, nice to have
- **P3** - Low priority, future enhancement

---

## Active Tasks

### TASK-001: Enhance Inline Code Comments
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Improve inline comments in STREAM RTL to better explain design choices and educational concepts.

**Acceptance Criteria:**
- [ ] Add detailed comments to descriptor format definition
- [ ] Explain simplified vs RAPIDS design choices
- [ ] Document credit mechanism in detail
- [ ] Add timing diagrams as ASCII art in comments
- [ ] Include example descriptor sequences in comments

**Dependencies:**
- None (RTL already complete)

**Related Files:**
- `rtl/stream/*.sv`

---

### TASK-002: Create Tutorial Documentation
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Create comprehensive tutorial guide comparing STREAM (simplified) with RAPIDS (full-featured).

**Acceptance Criteria:**
- [ ] Create tutorial comparing STREAM vs RAPIDS architecture
- [ ] Document simplified descriptor format
- [ ] Explain single data path vs dual data path
- [ ] Create side-by-side comparison table
- [ ] Add learning objectives for each section

**Dependencies:**
- None

**Related Files:**
- `docs/stream_spec/tutorial/stream_vs_rapids.md` (to be created)

---

### TASK-003: Add Example Usage Scenarios
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document common usage scenarios for STREAM with code examples.

**Acceptance Criteria:**
- [ ] Create simple memory copy example
- [ ] Create basic scatter-gather example
- [ ] Document descriptor chaining pattern
- [ ] Add AXI transaction timing examples
- [ ] Include CocoTB test snippets

**Dependencies:**
- None

**Related Files:**
- `docs/stream_spec/examples/` (to be created)

---

### TASK-004: Comparison Matrix with RAPIDS
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create detailed comparison matrix highlighting differences between STREAM and RAPIDS.

**Acceptance Criteria:**
- [ ] Create feature comparison table (descriptor format, data paths, FSMs, monitoring, etc.)
- [ ] Document complexity metrics (LOC, FSM states, signal count)
- [ ] Compare resource usage (FPGA/ASIC estimates)
- [ ] Highlight learning progression path
- [ ] Add "when to use STREAM vs RAPIDS" decision guide

**Dependencies:**
- None

**Related Files:**
- `docs/stream_vs_rapids_comparison.md` (to be created)

---

### TASK-005: Enhance Test Documentation
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Improve test documentation to explain verification methodology for educational purposes.

**Acceptance Criteria:**
- [ ] Add detailed test plan documentation
- [ ] Document test scenarios and coverage goals
- [ ] Explain testbench architecture
- [ ] Add annotations to existing tests for learning
- [ ] Create test writing guide for beginners

**Dependencies:**
- None

**Related Files:**
- `val/stream/test_*.py`
- `docs/stream_spec/verification_guide.md` (to be created)

---

### TASK-006: Wavedrom Timing Diagrams
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create wavedrom JSON files illustrating key STREAM operations.

**Acceptance Criteria:**
- [ ] Create descriptor_fetch.json (APB read of descriptor)
- [ ] Create axi_read_operation.json (simplified read)
- [ ] Create axi_write_operation.json (simplified write)
- [ ] Create credit_update.json (credit flow control)
- [ ] Generate SVG/PNG from all JSON files
- [ ] Place in docs/stream_spec/assets/waves/

**Dependencies:**
- None

**Related Files:**
- `docs/stream_spec/assets/waves/*.json`

---

### TASK-007: PlantUML FSM Diagrams
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create PlantUML state machine diagrams for STREAM FSMs (simplified vs RAPIDS comparison).

**Acceptance Criteria:**
- [ ] Create stream_descriptor_engine_fsm.puml
- [ ] Create stream_axi_read_fsm.puml
- [ ] Create stream_axi_write_fsm.puml
- [ ] Add annotations comparing with RAPIDS FSMs
- [ ] Generate PNG/SVG from all PUML files
- [ ] Place in docs/stream_spec/assets/puml/

**Dependencies:**
- None

**Related Files:**
- `docs/stream_spec/assets/puml/*.puml`

---

### TASK-008: Block Diagrams and Architecture Images
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create block diagrams and architecture illustrations for STREAM documentation.

**Acceptance Criteria:**
- [ ] Create stream_architecture.svg (top-level block diagram)
- [ ] Create simplified_descriptor_format.svg
- [ ] Create stream_vs_rapids_architecture_comparison.svg
- [ ] Create data_flow_diagram.svg
- [ ] Place in docs/stream_spec/assets/images/

**Dependencies:**
- None

**Related Files:**
- `docs/stream_spec/assets/images/*.svg`

---

### TASK-009: Create Learning Path Guide
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Create step-by-step learning guide for studying STREAM before moving to RAPIDS.

**Acceptance Criteria:**
- [ ] Define learning objectives for each chapter
- [ ] Create progression: STREAM → RAPIDS migration path
- [ ] Add hands-on exercises (modify STREAM, observe behavior)
- [ ] Include quiz questions for self-assessment
- [ ] Document common pitfalls and debugging tips

**Dependencies:**
- TASK-002 (Tutorial documentation)

**Related Files:**
- `docs/stream_spec/learning_guide.md` (to be created)

---

### TASK-010: Performance Characterization Documentation
**Status:** 🟡 Planned
**Priority:** P3
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document STREAM performance characteristics (latency, throughput) for educational reference.

**Acceptance Criteria:**
- [ ] Measure descriptor fetch latency
- [ ] Measure AXI read/write transaction timing
- [ ] Compare with RAPIDS performance metrics
- [ ] Create performance comparison graphs
- [ ] Document performance trade-offs of simplified design

**Dependencies:**
- None

**Related Files:**
- `docs/stream_spec/performance_analysis.md` (to be created)

---

## Recently Completed Tasks

### ✅ TASK-000: Core STREAM Implementation (Complete - 2025-10-10)
- Implemented simplified descriptor engine
- Implemented unified data path (read/write)
- Created basic AXI master interfaces
- Added minimal credit management
- Implemented basic monitoring
- Created comprehensive CocoTB testbenches
- Verified functional operation

### ✅ TASK-001-PREV: Initial Documentation (Complete - 2025-10-12)
- Created PRD.md with design goals
- Created CLAUDE.md with guidance
- Documented simplified architecture
- Added quick reference sections

---

## Future Enhancements (Backlog)

### TASK-011: Interactive Tutorial
**Priority:** P3
**Description:** Create web-based interactive tutorial with embedded waveform viewer and code editor.

### TASK-012: Video Tutorial Series
**Priority:** P3
**Description:** Record video walkthrough of STREAM architecture and comparison with RAPIDS.

### TASK-013: Jupyter Notebook Examples
**Priority:** P3
**Description:** Create Jupyter notebooks demonstrating STREAM simulation with CocoTB and analysis.

### TASK-014: FPGA Synthesis Tutorial
**Priority:** P3
**Description:** Create step-by-step guide for synthesizing STREAM on FPGA and running on hardware.

### TASK-015: Advanced Exercises
**Priority:** P3
**Description:** Create advanced exercises for extending STREAM (e.g., add scatter-gather, add interrupts).

---

## Task Dependencies

```
TASK-001 (Enhance Comments) - Independent
TASK-002 (Tutorial Docs)
    └─> TASK-009 (Learning Path Guide)

TASK-003 (Usage Scenarios) - Independent
TASK-004 (Comparison Matrix) - Independent
TASK-005 (Test Docs) - Independent
TASK-006 (Wavedrom) - Independent
TASK-007 (PlantUML) - Independent
TASK-008 (Block Diagrams) - Independent
TASK-010 (Performance Docs) - Independent
```

---

## Quick Commands

### Run Specification to PDF (when spec exists)
```bash
python bin/md_to_docx.py \
    projects/components/stream/docs/stream_spec/stream_index.md \
    -o projects/components/stream/docs/STREAM_Specification_v1.0.docx \
    --toc --title-page --pdf
```

### Run STREAM Tests
```bash
# Run all STREAM tests
pytest val/stream/ -v

# Run specific test
pytest val/stream/test_stream_basic.py -v
```

### Lint STREAM RTL
```bash
verilator --lint-only rtl/stream/stream_top.sv
```

### Generate Wavedrom SVG
```bash
wavedrom-cli -i docs/stream_spec/assets/waves/descriptor_fetch.json \
             -s docs/stream_spec/assets/waves/descriptor_fetch.svg
```

### Generate PlantUML PNG
```bash
plantuml docs/stream_spec/assets/puml/stream_descriptor_engine_fsm.puml
```

### Compare with RAPIDS
```bash
# Line count comparison
wc -l rtl/stream/*.sv rtl/rapids/*.sv

# Signal count comparison
grep -h "input\|output\|inout" rtl/stream/*.sv | wc -l
grep -h "input\|output\|inout" rtl/rapids/*.sv | wc -l
```

---

## Learning Objectives

STREAM is designed as an educational stepping stone to RAPIDS. Key learning objectives:

1. **Understand DMA Basics** - Learn descriptor-based DMA concepts
2. **Grasp AXI Protocol** - Understand AXI read/write transaction flow
3. **Learn FSM Design** - Study simplified state machines
4. **Appreciate Simplification Trade-offs** - Understand what was simplified and why
5. **Prepare for RAPIDS** - Build foundation for full-featured design

**Progression Path:**
1. Study STREAM architecture and implementation
2. Run STREAM tests and observe waveforms
3. Modify STREAM (exercises)
4. Compare STREAM vs RAPIDS side-by-side
5. Study RAPIDS architecture (building on STREAM knowledge)

---

**Last Review:** 2025-10-19
**Next Review:** Quarterly or when adding new tutorial content
