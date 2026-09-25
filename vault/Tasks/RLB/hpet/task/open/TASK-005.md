# TASK-005: no HPET integration examples
> Migrated 2026-09-25 from `projects/components/retro_legacy_blocks/TASKS.md` as **TASK-006** (tooling TOOL-001). That file numbered its own items TASK-001..006, which collide with RLB-001..017 on the frozen legacy page; per-lane IDs replace them. Body preserved as written except the Status line.

**Priority:** P2
**Status:** open. Confirmed 2026-09-25: no integration or example page
exists under `docs/hpet_mas/`.
**Owner:** TBD

**Description:**
Create comprehensive integration examples showing how to use APB HPET in different system contexts.

**Examples to Create:**

1. **Basic Integration (1-2 hours)**
   - Simple 2-timer system
   - APB slave connection
   - Interrupt handling
   - Basic timer configuration

2. **Multi-Timer System (1-2 hours)**
   - 8-timer configuration
   - Different timer modes (one-shot, periodic)
   - Interrupt prioritization
   - Timer coordination

3. **CDC Integration (1-2 hours)**
   - Asynchronous clock domains
   - APB clock vs. HPET clock
   - Clock crossing considerations
   - Performance implications

4. **Software Driver Example (1-2 hours)**
   - C header file definitions
   - Initialization sequence
   - Timer configuration functions
   - Interrupt service routine

**File Structure:**
```
projects/components/retro_legacy_blocks/examples/
├── basic_integration/
│   ├── system_top.sv
│   ├── testbench.sv
│   └── README.md
├── multi_timer/
│   ├── system_top.sv
│   ├── testbench.sv
│   └── README.md
├── cdc_integration/
│   ├── system_top.sv
│   ├── testbench.sv
│   └── README.md
└── software/
    ├── hpet_driver.h
    ├── hpet_driver.c
    └── README.md
```

**Verification Steps:**
1. Create example directories and files
2. Test each example with Verilator
3. Verify: All examples compile and simulate
4. Document: Usage instructions in READMEs
5. Review: Completeness and clarity

**Related Files:**
- Create: `projects/components/retro_legacy_blocks/examples/` directory and contents
- Update: `projects/components/retro_legacy_blocks/PRD.md` with links to examples

**Dependencies:** None

**Completion Criteria:**
- [ ] All example files created
- [ ] Examples compile and simulate
- [ ] Documentation complete
- [ ] PRD.md updated with links

**Notes:**
- Important for users integrating HPET
- Helps demonstrate capabilities
- Reduces integration errors

---
