# Claude Code Guide for RTL Design Sherpa

**Version:** 1.1
**Last Updated:** 2026-07-22
**Purpose:** Help Claude Code work efficiently with this repository

---

## The Handbook (repo memory) - READ THIS FIRST

**`vault/handbook/INDEX.md` is the SINGLE SOURCE OF TRUTH for every skill and
method in this repository.** It is the repo's working memory: design rules
(`design/`), DV practice (`dv/`), FPGA process (`fpga/`), and documentation
practice (`authoring/`) as atomic, wikilinked notes - each rule recorded WITH
the failure that taught it.

- **Skills (`.claude/skills/`, auto-discovered) are signposts only.** A skill
  names its canonical handbook note and stops. Method detail does not live in
  a skill file.
- **Methodology does not live next to the code.** No `README.md` beside a tool
  restating how to use it, no how-to in a docstring beyond what a reader of
  that one file needs, and no canonical process document outside the repo. A
  second copy is how documentation rots - the copy nobody edits is the one the
  next session reads. Point at the handbook note instead.
- /GLOBAL_REQUIREMENTS.md remains the enforcement authority and wins on conflict.
- When you learn a durable lesson, add it to the relevant handbook note -
  that is where future sessions will look. If no note fits, create one and
  index it; do not park the lesson in a CLAUDE.md or a skill.

## 📖 Global Requirements Reference

**IMPORTANT: All mandatory requirements are consolidated in `/GLOBAL_REQUIREMENTS.md`**

Before working in this repository, review the global requirements document:
- **Location:** `/GLOBAL_REQUIREMENTS.md`
- **Contents:** All MANDATORY requirements extracted from all CLAUDE.md files
- **Organization:** Categorized by RTL standards, testbench architecture, test standards, framework usage, and documentation

This CLAUDE.md provides repository-wide guidance and examples. For subsystem-specific details, see:
- `projects/components/CLAUDE.md` - Project area standards
- `projects/components/{name}/CLAUDE.md` - Component-specific guidance
- `rtl/{subsystem}/CLAUDE.md` - Subsystem-specific guidance
- DV framework patterns: shared TB classes live in `bin/TBClasses/`; the full CocoTB framework (BFMs, monitors) is the separate RTLDesignSherpa-DV repo (editable-installed into the venv)

---

## 🚨 CRITICAL RULE #0: Generated File Regeneration Requirements 🚨

**⚠️ READ THIS FIRST - FAILURE TO FOLLOW CAUSES SILENT TEST FAILURES ⚠️**

### The Absolute Rule for Generated Code

**When ANY generator code changes, you MUST delete ALL generated files and regenerate everything from scratch.**

This applies to:
- **RTL generators** (bridge_generator.py, bridge_csv_generator.py, etc.)
- **Test generators** (bridge_test_generator.py, etc.)
- **Testbench generators** (any code that generates .py or .sv files)

### Why This Is Non-Negotiable

Generated files have interdependencies:
- Wrapper RTL may instantiate core RTL
- Tests may import testbench classes
- Signal names, port widths, interfaces must match across all files
- **Partial regeneration creates version mismatches causing silent failures**

### The Workflow - ALWAYS Follow This Pattern

```bash
# ❌ WRONG - Partial regeneration
vim bridge_csv_generator.py  # Make changes
python3 bridge_csv_generator.py --config 4x4  # Regenerate ONE file
# Result: Version mismatch, tests mysteriously fail!

# ✅ CORRECT - Full regeneration
vim bridge_csv_generator.py  # Make changes

# Step 1: DELETE ALL generated files
cd projects/components/bridge/rtl
rm bridge_*.sv  # Or be more selective, but delete EVERYTHING generated
cd ../dv/tests
rm test_bridge_*_generated.py  # If test generator changed
cd ../tbclasses
rm *_generated*.py  # If TB generator changed

# Step 2: Regenerate EVERYTHING
cd ../../bin
./regenerate_all_bridges.sh  # Or manually regenerate each config

# Step 3: Verify ALL tests
cd ../dv/tests
pytest -v  # Run ALL tests, not just the one you think changed
```

### What Counts as "Generator Code"?

**Any Python file that creates .sv or .py files:**
- ✅ `bridge_generator.py` - Triggers full bridge regeneration
- ✅ `bridge_csv_generator.py` - Triggers full bridge regeneration
- ✅ `bridge_test_generator.py` - Triggers full test regeneration
- ✅ `bridge_address_arbiter.py` - Triggers full regeneration (imported by generators)
- ✅ **ANY** module imported by a generator

**When in doubt:** Delete and regenerate everything.

### Symptoms of Partial Regeneration

If you see these, you probably did partial regeneration:
- ❌ Tests that previously passed now fail
- ❌ "Signal not found" errors in simulation
- ❌ Port width mismatches
- ❌ Unexpected routing behavior
- ❌ Missing debug signals
- ❌ Tests marked as xfail still failing after fix implemented

### Think Like a Compiler Developer

Generated code is like compiled object files. When you update a compiler, you run `make clean && make all`, not selective recompilation.

When you update a generator, you **delete all generated outputs and regenerate all**.

**This is not a suggestion. This is a HARD REQUIREMENT that will be enforced.**

---

## 🚨 CRITICAL RULE #0.1: Generated File Directory Organization 🚨

**⚠️ ALL GENERATED FILES MUST BE IN NAMED SUBDIRECTORIES ⚠️**

### The Absolute Rule

**Generated code MUST ALWAYS be in its associated named directory. NEVER at the top level.**

```bash
# ✅ CORRECT - Generated files in subdirectories
projects/components/bridge/rtl/generated/bridge_4x4_rw/bridge_4x4_rw.sv
projects/components/bridge/rtl/generated/bridge_4x4_rw/bridge_4x4_rw_xbar.sv

# ❌ WRONG - Generated files at top level
projects/components/bridge/rtl/bridge_4x4_rw.sv       # WRONG!
projects/components/bridge/rtl/bridge_4x4_rw_xbar.sv  # WRONG!
```

### Why This Matters

1. **Easy cleanup** - Delete entire subdirectory to remove all generated files
2. **No confusion** - Hand-written files stay at top level, generated files in subdirs
3. **Version control** - Clear .gitignore patterns
4. **Parallel work** - Different configs don't conflict

### Hand-Written vs Generated

**Hand-written files (top level):**
```bash
projects/components/bridge/rtl/bridge_cam.sv          # Hand-written CAM module
projects/components/bridge/rtl/Makefile               # Build script
```

**Generated files (subdirectories):**
```bash
projects/components/bridge/rtl/generated/bridge_4x4_rw/   # All 4x4 generated files
projects/components/bridge/rtl/generated/bridge_2x2_rw/   # All 2x2 generated files
```

### Enforcement

If you find generated files at the top level:
1. **STOP** - This is an error
2. **DELETE** stale top-level generated files
3. **REGENERATE** properly into subdirectories
4. **UPDATE** clean targets to catch this

**This is a HARD REQUIREMENT - NO EXCEPTIONS.**

---

## 📖 Organizational Requirements - See Global Requirements

**⚠️ READ THIS BEFORE WRITING ANY TESTBENCH CODE ⚠️**

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1 for complete TB location requirements

**Quick Summary - Project-Specific TB Classes:**
- **RAPIDS:** `projects/components/dmas/rapids/dv/tbclasses/` ✅
- **STREAM:** `projects/components/dmas/stream/dv/tbclasses/` ✅
- **Bridge:** `projects/components/bridge/dv/tbclasses/` ✅
- **Framework (shared only):** `bin/TBClasses/` ✅

**Import Pattern:**
```python
# Project-specific TBs
from projects.components.dmas.rapids.dv.tbclasses.scheduler_tb import SchedulerTB

# Shared infrastructure
from TBClasses.shared.tbbase import TBBase
```

**Complete details:** Decision trees, anti-patterns, and rationale in `/GLOBAL_REQUIREMENTS.md`

---

## Workflow for Claude Code

### Starting a New Session

1. **Read the PRD** for the subsystem you're working on:
   - Root `/PRD.md` - Overall project goals
   - `rtl/{subsystem}/PRD.md` - Subsystem-specific requirements

2. **Check TASKS.md** for current priorities:
   - `rtl/{subsystem}/TASKS.md` - Active work items
   - Understand dependencies and status

3. **Review KNOWN_ISSUES/** before modifying RTL:
   - `rtl/{subsystem}/KNOWN_ISSUES/` - Documented bugs and workarounds
   - Avoid wasting time on known limitations

4. **Read subsystem CLAUDE.md** for specific guidance:
   - `rtl/{subsystem}/CLAUDE.md` - Module-specific tips
   - Common patterns and anti-patterns

### Before Creating New RTL

**CRITICAL: Always search for existing implementations first!**

```bash
# Search for similar functionality
find rtl/ -name "*.sv" | xargs grep -l "keyword"

# Find module definitions
find rtl/{subsystem}/ -name "*.sv" -exec grep -H "^module" {} \;

# Search for specific signals/parameters
grep -r "MAX_TRANSACTIONS\|FIFO_DEPTH\|ADDR_WIDTH" rtl/

# Check test usage examples
grep -r "module_name" val/
```

**Decision Tree:**
- ✅ Existing module found → Reuse with parameters
- ✅ Existing module close → Adapt/extend it
- ⚠️ Existing module insufficient → Document why, then create new
- ❌ No search performed → STOP, search first!

### Before Writing Testbenches - Check Signal Naming

**CRITICAL: Audit RTL for signal naming conflicts BEFORE writing testbench code!**

When using AXI factory functions with pattern matching, internal signals can conflict with external AXI port names, causing factory initialization failures.

**Run the Signal Naming Audit Tool:**

```bash
# Audit single file before writing testbench
./bin/audit_signal_naming_conflicts.py projects/components/dmas/rapids/rtl/macro_beats/scheduler_group_beats.sv

# Audit entire directory
./bin/audit_signal_naming_conflicts.py projects/components/dmas/rapids/rtl/

# Generate markdown report for documentation
./bin/audit_signal_naming_conflicts.py projects/components/dmas/rapids/rtl/ --markdown projects/components/dmas/rapids/rtl/signal_conflicts.md
```

**Why This Matters:**

AXI factory pattern matching searches for signals like `{prefix}ar_valid`, `{prefix}r_ready`, etc. If you have:
- Internal: `desc_valid`, `desc_ready` (simple handshake)
- External: `desc_ar_valid`, `desc_ar_ready` (AXI AR channel)

Both match the pattern `desc_*valid` → Factory finds BOTH signals → Initialization fails!

**Workflow:**
1. ✅ Write RTL module
2. ✅ **Run audit script to detect conflicts**
3. ✅ Fix any naming conflicts (rename internal signals)
4. ✅ Write testbench using factory pattern matching

**📖 Complete Guide:** `bin/SIGNAL_NAMING_AUDIT.md`

### Writing RTL

**Style Conventions:**
- **Module names:** `{category}_{function}.sv` (e.g., `counter_bin.sv`, `axi_monitor_base.sv`)
- **Parameters:** `UPPER_CASE` (e.g., `WIDTH`, `DEPTH`, `MAX_TRANSACTIONS`)
- **Ports:** `snake_case` with prefix
  - Inputs: `i_*` (e.g., `i_clk`, `i_data`)
  - Outputs: `o_*` (e.g., `o_valid`, `o_result`)
  - Bidirectional: `io_*`
- **Internal signals:** `snake_case` with prefix
  - Registers: `r_*` (e.g., `r_counter`, `r_state`)
  - Wires: `w_*` (e.g., `w_sum`, `w_match`)
- **Reset:** Always `aresetn` (active-low asynchronous reset)
- **Clock:** `aclk` for AXI/AMBA, `i_clk` for common modules

### Writing Tests

Test structure for this repo -- Pattern A vs Pattern B, the `cocotb_test_*`
prefix rule, pytest function naming, the three mandatory TB methods, and the
gate/func/full level convention -- is the `test-patterns` skill. It is loaded on
demand rather than every session; invoke it before writing or changing a test.

`/GLOBAL_REQUIREMENTS.md` remains the enforcement authority.

### Documentation Requirements

**Update ALL affected documentation:**

1. **Inline Comments:**
   - Complex logic needs explanation
   - FSM states documented
   - Parameter constraints noted
   - Interface timing requirements

2. **Module Header:**
```systemverilog
// Module: module_name
// Description: Brief description of functionality
// Parameters:
//   - PARAM1: Description, valid range, default
//   - PARAM2: Description, valid range, default
// Notes:
//   - Special constraints or assumptions
//   - Related modules or dependencies
```

3. **Update PRD.md** when:
   - Adding major features
   - Changing requirements
   - Reaching milestones

4. **Update TASKS.md** when:
   - Starting new work
   - Completing tasks
   - Discovering new issues

5. **Update KNOWN_ISSUES/** when:
   - Finding bugs
   - Identifying workarounds
   - Closing issues

6. **CRITICAL: No emojis in technical specifications**
   - Emojis break PDF generation tools (LaTeX)
   - Appear unprofessional in formal documentation
   - Use plain text for all technical documentation
   - Exception: User explicitly requests emojis (rare)

---

## Critical Gotchas and Warnings

### AMBA Subsystem

⚠️ **AXI Monitor Packet Congestion**
- **Issue:** Enabling all packet types simultaneously overwhelms monitor bus
- **Solution:** Use separate test configurations (see `docs/user-guides/AXI_Monitor_Configuration_Guide.md`)
- **Rule:** Never enable `cfg_compl_enable` and `cfg_perf_enable` together

⚠️ **Event Reported Feedback**
- **Status:** Fixed (historical)
- **History:** Transaction table exhaustion due to missing feedback
- **Verification:** Current monitor issues are tracked in `rtl/amba/KNOWN_ISSUES/`
  (the old axi_monitor_reporter issue page was retired; the reporter module doc is
  `docs/markdown/rtl-amba/monitor/axi_monitor_reporter.md`)

### RAPIDS Subsystem

⚠️ **Scheduler Credit Counter Bug (historical, pre-beats scheduler)**
- **Issue:** Credit counter initialized to 0 instead of `cfg_initial_credit`
- **Status:** Obsolete - the rearchitected beats scheduler
  (`projects/components/dmas/rapids/rtl/fub_beats/scheduler_beats.sv`) has no credit
  management yet; current issues are tracked in `projects/components/dmas/rapids/known_issues/`

### General RTL

⚠️ **Reset Convention**
- Always use `aresetn` (active-low asynchronous reset)
- Never use `rst` or `reset` (positive reset)
- Synchronize resets internally if needed

⚠️ **Parameter Overrides**
- Check instantiation parameters match module definition
- Document parameter dependencies (e.g., `DATA_WIDTH` must be power of 2)
- Use `localparam` for derived parameters

⚠️ **FIFO Depth**
- Always make FIFO depths power of 2 for efficient addressing
- Document minimum depth requirements
- Consider backpressure scenarios

---

**Version History:**
- v1.0 (2025-09-30): Initial creation
- v1.1 (2026-07-22): Path refresh - dmas relocation (projects/components/dmas/), RAPIDS beats
  rearchitecture, monitor move to rtl/amba/monitor/, math split to rtl/math/, TBClasses layout
- v1.2 (2026-08-31): Trimmed to what a session cannot derive. Removed the directory
  tree, subsystem module inventories, quick-reference tables, generic SystemVerilog
  patterns, standard tool invocations and the reference/FAQ tails - all reconstructible
  with `ls` and a manifest, and all already drifting (this file claimed ~156 files in
  bin/TBClasses; there were 248). Test structure moved to the `test-patterns` skill so it
  loads when a test is in scope rather than every session. 1032 -> 400 lines. What stayed
  is what the codebase cannot tell you: the regeneration rules, TB placement, naming and
  reset conventions, and the gotchas.

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2026-07-22
