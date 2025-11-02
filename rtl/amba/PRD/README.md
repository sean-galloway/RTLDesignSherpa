# Claude AI Task Directory

This directory contains task specifications for Claude AI to assist with RTL design, verification, and documentation tasks for the AXI Monitor subsystem.

## Purpose

Breaking down complex design tasks into clear, actionable subtasks that Claude can execute autonomously while following project standards and priorities.

## Task Structure

Each task file should follow this template:

```markdown
# Task: [Task Name]

## Priority
[P0 | P1 | P2 | P3]

## Status
[Not Started | In Progress | Blocked | Complete]

## Description
[Clear description of what needs to be done]

## Prerequisites
- Prerequisite 1
- Prerequisite 2

## Existing Code to Review
**CRITICAL: Search for existing implementations BEFORE creating new code**

- [ ] Directory: [path/to/search]
- [ ] Similar modules: [list potential matches]
- [ ] Reusable components: [list existing components]

## Deliverables
1. [Specific output 1]
2. [Specific output 2]

## Verification
- [ ] Verification step 1
- [ ] Verification step 2

## Success Criteria
- Criterion 1
- Criterion 2

## Notes
[Additional context, references, constraints]
```

## Design Principles for Claude Tasks

### 1. **ALWAYS Prefer Local Code Reuse**

Before creating any new RTL:
1. ✅ Search `rtl/common/`, `rtl/amba/`, `rtl/gaxi/` for existing implementations
2. ✅ Check if similar functionality exists in related modules
3. ✅ Adapt/extend existing code rather than creating from scratch
4. ✅ Document which modules were considered and why chosen approach was selected

**Example Good Practice:**
```markdown
## Existing Code Review
- [x] Searched rtl/common/ for counter implementations
- [x] Found counter_bin.sv and counter_load_clear.sv
- [x] Decision: Reuse counter_bin.sv with custom load logic
- [x] Rationale: Existing module has desired functionality, only needs wrapper
```

### 2. Maintain Consistency

- Follow existing naming conventions (found by examining current modules)
- Use same coding style as surrounding code
- Maintain module hierarchy and interface patterns
- Reference existing documentation templates

### 3. Thorough Verification

- Every RTL change must include verification strategy
- Test both existing and new functionality
- Document test results with specific pass/fail criteria
- Include waveform analysis for complex changes

### 4. Complete Documentation

- Update all affected documentation
- Add inline comments for non-obvious logic
- Create examples for new interfaces
- Update KNOWN_ISSUES if new limitations discovered

## Current Task Priorities

### P0 (Critical) - Immediate Action Required

1. **FIX-001**: Implement event_reported feedback mechanism
   - Status: Ready to start
   - File: `TASKS/FIX-001-event-reported-feedback.md`
   - Blocks: All other verification work

### P1 (High) - Short Term

2. **DOC-001**: Complete API reference documentation
   - Status: Not started
   - File: `TASKS/DOC-001-api-reference.md`

3. **VER-001**: Create unit test infrastructure
   - Status: Not started
   - File: `TASKS/VER-001-unit-tests.md`

### P2 (Medium) - Medium Term

4. **FEAT-001**: Add address range filtering
   - Status: Not started
   - File: `TASKS/FEAT-001-address-filtering.md`

5. **FEAT-002**: Add transaction ID filtering
   - Status: Not started
   - File: `TASKS/FEAT-002-id-filtering.md`

### P3 (Low) - Long Term

6. **OPT-001**: Performance optimization analysis
   - Status: Not started
   - File: `TASKS/OPT-001-performance-analysis.md`

## Task Workflow

### 1. Task Assignment
- Review available tasks in this directory
- Select task based on priority and prerequisites
- Update task status to "In Progress"

### 2. Code Review Phase
- **MANDATORY**: Search existing codebase first
- Document existing modules considered
- Justify new code creation if applicable

### 3. Implementation Phase
- Follow task deliverables checklist
- Maintain consistency with existing code
- Add comprehensive inline documentation

### 4. Verification Phase
- Execute all verification steps
- Document test results
- Update test suite if needed

### 5. Completion
- Check all success criteria met
- Update all affected documentation
- Mark task status as "Complete"
- Create follow-up tasks if needed

## Templates

### Quick Task Template

For simple, focused tasks:

```markdown
# Task: [Name]
## Priority: [P0-P3]
## Description
[1-2 sentence description]

## Existing Code Check
- [ ] Searched: [directories]
- [ ] Reusing: [existing modules]

## Action Items
1. [Step 1]
2. [Step 2]

## Done When
- [ ] [Criterion 1]
- [ ] [Criterion 2]
```

### Complex Task Template

For multi-step engineering tasks:

See full template at top of this document.

## Common Pitfalls to Avoid

❌ **Creating new modules without searching existing code**
   → Always search first, document search results

❌ **Implementing features without clear requirements**
   → Reference PRD section and success criteria

❌ **Making changes without verification strategy**
   → Every change needs test plan

❌ **Incomplete documentation updates**
   → Update ALL affected docs, not just code

❌ **Ignoring existing code style**
   → Match existing patterns and conventions

## Tools and Commands

### Search for Existing Implementations
```bash
# Search for similar functionality
grep -r "keyword" rtl/amba/ rtl/common/

# Find module definitions
find rtl/ -name "*.sv" -exec grep "^module" {} \;

# Search for specific signals/parameters
grep -r "MAX_TRANSACTIONS" rtl/amba/
```

### Verify Compilation
```bash
# Run specific test
python val/amba/test_module.py

# Run test suite
pytest val/amba/

# Check Verilator compilation
verilator --lint-only rtl/amba/module.sv
```

### Documentation Checks
```bash
# Check markdown formatting
markdownlint docs/

# Verify internal links
find docs/ -name "*.md" -exec grep -l "](.*\.md)" {} \;
```

## Questions?

For task-specific questions or clarifications, document them in the task file under a "Questions" section. Include:
- What is unclear
- What information is needed
- Proposed approaches for consideration

## Task History

Completed tasks are moved to `TASKS/COMPLETED/` with completion date in filename for future reference.

Example: `COMPLETED/2025-09-30_FIX-001-event-reported-feedback.md`