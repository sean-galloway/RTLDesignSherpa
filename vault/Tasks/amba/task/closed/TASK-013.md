# TASK-013: Create Integration Examples

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-013** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** Complete (2026-07-22) — integration guide + 2 working APB examples shipped (rtl/integ_amba/examples/). Example 3 (AXI4-to-APB bridge) and the other future examples were deferred, not delivered; reopen a new task if they are wanted. Original marker: Near Complete ~90% (2025-10-12).
**Owner:** Claude AI
**Effort:** Medium (3-4 days)
**Completion:** ~90% (2 examples complete, 1 planned)

**Description:**
Create example designs showing how to integrate monitors in real SoC environments. Focus on working APB-based examples.

**Work Completed:**

1. **Comprehensive Integration Guide**
   - rtl/integ_amba/examples/README.md (600+ lines)
   - Monitor packet format specification (64-bit structure)
   - Arbiter selection guide (round-robin, weighted, priority)
   - Downstream handling patterns (direct, FIFO, hierarchical)
   - Configuration strategies (functional, performance, production)
   - Agent ID assignment scheme
   - Integration checklist
   - Common pitfalls and solutions
   - Resource utilization estimates

2. **Example 1: APB Crossbar with Monitors**
   - File: rtl/integ_amba/examples/apbx_xbar_monitored.sv (400+ lines)
   - 3 masters × 4 slaves = 7 monitors total
   - Based on tested apbx_xbar_thin variant (PASSED)
   - Complete monitor coverage (every interface)
   - Round-robin arbiter for aggregation
   - Parameterized agent ID assignment
   - Full documentation with usage examples
   - Architecture diagrams and monitor table

3. **Example 2: Simple APB Peripheral Subsystem**
   - File: rtl/integ_amba/examples/apb4_peripheral_subsystem.sv (350+ lines)
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
- Comprehensive README.md with integration patterns (600+ lines)
- Example 1 detailed documentation (architecture, usage, testing)
- Example 2 detailed documentation (learning guide, extension patterns)
- Arbiter usage and selection guide
- Monitor bus aggregation strategies
- Best practices for packet type configuration
- Resource utilization estimates
- Integration checklist
- Common pitfalls with solutions

---
