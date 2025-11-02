# Delta: AXI-Stream Crossbar Generator - Product Requirements Document

**Project:** Delta
**Version:** 1.0
**Date:** 2025-10-18
**Status:** Active Development

---

## Executive Summary

**Delta** is an AXI-Stream crossbar generator that produces parameterized RTL for routing data between multiple masters and multiple slaves. The name "Delta" follows the water/river theme (like RAPIDS) - deltas are where rivers split into multiple branches, analogous to crossbar routing.

**Key Features:**
- Python-based RTL generation (similar to APB crossbar automation)
- Dual topology support: Flat crossbar (low latency) and Tree (modular/scalable)
- Performance modeling (analytical + simulation)
- Complete AXI-Stream protocol compliance
- Educational focus with rigorous specifications

---

## 1. Project Goals

### 1.1 Primary Goals

1. **Code Generation Excellence**
   - Python generator produces clean, parameterized SystemVerilog
   - Reuses patterns from existing APB crossbar automation (~95% code reuse)
   - Single tool generates multiple topologies

2. **Performance Rigor**
   - Analytical models (closed-form latency/throughput)
   - Discrete event simulation (SimPy)
   - Resource estimation
   - Validation against RTL synthesis

3. **Educational Value**
   - Demonstrates specification-driven design
   - Shows code generation techniques
   - Compares topology trade-offs
   - Suitable for instruction on GitHub

4. **Integration Ready**
   - Works with existing CocoTBFramework
   - Compatible with RAPIDS subsystem
   - Supports RISC core + DSP array use case

### 1.2 Non-Goals

- Vendor-specific IP (using custom generators only)
- Protocol conversion (AXIS only, not AXI4/APB)
- Advanced routing algorithms (static TDEST-based only)
- Dynamic reconfiguration

---

## 2. Architecture

### 2.1 Flat Crossbar Topology

**Description:** Full MxN crossbar with per-slave arbiters

**Characteristics:**
- **Latency:** 2 cycles (arbitration + output register)
- **Throughput:** High aggregate (each slave independent)
- **Resources:** ~1,920 LUTs for 4x16 @ 64-bit
- **Best For:** Production systems requiring low latency

**Block Diagram:**
```
Masters (M)          Arbiters (N)         Slaves (N)

M0 ------+----------+-[Arbiter_S0]----- S0
         |          |
M1 ------+          +-[Arbiter_S1]----- S1
         |          |
M2 ------+          +-[Arbiter_S2]----- S2
         |          |
M3 ------+          +-[Arbiter_S15]---- S15

Request Matrix      Grant Matrix
(decode TDEST)      (round-robin)
```

### 2.2 Tree Topology

**Description:** Hierarchical composition of 1:2 splitters and 2:1 mergers

**Characteristics:**
- **Latency:** 4-6 cycles (multi-stage pipeline)
- **Throughput:** Lower aggregate (bottleneck at root)
- **Resources:** ~1,600 LUTs for 4x16 @ 64-bit (fewer LUTs but more instances)
- **Best For:** Educational examples, demonstrating modularity

**Block Diagram:**
```
Masters     Mergers        Splitters       Slaves

M0 --+
     +-[2:1]--[1:2]--+-[1:2]--+- S0
M1 --+              |         +- S1
                    |
M2 --+              +-[1:2]--+- S2
     +-[2:1]--------+         +- S3
M3 --+

Tree depth: log2(N) stages
```

---

## 3. Functional Requirements

### 3.1 Code Generation

**REQ-GEN-001:** Python generator shall produce SystemVerilog RTL
- **Input:** Command-line parameters (masters, slaves, data width, topology)
- **Output:** Synthesizable SystemVerilog modules
- **Verification:** Verilator lint clean, synthesis clean

**REQ-GEN-002:** Generator shall support both flat and tree topologies
- **Flat:** Single crossbar module
- **Tree:** Hierarchical node composition
- **Both:** Generate both variants with `--topology both`

**REQ-GEN-003:** Generated RTL shall be parameterized
- NUM_MASTERS, NUM_SLAVES (up to 32x256)
- DATA_WIDTH (8, 16, 32, 64, 128, 256, 512, 1024 bits)
- DEST_WIDTH, ID_WIDTH (auto-calculated)

**REQ-GEN-004:** Generator shall follow APB crossbar patterns
- ~95% code reuse from APB automation
- Same request generation, arbitration, mux patterns
- Signal name mapping (pclk->aclk, psel->tvalid, etc.)

### 3.2 Performance Modeling

**REQ-MODEL-001:** Analytical model shall provide closed-form results
- Latency calculation (cycles and nanoseconds)
- Throughput estimation (transfers/cycle, Gbps)
- Resource estimation (LUTs, FFs)

**REQ-MODEL-002:** Simulation model shall use discrete event simulation
- SimPy-based cycle-accurate model
- Statistical analysis (mean, percentiles)
- Traffic pattern support (uniform, hotspot, localized)

**REQ-MODEL-003:** Models shall be validated against RTL
- Compare analytical vs simulation results
- Validate against synthesis reports
- Document discrepancies

### 3.3 Protocol Compliance

**REQ-PROTO-001:** Generated RTL shall comply with AXI-Stream specification
- TVALID/TREADY handshaking
- TLAST packet boundaries
- TDEST, TID, TUSER sideband signals

**REQ-PROTO-002:** Arbitration shall provide packet atomicity
- Grant locked until TLAST
- No packet interleaving
- Fair round-robin arbitration

**REQ-PROTO-003:** Backpressure shall propagate correctly
- TREADY from slave to granted master
- No deadlocks
- No data loss

---

## 4. Non-Functional Requirements

### 4.1 Performance Targets

**NFR-PERF-001:** Flat crossbar latency <= 2 cycles
**NFR-PERF-002:** Flat crossbar Fmax >= 300 MHz (UltraScale+)
**NFR-PERF-003:** Tree topology latency <= 6 cycles
**NFR-PERF-004:** Throughput >= 0.7 transfers/cycle under mixed traffic

### 4.2 Resource Targets

**NFR-RES-001:** Flat 4x16 @ 64-bit <= 2,500 LUTs
**NFR-RES-002:** Tree 4x16 @ 64-bit <= 2,000 LUTs
**NFR-RES-003:** No BRAM usage (pure logic implementation)

### 4.3 Code Quality

**NFR-QUAL-001:** Generated RTL shall pass Verilator lint
**NFR-QUAL-002:** Generator code shall follow PEP 8 style
**NFR-QUAL-003:** Comprehensive inline documentation
**NFR-QUAL-004:** Assertions for formal verification

---

## 5. Interface Specifications

### 5.1 AXI-Stream Master Interface (S_AXIS)

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `s_axis_tdata[m]` | DATA_WIDTH | Input | Data payload |
| `s_axis_tvalid[m]` | 1 | Input | Valid indicator |
| `s_axis_tready[m]` | 1 | Output | Ready (backpressure) |
| `s_axis_tlast[m]` | 1 | Input | Packet boundary |
| `s_axis_tdest[m]` | DEST_WIDTH | Input | Target slave ID |
| `s_axis_tid[m]` | ID_WIDTH | Input | Transaction ID |
| `s_axis_tuser[m]` | USER_WIDTH | Input | User sideband |

**Array:** `[NUM_MASTERS]` (one per master)

### 5.2 AXI-Stream Slave Interface (M_AXIS)

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `m_axis_tdata[s]` | DATA_WIDTH | Output | Data payload |
| `m_axis_tvalid[s]` | 1 | Output | Valid indicator |
| `m_axis_tready[s]` | 1 | Input | Ready (backpressure) |
| `m_axis_tlast[s]` | 1 | Output | Packet boundary |
| `m_axis_tdest[s]` | DEST_WIDTH | Output | Target slave ID (pass-through) |
| `m_axis_tid[s]` | ID_WIDTH | Output | Transaction ID (pass-through) |
| `m_axis_tuser[s]` | USER_WIDTH | Output | User sideband (pass-through) |

**Array:** `[NUM_SLAVES]` (one per slave)

### 5.3 Clock and Reset

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `aclk` | 1 | Input | Clock |
| `aresetn` | 1 | Input | Active-low reset |

---

## 6. Key Design Decisions

### 6.1 Why AXI-Stream vs AXI4?

**Decision:** Use AXI-Stream instead of full AXI4

**Rationale:**
- Streaming workloads (RISC cores, DSP arrays)
- Simpler protocol (no address phases, burst management)
- Better fit for compute fabrics
- Still allows future upgrade to AXI4 if needed

### 6.2 Why Round-Robin vs Fixed Priority?

**Decision:** Default to round-robin arbitration

**Rationale:**
- Fair bandwidth allocation
- No starvation
- Suitable for general-purpose compute
- Can add fixed-priority mode later if needed

### 6.3 Why Flat AND Tree Topologies?

**Decision:** Support both, not either/or

**Rationale:**
- Flat for production (low latency, high throughput)
- Tree for education (modular, demonstrates composition)
- Python generator makes both easy (~zero extra cost)
- Shows trade-off analysis

### 6.4 Why Python Generator vs Manual RTL?

**Decision:** Python-based code generation

**Rationale:**
- Reuse existing APB crossbar automation (~95%)
- Parameterization without manual edits
- Consistent code quality
- Educational value (code generation techniques)
- Rapid design space exploration

---

## 7. Comparison to APB Crossbar

### 7.1 Similarities (~95% Code Reuse)

| Component | APB Crossbar | Delta (AXIS) | Reusable? |
|-----------|--------------|--------------|-----------|
| Request generation | Address decode | TDEST decode | [PASS] Pattern same |
| Per-slave arbitration | Round-robin | Round-robin | [PASS] Identical logic |
| Grant matrix | MxN grants | MxN grants | [PASS] Identical |
| Data multiplexing | Mux PRDATA | Mux TDATA/TVALID/TLAST | [PASS] Same pattern |
| Backpressure | PREADY | TREADY | [PASS] Renamed only |

### 7.2 Differences

| Aspect | APB Crossbar | Delta (AXIS) |
|--------|--------------|--------------|
| **Address decode** | Range check (base/end) | Direct TDEST (simpler!) |
| **Packet concept** | Single transaction | Multi-beat packets with TLAST |
| **Arbitration** | Re-arbitrate every cycle | Lock until TLAST (packet atomicity) |
| **Signals** | PRDATA, PSLVERR | TDATA, TVALID, TLAST, TDEST, TID, TUSER |
| **Read/Write** | Separate paths | Unified data path (simpler!) |

### 7.3 Migration Effort

**Estimated Time:** ~75 minutes (from existing APB generator to AXIS)

**Tasks:**
1. Rename signals (10 min)
2. Simplify address decode to TDEST (5 min)
3. Add packet atomicity logic (15 min)
4. Add new signals (TLAST, TID, TUSER) to ports and mux (10 min)
5. Update module naming (5 min)
6. Test with 2x2 configuration (30 min)

---

## 8. Use Cases

### 8.1 Primary: RISC Cores + DSP Array

**Scenario:** 4 small RISC-V cores need to route compute tasks to 16 DSP accelerators

**Configuration:**
- 4 masters (RISC cores)
- 16 slaves (DSP arrays)
- 64-bit data width
- Flat topology (low latency critical)

**Benefits:**
- Each RISC core can target any DSP (full flexibility)
- Round-robin ensures fair DSP access
- Low 2-cycle latency for task dispatch

### 8.2 Secondary: Educational Demonstration

**Scenario:** Teach students about interconnect design trade-offs

**Configuration:**
- Generate both flat and tree topologies
- Compare latency, throughput, resources
- Show code generation techniques
- Demonstrate verification methodology

**Benefits:**
- Hands-on learning with working RTL
- Clear performance comparisons
- Demonstrates real-world design process

### 8.3 Future: Integration with RAPIDS

**Scenario:** Use Delta for compute fabric routing, RAPIDS for memory DMA

**Configuration:**
- RAPIDS handles descriptor-based memory transfers
- Delta routes compute tasks between processors
- Protocol adapter (Network 2.0 <-> AXI-Stream)

**Benefits:**
- Separate concerns (memory vs compute)
- Reusable components
- Scalable architecture

---

## 9. Verification Strategy

### 9.1 Generator Verification

**Approach:**
1. Unit tests for each generator function (Python unittest)
2. Lint generated RTL (Verilator)
3. Synthesis test (Vivado/Yosys)
4. Compare output for different parameters

**Success Criteria:**
- All Python tests pass
- Generated RTL lints clean
- Synthesis completes without errors

### 9.2 RTL Verification

**Approach:**
1. CocoTB testbench framework (reuse AMBA patterns)
2. Test all MxS routing combinations
3. Concurrent traffic scenarios
4. Backpressure stress tests
5. Packet atomicity verification

**Success Criteria:**
- 100% routing coverage
- No deadlocks under stress
- Packet atomicity confirmed
- Performance matches model (±10%)

### 9.3 Model Validation

**Approach:**
1. Analytical model vs simulation model comparison
2. Simulation model vs RTL CocoTB results
3. Synthesis reports vs resource estimates

**Success Criteria:**
- Latency within ±1 cycle
- Throughput within ±15%
- Resources within ±20%

---

## 10. Documentation Requirements

### 10.1 Specifications

**PRD** (this document)
- Requirements, architecture, use cases

**Technical Specification**
- Detailed block diagrams
- Interface timing diagrams
- Performance analysis

**User Guide**
- Generator usage examples
- Integration patterns
- Best practices

### 10.2 Code Documentation

**Generator Code:**
- Docstrings for all functions
- Inline comments for complex logic
- Usage examples in header

**Generated RTL:**
- Module header with configuration
- Block-level comments
- Signal descriptions

**Performance Models:**
- Algorithm explanations
- Formula derivations
- Validation methodology

---

## 11. Success Metrics

### 11.1 Functional Metrics

- [PASS] Generator produces lint-clean RTL
- [PASS] All routing combinations verified
- [PASS] No protocol violations
- [PASS] Packet atomicity enforced

### 11.2 Performance Metrics

- [PASS] Flat crossbar: 2-cycle latency
- [PASS] Tree topology: <=6-cycle latency
- [PASS] Throughput: >=0.7 transfers/cycle
- [PASS] Fmax: >=300 MHz

### 11.3 Quality Metrics

- [PASS] Code reuse: >=90% from APB generator
- [PASS] Model accuracy: ±10% vs RTL
- [PASS] Resource estimate: ±20% vs synthesis
- [PASS] Documentation: Complete and clear

---

## 12. Timeline and Milestones

### Week 1: Generator and Models
- [PASS] Python generator (flat topology)
- [PASS] Analytical performance model
- [PASS] Simulation model (SimPy)
- [PASS] Specifications

### Week 2: RTL and Verification
- Generate RTL variants (flat 4x16, tree 4x16)
- CocoTB testbench framework
- Basic functional tests
- Performance validation

### Week 3: Integration and Documentation
- RISC + DSP integration example
- Complete user guide
- Performance comparison report
- Educational materials

---

## 13. Open Questions

**Q1:** Should we add configurable FIFO insertion for burst buffering?
- **Status:** Deferred to v1.1 (keep v1.0 simple)

**Q2:** Support for weighted round-robin arbitration?
- **Status:** Deferred (default round-robin sufficient for now)

**Q3:** Integration with existing APB crossbar generator (unified tool)?
- **Status:** Under consideration (separate for now, may merge later)

---

## 14. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-10-18 | RTL Design Sherpa | Initial release |

---

## 15. Attribution and Contribution Guidelines

### 15.1 Git Commit Attribution

When creating git commits for Delta documentation or implementation:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** Delta documentation and organization receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

---

## 16. Documentation Generation

### 16.1 Generating PDF/DOCX from Specification

**Tool:** `/mnt/data/github/rtldesignsherpa/bin/md_to_docx.py`

Use this tool to convert the linked specification index into a single all-inclusive PDF or DOCX file.

**Basic Usage:**

```bash
# Generate DOCX from delta_spec index
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
    -o projects/components/delta/docs/Delta_Specification_v0.25.docx \
    --toc \
    --title-page

# Generate both DOCX and PDF
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
    -o projects/components/delta/docs/Delta_Specification_v0.25.docx \
    --toc \
    --title-page \
    --pdf

# With custom template (optional)
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
    -o projects/components/delta/docs/Delta_Specification_v0.25.docx \
    -t path/to/template.dotx \
    --toc \
    --title-page \
    --pdf
```

**Key Features:**
- **Recursive Collection:** Follows all markdown links in the index file
- **Heading Demotion:** Automatically adjusts heading levels for included files
- **Table of Contents:** `--toc` flag generates automatic ToC
- **Title Page:** `--title-page` flag creates title page from first heading
- **PDF Export:** `--pdf` flag generates both DOCX and PDF
- **Image Support:** Resolves images relative to source directory
- **Template Support:** Optional custom DOCX/DOTX template via `-t` flag

**Common Workflow:**

```bash
# 1. Update version number in index file (delta_index.md)
# 2. Generate documentation
cd /mnt/data/github/rtldesignsherpa
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
    -o projects/components/delta/docs/Delta_Specification_v0.25.docx \
    --toc --title-page --pdf

# 3. Output files created:
#    - Delta_Specification_v0.25.docx
#    - Delta_Specification_v0.25.pdf (if --pdf used)
```

**Debug Mode:**

```bash
# Generate debug markdown to see combined output
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
    -o output.docx \
    --debug-md

# This creates debug.md showing the complete merged content
```

**Tool Requirements:**
- Python 3.6+
- Pandoc installed and in PATH
- For PDF generation: LaTeX (e.g., texlive) or use Pandoc's built-in PDF writer

**📖 See:** `/mnt/data/github/rtldesignsherpa/bin/md_to_docx.py` for complete implementation details

---

## 16.2 PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
/mnt/data/github/rtldesignsherpa/projects/components/delta/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/delta/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the delta_spec index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## Appendix A: Glossary

- **AXIS:** AXI-Stream (streaming variant of AXI protocol)
- **Delta:** Project name (river delta = branching flow, like crossbar routing)
- **Flat Topology:** Full MxN crossbar with all connections
- **Tree Topology:** Hierarchical composition of 1:2 and 2:1 nodes
- **Packet Atomicity:** Locking grant until TLAST (prevent interleaving)
- **TDEST:** Transaction destination (slave ID in AXI-Stream)
- **TID:** Transaction ID (master identifier in AXI-Stream)

---

**END OF PRD**
