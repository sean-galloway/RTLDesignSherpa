<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Claude Code Guide: Miscellaneous Components

**Version:** 1.0
**Last Updated:** 2025-11-11
**Purpose:** AI-specific guidance for working with miscellaneous utility components

---

## Quick Context

**What:** Collection of reusable utility components and adapters
**Status:** Active - Currently planning AXI ROM wrapper
**Your Role:** Help users develop utility components following repository standards

**Complete Documentation:** `projects/components/misc/README.md` ← Component overview

---

## Global Requirements Reference

**IMPORTANT: Check `/GLOBAL_REQUIREMENTS.md` for all mandatory requirements**

This file contains misc-specific guidance. For complete requirements:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Consolidated mandatory requirements
- **See:** `projects/components/CLAUDE.md` - Component area standards
- **See:** Root `/CLAUDE.md` - Repository-wide guidance

---

## Critical Rules for This Component Area

### Rule #0: Reset Macro Standards (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Section 1.1 -- all RTL here uses
`ALWAYS_FF_RST` / `RST_ASSERTED` from `reset_defs.svh`, no exceptions.
Rationale: `vault/handbook/design/reset-and-clocking.md`.

---

### Rule #1: FPGA Synthesis Attributes (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Section 1.2

ROM and RAM wrappers are this area's primary use case, so the attribute choice
matters more here than elsewhere -- a large ROM without a hint synthesises into
logic.

```systemverilog
`ifdef XILINX
    (* ram_style = "block" *)          // block RAM for large ROMs
`elsif INTEL
    /* synthesis ramstyle = "M20K" */
`endif
logic [DATA_WIDTH-1:0] rom_data [DEPTH];
```

See `vault/handbook/design/sram-and-memories.md`.

---

### Rule #2: Testbench Location (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1 -- a TB class never lives in a
test runner. The layout here is flat, with no per-component subdirectory:

```
projects/components/misc/dv/
├── tbclasses/{name}_tb.py      # TB classes, flat
└── tests/fub/test_{name}.py    # runners
```

```python
from projects.components.misc.dv.tbclasses.dma_address_gen_tb import DmaAddressGenTB
from TBClasses.shared.tbbase import TBBase
```

---

### Rule #2b: AXI/AXIL Protocol Modules ARE the Interface (MANDATORY)

**Every AXI4 / AXI-Lite agent under `projects/components/misc/` MUST use
the standard protocol modules from `rtl/amba/` -- do not hand-roll the
AR/R/AW/W/B handshake, skid buffers, or transaction tracking.**

| Agent role | Required wrapper | Adds for free |
|---|---|---|
| AXI4 slave, read-only  | `axi4_slave_rd_mon`  | filtered monitor |
| AXI4 slave, write-only | `axi4_slave_wr_mon`  | filtered monitor |
| AXIL slave, read-only  | `axil4_slave_rd_mon` | filtered monitor |
| AXIL slave, write-only | `axil4_slave_wr_mon` | filtered monitor |
| AXI4 master, rd / wr   | `axi4_master_rd_mon` / `axi4_master_wr_mon` | filtered monitor |

User logic (BRAM, LFSR, CRC accumulator, etc.) lives on the wrapper's
`fub_axi_*` user-side queue and never touches the AXI handshake directly.

The two synthetic test slaves used by `stream_char_harness`
(`axi4_slave_rd_pattern_gen.sv` and `axi4_slave_wr_crc_check.sv`)
have been promoted into `rtl/amba/shared/` so they're reusable across
projects. Their AXI4 handshake is hand-rolled around the standard
`axi4_slave_rd` / `axi4_slave_wr` skids and doesn't go through the
monitor wrappers — that's intentional: they are characterization
peers, not production agents. The observation gap on the
descriptor-fetch path is covered by the existing `o_dbg_vr`
handshake counters in `desc_ram`, not by additional monitors.

---

### Rule #3: Three Mandatory TB Methods

**See:** `/GLOBAL_REQUIREMENTS.md` Section 2.2 -- every TB class implements
`setup_clocks_and_reset()`, `assert_reset()` and `deassert_reset()`. Working
examples are in `dv/tbclasses/`.

---

## Component Development Workflow

> Note (2026-07-22): the `axi_rom_wrapper` / `axi_rom_tb.py` / `test_axi_rom.py` /
> `docs/axi_rom_spec.md` files used throughout this walkthrough are a TEMPLATE example,
> not existing files. The ROM actually implemented in misc/ is `rtl/axi4_slave_rom.sv`
> (+ `rtl/rom.sv`); it does not yet have a dedicated test. Real misc tests live in
> `dv/tests/fub/` with TB classes in `dv/tbclasses/`.

### Step 1: Validate Component Suitability

**Before adding to misc/, verify:**

**Belongs in misc/ if:**
- Solves common integration problem
- Reusable across multiple projects
- Doesn't fit existing categories
- Uses standard interfaces
- Production quality (tested, documented)

**Does NOT belong in misc/ if:**
- Project-specific glue logic
- Experimental or prototype code
- Duplicates existing functionality
- Lacks standard interface

**Examples:**

| Component | Belongs in misc/? | Reason |
|-----------|-------------------|--------|
| AXI ROM wrapper | Yes | Common, reusable, standard interface |
| AXI RAM wrapper | Yes | Common, reusable, standard interface |
| Project X custom mux | No | Project-specific, no standard interface |
| Debug probe | No | Better in separate debug infrastructure |

---

### Step 2: Build It

The walkthrough that used to fill this section -- `axi_rom_wrapper.sv`,
`axi_rom_tb.py`, `test_axi_rom.py`, `docs/axi_rom_spec.md` -- documented four
files that do not exist, and carried a disclaimer saying so. Its RTL template
also hand-rolled the AXI4 AR/R handshake, which is exactly what Rule #2b above
forbids. Build against what is actually here.

**What this area holds** (`rtl/`):

| Module | What it is |
|---|---|
| `axi4_slave_rom.sv`, `rom.sv` | the ROM, behind a standard AXI4 slave wrapper |
| `axi4_intf_master_observer.sv`, `axi4_intf_slave_observer.sv` | bus observers |
| `dma_address_gen.sv`, `stream_run_addr_gen.sv` | address generators |
| `monbus_legal_cam.sv`, `monbus_pkt_tally.sv`, `monbus_tally_axil.sv` | monbus collateral |

Tests are `dv/tests/fub/test_*.py` over TB classes in `dv/tbclasses/` -- four of
each today, and `axi4_slave_rom.sv` is not among them.

**Shapes to follow:** Rule #2b for any AXI/AXIL agent; the `test-patterns` skill
and `/GLOBAL_REQUIREMENTS.md` 2.2 / 3.2 for the test; a filelist in the same
commit as the module (`vault/handbook/design/filelists.md`); a spec page under
`docs/` following `vault/handbook/authoring/module-doc-template.md`.

---

## Quick Commands

```bash
# Lint
cd projects/components/misc
verilator --lint-only rtl/{name}.sv

# Tests through the Makefile, never bare pytest -- it supplies the level, the
# derived worker count and the reruns, and cleans first.
cd dv/tests && make clean-all && make run-{name}-gate
cd dv/tests && make run-{name}-gate-waves

# create_view_cmd() writes a ready-made gtkwave command beside the log --
# do not hand-build the path.
```

Grammar and rationale: `vault/handbook/dv/running-regressions.md`.

---

**Version:** 1.0
**Last Updated:** 2025-11-11
**Maintained By:** RTL Design Sherpa Project
