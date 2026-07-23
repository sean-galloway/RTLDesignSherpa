# Review: axi4_part_01 (11 docs, RTL for 8 modules + 4 dependencies)

I verified every parameter table, port list, code example, and numeric claim against the supplied RTL. The core master/stub pages are largely accurate; the defects are concentrated in the clock-gating collateral and the read data-width converter page.

---

## Findings

```
[CONFIRMED] axi4_dwidth_converter_rd documented with parameter names/defaults that do not exist
  File:     docs/markdown/RTLAmba/axi4/axi4_dwidth_converter_rd.md
  Says:     "| `AR_FIFO_DEPTH` | int | 4 | Read address FIFO depth (power of 2) |" and
            "| `R_FIFO_DEPTH` | int | 8 | Read data FIFO depth (power of 2) |"; both usage
            examples instantiate `.AR_FIFO_DEPTH(4), .R_FIFO_DEPTH(16)` / `.R_FIFO_DEPTH(32)`
  Actually: RTL declares `parameter int SKID_DEPTH_AR = 2` and `parameter int SKID_DEPTH_R = 4`,
            feeding `gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_AR)...)`. No AR_FIFO_DEPTH /
            R_FIFO_DEPTH parameters exist. gaxi_skid_buffer's header restricts DEPTH to
            {2,4,6,8}, so the documented depths of 16 and 32 and the "power of 2" constraint
            are also wrong, and the "Buffer Depth Guidelines" (R_FIFO_DEPTH ≥ WIDTH_RATIO ×
            max_burst_length, e.g. 16–32 entries) cannot be satisfied at all.
  Impact:   Both copy-paste examples fail elaboration (unknown parameter); the buffering
            guidance is unusable. The page also calls the buffers FIFOs throughout and lists
            gaxi_fifo_sync under "Used Components"; the RTL uses only gaxi_skid_buffer plus
            the axi_data_upsize/dnsize primitives (which the page never mentions).
```

```
[CONFIRMED] axi4_dwidth_converter_rd documents status ports that do not exist
  File:     docs/markdown/RTLAmba/axi4/axi4_dwidth_converter_rd.md
  Says:     "| `busy` | Output | 1 | Indicates active read conversions in progress |" and
            "| `rd_transactions_pending` | Output | 16 | Number of pending read transactions |";
            Key Features: "Status Outputs: Busy signal and pending transaction counter";
            examples connect `.busy(rd_busy), .rd_transactions_pending(rd_pend)`
  Actually: The RTL port list ends at `m_axi_rvalid`/`m_axi_rready`; there is no busy and no
            rd_transactions_pending port anywhere in the module.
  Impact:   Examples do not compile; the module has no status outputs at all.
```

```
[CONFIRMED] axi4_master_rd_cg.md documents a completely different clock-gating interface than the RTL
  File:     docs/markdown/RTLAmba/axi4/axi4_master_rd_cg.md
  Says:     Parameters "ENABLE_CLOCK_GATING | 1", "CG_IDLE_CYCLES | 8", "CG_GATE_* | 1";
            example `.ENABLE_CLOCK_GATING(1), .CG_IDLE_CYCLES(8)`;
            "Zero Overhead When Disabled: ENABLE_CLOCK_GATING=0 → identical to base";
            "// ... all other ports same as axi4_master_rd"
  Actually: RTL axi4_master_rd_cg adds exactly one parameter, `CG_IDLE_COUNT_WIDTH = 4`, and
            four ports: `cfg_cg_enable`, `cfg_cg_idle_count`, `cg_gating`, `cg_idle`. None of
            ENABLE_CLOCK_GATING / CG_IDLE_CYCLES / CG_GATE_* exist. Ports are also not "the
            same as axi4_master_rd": the base module's `busy` output is consumed internally
            (int_busy) and is not exposed. The page contradicts this book's own
            axi4_clock_gating_guide.md, which documents the real interface correctly.
  Impact:   The Quick Usage example fails elaboration; the two required configuration inputs
            (cfg_cg_enable, cfg_cg_idle_count) are never mentioned, so a reader cannot hook
            the module up from this page. (The page also claims "Power Savings: 25-70%", which
            contradicts the guide's own unsourced table topping out at 40-45%.)
```

```
[CONFIRMED] axi4_master_wr_cg.md has the same wrong interface as the read variant
  File:     docs/markdown/RTLAmba/axi4/axi4_master_wr_cg.md
  Says:     Parameters "ENABLE_CLOCK_GATING | 1", "CG_IDLE_CYCLES | 8", "CG_GATE_* | 1";
            example `.ENABLE_CLOCK_GATING(1), .CG_IDLE_CYCLES(8)`;
            "// ... all other ports same as axi4_master_wr"
  Actually: RTL axi4_master_wr_cg has only the added parameter CG_IDLE_COUNT_WIDTH and ports
            cfg_cg_enable / cfg_cg_idle_count / cg_gating / cg_idle; `busy` is not exposed.
  Impact:   Same as above — example does not compile, real configuration interface undocumented.
```

```
[CONFIRMED] "Clock Gating Integration" example in axi4_master_rd.md uses nonexistent ports
  File:     docs/markdown/RTLAmba/axi4/axi4_master_rd.md
  Says:     "axi4_master_rd_cg #( ... ) u_rd_master_cg (
               ...
               .cg_enable       (rd_enable),
               .cg_test_enable  (scan_mode),
               .busy            (rd_busy));"
  Actually: axi4_master_rd_cg has no cg_enable, cg_test_enable, or busy ports (actual:
            cfg_cg_enable, cfg_cg_idle_count, cg_gating, cg_idle). There is also no test-mode
            port anywhere in the _cg RTL — bypass is cfg_cg_enable=0.
  Impact:   Example does not compile and invents a scan-bypass port.
```

```
[CONFIRMED] "Clock Gating Example" in axi4_master_wr.md instantiates clock_gate_ctrl with wrong port names
  File:     docs/markdown/RTLAmba/axi4/axi4_master_wr.md
  Says:     "clock_gate_ctrl u_cg (
               .i_clk          (axi_clk),
               .i_enable       (wr_master_busy),
               .o_clk_gated    (axi_clk_gated));"
  Actually: rtl/common/clock_gate_ctrl.sv ports are `clk_in`, `aresetn`, `cfg_cg_enable`,
            `cfg_cg_idle_count`, `wakeup`, `clk_out`, `gating`. No i_clk/i_enable/o_clk_gated
            exist (and the example omits aresetn and the idle-count input entirely).
  Impact:   Example does not compile; a reader copying it cannot drive the real controller.
```

```
[CONFIRMED] fub_axi_ar_count documented as buffer-occupancy output but is never driven in RTL
  File:     docs/markdown/RTLAmba/axi4/axi4_master_rd_stub.md (also axi4_master_stub.md)
  Says:     "| fub_axi_ar_count | 3 | Output | AR buffer occupancy |"
  Actually: In rtl/amba/axi4/stubs/axi4_master_rd_stub.sv the AR skid buffer is instantiated
            with both `.count()` and `.rd_count()` left unconnected (PINCONNECTEMPTY), so the
            output port fub_axi_ar_count is driven by nothing. The sibling
            axi4_master_wr_stub drives its count correctly (`.rd_count(fub_axi_aw_count)`).
            axi4_master_stub forwards the same undriven signal. See POSSIBLE RTL BUGS.
  Impact:   A testbench reading fub_axi_ar_count gets X/garbage, not occupancy.
```

```
[CONFIRMED] Converter reference paths contradict the pages' own Location headers
  File:     docs/markdown/RTLAmba/axi4/axi4_dwidth_converter_rd.md,
            docs/markdown/RTLAmba/axi4/axi4_dwidth_converter_wr.md
  Says:     References: "RTL: `rtl/amba/axi4/axi4_dwidth_converter_rd.sv`" (and `_wr.sv`)
  Actually: Both pages state "**Location:** `projects/components/converters/rtl/`" at the top,
            the RTL banners confirm that path, and the README says explicitly "The converters
            live in `projects/components/converters/rtl/`, not `rtl/amba/axi4/`."
  Impact:   Readers are sent to a path that does not contain the files.
```

```
[CONFIRMED] Clock-gating guide: "All other ports are identical to the base module" is false
  File:     docs/markdown/RTLAmba/axi4/axi4_clock_gating_guide.md
  Says:     "**All other ports are identical to the base module.**" (stated twice)
  Actually: The base modules expose `busy`; both _cg wrappers consume it internally as
            int_busy and do not re-export it (port lists end at cg_gating/cg_idle).
  Impact:   Minor — a reader wiring `.busy(...)` on a _cg instance gets an elaboration error.
```

```
[CONFIRMED] Clock-gating guide: cfg_cg_idle_count change does not trigger ungating
  File:     docs/markdown/RTLAmba/axi4/axi4_clock_gating_guide.md
  Says:     "Ungating Conditions (Any Triggers Ungating): ... 2. Configuration change
            (`cfg_cg_enable` or `cfg_cg_idle_count`)"
  Actually: In clock_gate_ctrl the counter reloads only on `wakeup || !cfg_cg_enable`;
            w_gate_enable requires `r_idle_counter == 'h0`. Changing cfg_cg_idle_count while
            gated leaves the counter at 0 and the clock stays gated. Only cfg_cg_enable→0
            ungates among config changes.
  Impact:   Minor — a user adjusting the idle threshold at runtime may expect a wake that
            never comes.
```

```
[CONFIRMED] Latency/resource comparisons against the "full converter" have no basis — that module does not exist
  File:     docs/markdown/RTLAmba/axi4/axi4_dwidth_converter_rd.md,
            docs/markdown/RTLAmba/axi4/axi4_dwidth_converter_wr.md
  Says:     "**Comparison to Full Converter:** ~20-30% lower latency (no write path overhead),
            ~40% resource savings (no write channel FIFOs)" (wr page mirrors with "read")
  Actually: axi4_dwidth_converter.md states "Status: Planned - no RTL in this repository" and
            "There is no axi4_dwidth_converter.sv in the repository." There is no full
            converter to measure against.
  Impact:   Fabricated comparison numbers presented as measured fact.
```

```
[CONFIRMED] Planned-converter page references files its own disclaimer says do not exist
  File:     docs/markdown/RTLAmba/axi4/axi4_dwidth_converter.md
  Says:     References: "RTL: `rtl/amba/axi4/axi4_dwidth_converter.sv`",
            "Tests: `val/amba/test_axi4_dwidth_converter.py`" — while the header says
            "**Location:** Not implemented" and the status note says there is no RTL.
  Impact:   Minor internal contradiction; readers may search for nonexistent files.
```

```
[SUSPECTED] Multi-master example instantiates an interconnect module not present in the repo
  File:     docs/markdown/RTLAmba/axi4/axi4_master_rd.md
  Says:     "axi4_interconnect #(.NUM_MASTERS(2), .NUM_SLAVES(1)) u_interconnect (...)" with
            ports declared as `axi4_if.slave` / `axi4_if.master`; "Related Modules" lists
            axi4_interconnect.
  Actually: No axi4_interconnect module and no axi4_if interface appear in the supplied RTL,
            and the README's own module tables list no interconnect component (only masters,
            slaves, monitors, converters, and _cg variants). Marked SUSPECTED because part 2
            of this book was not supplied; if no interconnect ships, this example and the
            README's "interconnect components" claim are unsupported.
  Impact:   Example likely targets a module that does not exist.
```

```
[SUSPECTED] Read-converter data-width range "8-1024" unsupported
  File:     docs/markdown/RTLAmba/axi4/axi4_dwidth_converter_rd.md
  Says:     "| `S_AXI_DATA_WIDTH` | int | 32 | 8-1024 | ..." (same for M)
  Actually: The RTL header comment says "(32, 64, 128, 256)", the sibling wr page documents
            32-256, and the only elaboration checks are power-of-2 and WIDTH_RATIO ≥ 2.
            Whether 8-bit or 1024-bit widths work through the axi_data_upsize/dnsize
            primitives (not supplied) cannot be verified.
  Impact:   Low; range likely overstated relative to what was ever tested.
```

```
[CONFIRMED] Gap: upsize read converter caps outstanding read bursts at 16 — undocumented
  File:     docs/markdown/RTLAmba/axi4/axi4_dwidth_converter_rd.md
  Says:     Nothing about outstanding-transaction limits.
  Actually: In upsize mode the RTL pushes each accepted AR's narrow length into a 16-deep
            FIFO (BLEN_FIFO_DEPTH = 16) and gates issuance:
            `m_axi_arvalid = int_ar_valid && w_blen_wr_ready`. A 17th outstanding read burst
            stalls at AR until an earlier burst's R data fully drains.
  Impact:   Users issuing >16 outstanding reads hit an undocumented AR stall; relevant to
            anyone sizing ID widths / outstanding counts (the README suggests up to 256 IDs).
```

---

## What I checked that is correct

- **Clock-gating guide cycle math.** Recomputed against `amba_clock_gate_ctrl` + `clock_gate_ctrl`: last activity cycle N → `r_wakeup` high through N+1 → counter (loaded with C) first decrements during N+2 → reaches 0 during N+C+2, when `w_gate_enable` asserts. So gating at C+2 cycles after last bus activity, and C+1 after last wakeup — exactly as the guide states. Wake path: activity at N → `r_wakeup` at N+1 → combinational ICG enable → first gated edge at N+2: matches "1 register stage … first usable gated-clock edge arrives 2 cycles after activity". The forced-ready behavior (`fub_axi_arready = cg_gating ? 1'b0 : int_arready`) is also as documented.
- **Converter burst/address rewrites.** RTL matches the documented formulas: upsize `ARLEN = (arlen + R)/R − 1` (ceiling divide) and `ARSIZE = $clog2(M_STRB_WIDTH)` in both directions; downsize `ARLEN = (arlen+1)*R − 1`; read path aligns `m_axi_araddr` down to the wide boundary while the write path passes AWADDR through unmodified — both as the pages' (accurate, recently corrected) notes say.
- **Master/stub interface tables.** `axi4_master_rd`, `axi4_master_wr`, and both stub pages: parameter names/defaults, port names/widths, packet concatenation orders (ARSize/RSize/AWSize/WSize/BSize), the busy equations (quoted verbatim in the docs, identical in RTL), and the AR/R packet bit-slice examples all check out. SKID_DEPTH guidance of {2,4,6,8} matches the gaxi_skid_buffer header.
- `CG_IDLE_COUNT_WIDTH` default of 4, and the _cg port set, as documented in the guide.

---

## POSSIBLE RTL BUGS

1. **CONFIRMED — `axi4_master_rd_stub`: undriven output port.** `fub_axi_ar_count` is declared (`output logic [2:0]`) but the AR skid buffer's `.count()` and `.rd_count()` are both left unconnected under `PINCONNECTEMPTY` pragmas. The sibling `axi4_master_wr_stub` connects `.rd_count(fub_axi_aw_count)`, so this looks like an accidental omission. Propagates to `axi4_master_stub.fub_axi_ar_count`.

2. **SUSPECTED — `clock_gate_ctrl`: undeclared identifier in ANSI port list.** The port `input logic [N-1:0] cfg_cg_idle_count` uses `N`, but `N` is a `localparam` declared in the module *body* (`localparam int N = IDLE_CNTR_WIDTH;`), which is not visible in the parameter/port declaration scope per IEEE 1800; strict tools should reject this. (The sibling `amba_clock_gate_ctrl` does it correctly with `ICW` in the parameter list.) Flagged SUSPECTED because I cannot compile here and some tools accept it as an extension.

3. **SUSPECTED — `axi4_dwidth_converter_rd`: "latest rid" carry can alias across outstanding bursts.** `r_rid_held`/`r_ruser_held` update on every master-side R handshake and are presented on whatever slave-side beat is currently draining. With multiple outstanding bursts and out-of-order completion (legal across IDs in AXI4), a later burst's rid/ruser could appear on an earlier burst's tail beats — unless `axi_data_dnsize` backpressures new wide beats while draining (that primitive was not supplied, so I cannot confirm reachability). The same pattern exists for `r_wuser_held` in the write converter if WUSER ever changes per beat.

---

## Overall assessment

The four core module pages (`axi4_master_rd`, `axi4_master_wr`, the stubs) and the clock-gating guide are accurate and, in places, commendably precise — the guide's idle/wake cycle counts and the converters' burst-rewrite formulas all reproduce exactly from the RTL. The book's weak spots are three: (1) everything about clock gating *outside* the guide — the two `*_cg.md` pages describe an interface (`ENABLE_CLOCK_GATING`, `CG_IDLE_CYCLES`, `CG_GATE_*`, `cg_test_enable`) that simply does not exist in the RTL, and the two clock-gating snippets embedded in the master pages would not compile; (2) the read data-width converter page, which appears written against an older FIFO-based design — wrong parameter names and defaults, two phantom status ports, FIFO terminology throughout, and fabricated comparisons against a sibling module that has no RTL; (3) stale `rtl/amba/axi4/` reference paths for the converters that contradict the pages' own Location headers. The `axi4_master_rd_stub` occupancy-count discrepancy is both a doc error and a genuine RTL bug worth fixing before release.