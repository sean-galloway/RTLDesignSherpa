# Review: axi4_part_02 (AXI4 slave/stub pages, 8 files)

I checked every parameter table, port table, packet layout, bit-slice example, and code snippet in these 8 pages against the 8 modules plus `gaxi_skid_buffer`, `amba_clock_gate_ctrl`, and `clock_gate_ctrl` in `RTL.sv`. The base-module pages (`axi4_slave_rd`, `axi4_slave_wr`) and all four stub pages are largely accurate — packet concatenation orders, widths, directions, the `busy` equations, and the example bit-slices all match the RTL exactly. The two `_cg` pages are a different story: they describe a parameter-based clock-gating wrapper that does not exist in this RTL.

---

## Findings

```
[CONFIRMED] axi4_slave_rd_cg.md documents three parameter groups that do not exist in the RTL
  File:     docs/markdown/RTLAmba/axi4/axi4_slave_rd_cg.md
  Says:     "| `ENABLE_CLOCK_GATING` | 1 | Master enable (0=disable, identical to base) |
             | `CG_IDLE_CYCLES` | 8 | Cycles before clock gating activates |
             | `CG_GATE_*` | 1 | Domain-specific gating enables |"
  Actually: axi4_slave_rd_cg's only clock-gating parameter is
            `parameter int CG_IDLE_COUNT_WIDTH = 4`. There is no ENABLE_CLOCK_GATING,
            no CG_IDLE_CYCLES, and no CG_GATE_* anywhere in the module. Gating is
            controlled at runtime via input ports `cfg_cg_enable` and
            `cfg_cg_idle_count[CG_IDLE_COUNT_WIDTH-1:0]` (max idle 15 at the default
            width), and there is a single gating domain — one amba_clock_gate_ctrl
            gates the entire module, so "domain-specific gating enables" has nothing
            to attach to.
  Impact:   A reader sets parameters that don't exist (elaboration error) and never
            learns about the two configuration ports or CG_IDLE_COUNT_WIDTH, which
            are the actual control interface.
```

```
[CONFIRMED] axi4_slave_rd_cg.md Quick Usage example would not compile, and the port claim is wrong
  File:     docs/markdown/RTLAmba/axi4/axi4_slave_rd_cg.md
  Says:     "axi4_slave_rd_cg #( ... .ENABLE_CLOCK_GATING(1), .CG_IDLE_CYCLES(8) ) u_cg (
             .aclk(clk), .aresetn(rst_n), // ... all other ports same as axi4_slave_rd );"
  Actually: ENABLE_CLOCK_GATING and CG_IDLE_CYCLES are not parameters, so this fails
            at elaboration. The port list also differs from the base module in five
            places: the CG wrapper adds cfg_cg_enable, cfg_cg_idle_count, cg_gating,
            cg_idle, and it does NOT have the base module's `busy` output (busy is
            internal, wired to int_busy). "All other ports same as axi4_slave_rd" is
            therefore wrong — a reader connecting .busy(...) gets an elaboration
            error, and leaving cfg_cg_enable/cfg_cg_idle_count unconnected leaves
            the gating inputs floating.
  Impact:   Copy-paste integration fails; the module's actual status outputs
            (cg_gating, cg_idle) are never mentioned anywhere on the page.
```

```
[CONFIRMED] axi4_slave_wr_cg.md — identical defects to the two findings above
  File:     docs/markdown/RTLAmba/axi4/axi4_slave_wr_cg.md
  Says:     "| `ENABLE_CLOCK_GATING` | 1 | ... | `CG_IDLE_CYCLES` | 8 | ... | `CG_GATE_*` | 1 | ..."
            and the same Quick Usage pattern with ".ENABLE_CLOCK_GATING(1), .CG_IDLE_CYCLES(8)"
            and "all other ports same as axi4_slave_wr"
  Actually: axi4_slave_wr_cg has only `parameter int CG_IDLE_COUNT_WIDTH = 4` for
            clock gating; control is via ports cfg_cg_enable / cfg_cg_idle_count;
            status via cg_gating / cg_idle; no `busy` port; single gating domain.
            Verified line-by-line against the module header in
            rtl/amba/axi4/axi4_slave_wr_cg.sv.
  Impact:   Same as above. Both _cg pages appear to have been written against a
            different, parameter-configured CG wrapper family (possibly the monitor
            _cg modules they cross-reference) and do not describe this RTL at all.
```

```
[CONFIRMED] "Clock Gating Example" in axi4_slave_rd.md and axi4_slave_wr.md uses port names that
            do not exist on clock_gate_ctrl — example would not compile
  File:     docs/markdown/RTLAmba/axi4/axi4_slave_rd.md (and identically axi4_slave_wr.md)
  Says:     "clock_gate_ctrl u_cg (
                 .i_clk          (axi_clk),
                 .i_enable       (rd_slave_busy),
                 .o_clk_gated    (axi_clk_gated)
             );"
  Actually: clock_gate_ctrl (rtl/common/clock_gate_ctrl.sv) has ports clk_in, aresetn,
            cfg_cg_enable, cfg_cg_idle_count, wakeup, clk_out, gating. There is no
            i_clk, i_enable, or o_clk_gated. The example also leaves the required
            aresetn input unconnected. Both files repeat the same example
            (wr version uses wr_slave_busy).
  Impact:   A reader following the example hits "port not found" errors on all three
            connections. The page presents this as the way to use the busy signal,
            so the one piece of guidance on that feature is unusable as written.
```

```
[CONFIRMED] "Values greater than 8 overflow the occupancy counter" — wrong mechanism and wrong limit
  File:     docs/markdown/RTLAmba/axi4/axi4_slave_rd.md and axi4_slave_wr.md
            ("Buffer Depth Selection", identical text in both)
  Says:     "The underlying gaxi_skid_buffer ... tracks occupancy with a 4-bit counter,
             so legal values are 2, 4, 6, and 8. Values greater than 8 overflow the
             occupancy counter and are not supported."
  Actually: The 4-bit counter (r_data_count, rd_count in gaxi_skid_buffer.sv) holds
            0–15; the count never exceeds DEPTH, so overflow would begin at DEPTH=16,
            not 9. Mechanically, DEPTH=10 or 12 (or odd values) work fine — the
            write-slot compare `r_data_count == gi[3:0]` and the registered
            wr_ready/rd_valid equations are depth-generic through 15. The {2,4,6,8}
            set is the module author's stated design expectation ("DEPTH ... Must be
            one of {2, 4, 6, 8}" in the gaxi_skid_buffer header), not a consequence
            of counter width.
  Impact:   The recommended set is fine, but the stated reason is false: a reader
            needing depth 10–15 is told the counter breaks when it would not, and a
            reader inferring the real limit from the rationale would wrongly conclude
            16 is safe. The entry-count (not log2) clarification itself is correct
            and matches the RTL.
```

```
[SUSPECTED] Unsourced power-savings figure on both _cg pages
  File:     docs/markdown/RTLAmba/axi4/axi4_slave_rd_cg.md and axi4_slave_wr_cg.md
  Says:     "Power Savings: 25-70% depending on traffic utilization"
  Actually: No measurement, simulation, or synthesis reference is given anywhere in
            this unit, and I cannot derive the number from the RTL. It may be true
            for some workload, but as written it is an unmeasured claim stated as fact.
  Impact:   A reader quoting the figure for a power budget has no basis for it.
```

```
[CONFIRMED] Usage example in axi4_master_wr_stub.md references BSize without declaring it
  File:     docs/markdown/RTLAmba/axi4/axi4_master_wr_stub.md
  Says:     "wire [7:0] b_id   = tb_b_pkt[BSize-1:BSize-8];" (in the "Parse B packet"
             block) — the example explicitly declares `localparam AWSize = ...` and
             `localparam WSize = ...` but never declares BSize.
  Actually: The sibling example in axi4_slave_wr_stub.md does declare it
            ("localparam BSize = 8 + 2 + 4;"). As written, this snippet has an
            undeclared identifier. The slice arithmetic itself is correct
            (BSize=14 for IW=8/UW=4: id=[13:6], resp=[5:4], user=[3:0] — matches the
            {bid,bresp,buser} concatenation in the RTL).
  Impact:   Minor; example fragment fails as written, trivial fix for consistency
            with the sibling page.
```

```
[SUSPECTED] arlen described as "Burst length (0-255 beats)"
  File:     docs/markdown/RTLAmba/axi4/axi4_slave_rd.md (s_axi_arlen row) and
            axi4_slave_wr.md (s_axi_awlen row)
  Says:     "Burst length (0-255 beats)"
  Actually: Per AXI4, AxLEN encodes transfers−1: the 8-bit field value 0–255
            represents 1–256 beats; 0 is not "0 beats". The RTL port is 8 bits
            (`input logic [7:0] s_axi_arlen`) with no interpretation. Low severity —
            the raw range is right, the "beats" label is off by one.
  Impact:   A reader could believe a zero-beat burst is encodable or that the max
            burst is 255 beats rather than 256.
```

```
[CONFIRMED] Gap: axi4_slave_rd.md and axi4_slave_wr.md parameter tables omit RTL parameters
  File:     docs/markdown/RTLAmba/axi4/axi4_slave_rd.md, axi4_slave_wr.md
  Says:     Parameter tables list only SKID_DEPTH_*, AXI_ID_WIDTH, AXI_ADDR_WIDTH,
            AXI_DATA_WIDTH, AXI_USER_WIDTH; the "Module Interface" code blocks show
            the same reduced list.
  Actually: Both modules also expose overridable parameters AXI_WSTRB_WIDTH, AW, DW,
            IW, SW, UW, and the packet-size parameters (ARSize/RSize or AWSize/WSize/
            BSize). The stub pages in this same book document the full set (the
            slave_rd_stub page even notes AXI_WSTRB_WIDTH is "unused"), so the base
            pages are internally inconsistent with their siblings. Notably, the
            slave_wr doc hard-codes s_axi_wstrb as `[AXI_DATA_WIDTH/8-1:0]` where
            the RTL uses `[SW-1:0]` with SW=AXI_WSTRB_WIDTH — equal only by default.
  Impact:   Low; affects only a reader overriding AXI_WSTRB_WIDTH or the alias/size
            parameters, who would not learn from these pages that they can.
```

Everything else I checked matched: all parameter defaults; all port names, widths, and directions (including `fub_axi_aw_count`/`fub_axi_ar_count` being present exactly where the RTL connects `rd_count` and absent where RTL leaves it unconnected); all five packet layouts against the RTL concatenations; the `busy` equations (verbatim match in both base modules); `axi4_slave_stub`'s internal instantiation of `axi4_slave_wr_stub` + `axi4_slave_rd_stub`; and every bit-slice in the usage examples (AW/AR packet slices at ARSize/AWSize=73, W packet slices at WSize=77, B and R packet builds at 14 and 79 bits — all arithmetically consistent with the documented field order).

## POSSIBLE RTL BUGS

None confirmed. One portability observation only: `clock_gate_ctrl.sv` uses `[N-1:0]` in its ANSI port list where `localparam int N = IDLE_CNTR_WIDTH` is declared later in the module body. This is a reference-before-declaration that strict tools may reject; most mainstream tools accept it. SUSPECTED, low confidence, no functional impact where accepted.

The two `_cg` wrappers themselves do contain real gating logic (`amba_clock_gate_ctrl` → `clock_gate_ctrl` → `icg`), so the known `*_mon_cg` "no gating logic" issue does not apply here.

## Overall assessment

The six non-CG pages are in good shape: the stub pages in particular are precise — packet formats, field orders, count ports, and example arithmetic all verify exactly against the RTL, and the earlier log2-vs-count confusion has been properly corrected. The two clock-gated-variant pages are the outlier and should be rewritten before release: their parameter tables, quick-usage examples, and "same ports as base" claims describe a module that does not exist in this RTL, omitting the actual interface (`cfg_cg_enable`, `cfg_cg_idle_count`, `cg_gating`, `cg_idle`, `CG_IDLE_COUNT_WIDTH`, and the absence of `busy`). The wrong `clock_gate_ctrl` port names in the two base pages' clock-gating examples and the counter-overflow rationale are smaller but confirmed defects worth fixing in the same pass.