# Review: axi5 book

I checked every parameter table, port list, derived-width formula, gating-behavior description, and numeric claim in the 9 pages against the 8 modules plus `gaxi_skid_buffer`, `amba_clock_gate_ctrl`, and `clock_gate_ctrl` in `RTL.sv`. The findings below are what survived verification.

---

```
[CONFIRMED] Slave *_cg pages document cfg_cg_idle_count as a log2 exponent; the RTL counter is a linear countdown
  File:     docs/markdown/RTLAmba/axi5/axi5_slave_rd_cg.md and docs/markdown/RTLAmba/axi5/axi5_slave_wr_cg.md
  Says:     "| 1-3 | 2-8 | Balanced, reduces gate churn |
             | 4-7 | 16-128 | Conservative, for bursty traffic |
             | 8+ | 256+ | Minimal gating, continuous operation |"
            and in both usage examples:
            ".cfg_cg_idle_count  (4'd3),          // Gate after 8 idle cycles"
  Actually: clock_gate_ctrl loads the configured value and decrements by one:
              r_idle_counter <= cfg_cg_idle_count;          // on wakeup/reset
              r_idle_counter <= r_idle_counter - 1'b1;      // each idle clock
              w_gate_enable = cfg_cg_enable && !wakeup && (r_idle_counter == 'h0);
            Gating is therefore cfg_cg_idle_count + 1 clocks after wakeup
            deasserts — exactly what the clock_gate_ctrl header says
            ("Latency: cfg_cg_idle_count + 1 clocks from last wakeup to
            gating") and what the AXI5 master-side pages correctly document
            (axi5_master_rd_cg.md: "Gating engages cfg_cg_idle_count + 1
            clocks after the internal wakeup deasserts", table "1-3 | 2-4
            cycles"). 4'd3 gates after 4 idle cycles, not 8. With the default
            CG_IDLE_COUNT_WIDTH=4 the maximum is 15+1=16 cycles, so the
            "256+" row is unreachable at any legal value.
  Impact:   A reader sizes cfg_cg_idle_count=7 expecting ~128 idle cycles
            before gating and gets 8. This is also an internal contradiction:
            the master *_cg pages and slave *_cg pages give incompatible
            tables for the same parameter of the same shared controller, and
            the master_rd_cg example ("4'd3 // Gate after 4 idle cycles")
            directly contradicts the slave examples for the identical value.
```

```
[CONFIRMED] README module table and slave_wr.md opening claim the slaves generate/handle responses; the RTL only transports them
  File:     docs/markdown/RTLAmba/axi5/README.md ; docs/markdown/RTLAmba/axi5/axi5_slave_wr.md
  Says:     README: "| **axi5_slave_wr** | AXI5 write slave with write response generation |"
            README: "| **axi5_slave_rd** | AXI5 read slave with configurable response handling |"
            axi5_slave_wr.md: "implements a complete AMBA AXI5 slave write
            interface with full AXI5 protocol support."
  Actually: In axi5_slave_wr the B channel is a pure skid: the response comes
            from the backend (`input logic fub_axi_bvalid/bresp/buser`, packed
            into w_b_wr_data) and `assign s_axi_bvalid = int_skid_bvalid;`.
            No response-generation or response-handling logic exists anywhere
            in the file. axi5_slave_rd is the same for the R channel
            (`assign s_axi_rvalid = int_skid_rvalid;` with the payload packed
            from fub_axi_r* inputs). The README's own Scope section says the
            opposite of its table: "It does not execute AXI5 semantics...
            Those behaviors belong to the endpoint", and slave_wr.md's own
            Scope paragraph contradicts its opening sentence two lines later.
  Impact:   Low-to-moderate. The scope disclaimers limit the damage, but the
            category table is what shows up in indexes and search results; a
            reader could conclude axi5_slave_wr terminates writes on its own
            rather than requiring a backend that drives fub_axi_b*.
```

```
[CONFIRMED] AXI_WSTRB_WIDTH missing from the axi5_slave_wr / axi5_slave_wr_cg parameter tables
  File:     docs/markdown/RTLAmba/axi5/axi5_slave_wr.md and docs/markdown/RTLAmba/axi5/axi5_slave_wr_cg.md
  Says:     Parameter tables list SKID depths, ID/ADDR/DATA/USER widths,
            ATOP/NSAID/MPAM/MECID/TAG/TAGOP widths and the ENABLE_* bits, then
            a derived row "| SW | AXI_WSTRB_WIDTH | Write strobe width, one
            bit per data byte |" — the AXI_WSTRB_WIDTH parameter itself, its
            default, and its overridability never appear.
  Actually: `parameter int AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8` is a real
            overridable parameter of axi5_slave_wr/axi5_slave_wr_cg and sets
            the s_axi_wstrb/fub_axi_wstrb port width via SW
            (`input logic [SW-1:0] s_axi_wstrb`). The sibling pages handle
            this correctly: axi5_master_wr.md and axi5_master_wr_cg.md list it
            in the main table, and the read-side pages carry an explicit
            "Note on AXI_WSTRB_WIDTH".
  Impact:   Minor gap. A reader of the slave-write pages cannot discover the
            strobe-width default or that it is independently overridable.
```

```
[SUSPECTED] MTE terminology: "(Match/Insert/Fetch)" TAGOP operations; AWTAG presented as an AXI5 MTE signal
  File:     docs/markdown/RTLAmba/axi5/axi5_master_rd.md ; docs/markdown/RTLAmba/axi5/README.md
  Says:     axi5_master_rd.md: "**ARTAGOP:** Specifies tag operation
            (Match/Insert/Fetch)"
            README sideband table: "| AWTAG | AW | MTE address tags |"
  Actually: Not verifiable against the provided RTL (the module transports
            TAGOP and AWTAG opaquely, so doc and RTL are mutually consistent).
            Against the ARM AMBA spec, though: the MTE TAGOP operations are
            Invalid/Insert/Transfer/Match — there is no "Fetch"; and the AXI5
            MTE signal set (AxTAGOP, WTAG, WTAGUPDATE, RTAG, BTAG,
            xTAGMATCH) contains no AWTAG signal — address-related tag payloads
            travel on WTAG. AWTAG appears to be a library-specific extra
            signal, but the README lists it inside a table titled "AXI5
            Sideband Signals Carried by These Modules" without flagging it as
            non-standard.
  Impact:   A reader cross-referencing the AMBA spec will not find AWTAG or
            the "Fetch" operation. Marking SUSPECTED because the spec is
            outside the material provided; worth the author double-checking.
```

```
[SUSPECTED] Unhedged quantitative claims on the slave *_cg pages: "<50ps" gating delay, "<1% of savings" overhead
  File:     docs/markdown/RTLAmba/axi5/axi5_slave_rd_cg.md and docs/markdown/RTLAmba/axi5/axi5_slave_wr_cg.md
  Says:     "**Timing:** Clock gating adds minimal delay (typically <50ps)"
            "**Power:** Overhead from gate control logic usually <1% of savings"
            (also "**Area:** ~2-5% increase")
  Actually: Cannot verify from the material; no synthesis or simulation data
            is cited. These numbers are technology- and library-dependent
            (the ICG cell is an external tech primitive — `icg u_icg` is not
            even in this source set), yet unlike the power figures on the
            same pages they carry no "first-order estimate, not measured"
            disclaimer.
  Impact:   Low. Readers may quote the <50ps figure as a characterization
            result. Recommend either deleting or folding under the same
            disclaimer the pages already use for the power numbers.
```

## POSSIBLE RTL BUGS

None found. The skid buffer, packing/unpacking, conditional field widths, busy equations, forced-ready muxes, and the clock-gating controller all behave as documented. Specifically verified: the `busy` OR-terms in all four base modules, the activity equations in all four `_cg` wrappers (they match the doc code snippets verbatim, including the documented `rready`/`bready`-tied-high caveat), the gating-only-when-empty safety (rd_valid is registered and is 0 whenever count is 0, so no valid can be stranded high while gated), and the simultaneous read/write slot logic in `gaxi_skid_buffer` (write lands at `count-1` after the shift, which is correct for both `count==1` and full cases). Minor lint noise only: `int_ar_pkt`/`int_r_pkt`/`int_aw_pkt` etc. are declared but unused in the base modules.

## Overall assessment

This book is in good shape — substantially more accurate than the average for this library. Every parameter default, port name, port width, and enable in the eight module pages matches the RTL; the derived-width formulas (NUM_TAGS, TW, CHUNK_STRB_WIDTH, ARSize/RSize sums) recompute correctly; the "AXI_WSTRB_WIDTH is declared but unused" notes are honest and correct; the AWATOP class/endian/opcode tables match the AXI spec; and the transport-only scope disclaimers are prominent, repeated, and accurate. The 8 GB/s figure for a 128-bit bus at 500 MHz checks out (16 B × 500 MHz), the "1 cycle per SKID stage" latency and sustained 1-beat/clock throughput claims hold against the registered-ready/registered-valid skid implementation, and the wake-latency analysis on the master `_cg` pages (1 register stage via `r_wakeup`, combinational ICG enable) is exactly what the RTL does.

The one systematic defect is the slave-side `_cg` idle-count documentation, which uses a 2^N interpretation of a linear counter and contradicts the master-side pages of the same book — that should be fixed before release. The remaining items (response-generation overclaims in the README table and slave_wr.md's opening line, the missing AXI_WSTRB_WIDTH rows on the slave write pages, and a handful of unhedged or spec-divergent details) are small. Per the review brief I did not re-report the placeholder timing diagrams, the "Production Ready" markers, or the generally unsourced performance estimates that the pages themselves already flag as uncharacterized.