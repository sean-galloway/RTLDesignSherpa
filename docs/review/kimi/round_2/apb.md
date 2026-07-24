# Review: `apb` book (RTL AMBA APB4)

I verified every parameter table, port list, packet format, FSM description, and numeric claim in the 11 pages against the bundled RTL, recomputing widths, latencies, and field offsets where numbers appear. The generated crossbars (`apb_xbar_1to1/2to1/1to4/2to4`) and `arbiter_round_robin_weighted` are **not** in the RTL bundle, so claims specific to them are noted as unverifiable rather than confirmed.

---

## Findings

```
[CONFIRMED] README Quick Start examples would not compile: wrong clock/reset port names; apb_master example passes a nonexistent DEPTH parameter
  File:     docs/markdown/RTLAmba/apb/README.md
  Says:     "apb_master #(.ADDR_WIDTH(32), .DATA_WIDTH(32), .DEPTH(2)) u_apb_master (
             .aclk (clk), .aresetn (resetn), ..." and the apb_slave example likewise uses .aclk/.aresetn
  Actually: rtl/amba/apb/apb_master.sv and rtl/amba/apb/apb_slave.sv declare `input logic pclk, presetn`
            -- there are no `aclk`/`aresetn` ports. apb_master's parameters are ADDR_WIDTH, DATA_WIDTH,
            PROT_WIDTH, CMD_DEPTH, RSP_DEPTH, STRB_WIDTH -- there is no DEPTH parameter (that is
            apb_slave's parameter). The master example fails on three counts (.aclk, .aresetn, .DEPTH);
            the slave example on two (.aclk, .aresetn).
  Impact:   The book's front-page copy-paste examples fail elaboration. First thing a new user tries.
```

```
[CONFIRMED] Packed command formats in both stub docs swap paddr and pwdata relative to the RTL
  File:     docs/markdown/RTLAmba/apb/apb_master_stub.md
  Says:     "Command Packet Format (MSB to LSB): last, first, pwrite, pprot, pstrb, pwdata, paddr"
            and the example: "assign test_cmd_data = {1'b1, 1'b1, 1'b1, 3'b000, 4'hF, 32'hDEADBEEF, 16'h1000};
            // Pack command: addr=0x1000, data=0xDEADBEEF"
  Actually: rtl/amba/apb/apb_master_stub.sv:
            `assign {cmd_last, cmd_first, cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata} = cmd_data;`
            -- paddr sits ABOVE pwdata. Decoded per the RTL, the doc's example vector yields
            paddr=16'hDEAD, pwdata=32'hBEEF_1000 -- exactly swapped from its stated intent.
  Impact:   These stubs exist for testbench authors who hand-pack cmd_data. Anyone following the doc
            drives the wrong address and wrong write data with no error message.
```

```
[CONFIRMED] apb_slave_stub.md has the same paddr/pwdata swap, contradicts its own comparison table, and its unpack example uses the wrong bit offsets
  File:     docs/markdown/RTLAmba/apb/apb_slave_stub.md
  Says:     "Command Packet Format (MSB to LSB): pwrite, pprot, pstrb, pwdata, paddr"
            and the example: "logic [AW-1:0] addr = test_cmd_data[AW-1:0];
                              logic [DW-1:0] wdata = test_cmd_data[AW+DW-1:AW];"
            but its own later table says: "Command fields | pwrite, pprot, pstrb, paddr, pwdata | ..."
  Actually: rtl/amba/apb/apb_slave_stub.sv:
            `assign r_cmd_data = {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata};`
            -- paddr above pwdata, matching the doc's comparison table but not its format section.
            Per RTL packing, pwdata occupies [DW-1:0] and paddr [DW+AW-1:DW], so the example's
            `addr = data[AW-1:0]` reads write-data bits.
  Impact:   Internal contradiction plus disagreement with the RTL; a responder written to the doc
            decodes address and data swapped.
```

```
[CONFIRMED] Entry-count parameters still annotated as log2 exponents in code examples, contradicting the same pages' corrected prose
  File:     docs/markdown/RTLAmba/apb/apb_master.md
  Says:     ".CMD_DEPTH(4),      // 16-entry command FIFO" / ".RSP_DEPTH(4)       // 16-entry response FIFO"
  Actually: The same page's parameter section says "CMD_DEPTH and RSP_DEPTH are literal entry counts...
            Supported values are {2, 4, 6, 8}." CMD_DEPTH(4) builds a 4-entry gaxi_skid_buffer
            (rtl/amba/gaxi/gaxi_skid_buffer.sv: `logic [DW-1:0] r_data [DEPTH]`).
  Impact:   Reader sizes buffering 4x larger than intended; undermines the page's own correction.

[CONFIRMED] Same defect in apb_slave.md examples, plus an illegal parameter value
  File:     docs/markdown/RTLAmba/apb/apb_slave.md
  Says:     ".DEPTH(2)            // 4-entry buffers" (Basic Register Block Interface) and
            ".DEPTH(3)            // 8-entry buffers for memory latency" (Memory Interface Example)
  Actually: DEPTH is a literal count (2 entries, not 4); and 3 is not a supported value at all --
            the page itself says "Supported values are {2, 4, 6, 8}", matching gaxi_skid_buffer's
            "Depth is expected to be one of {2, 4, 6, 8}".
  Impact:   Wrong capacity expectations; DEPTH(3) is also flagged unsupported by the doc itself.
```

```
[CONFIRMED] apb_slave module declaration / parameter table claims STRB_WIDTH defaults to DATA_WIDTH/8; RTL hardcodes 32/8
  File:     docs/markdown/RTLAmba/apb/apb_slave.md
  Says:     "parameter int STRB_WIDTH      = DATA_WIDTH / 8" and table row "STRB_WIDTH | int | DATA_WIDTH/8"
  Actually: rtl/amba/apb/apb_slave.sv: `parameter int STRB_WIDTH = 32 / 8` (literal 32).
            rtl/amba/apb/apb_slave_cg.sv has the same `32 / 8`. By contrast apb_master.sv and
            apb_slave_cdc.sv do use `DATA_WIDTH / 8`.
  Impact:   None at DATA_WIDTH=32, but at any other data width the default strobe width is wrong
            and the doc tells the user it is derived. See POSSIBLE RTL BUGS (A).
```

```
[CONFIRMED] Enhanced-backend example labels PPROT[0] as "Instruction access" -- wrong bit
  File:     docs/markdown/RTLAmba/apb/apb_slave.md
  Says:     "assign prot_error = (cmd_prot[0] == 1'b1);                 // Instruction access"
  Actually: Per the book's own PPROT table (apb_master.md: "PPROT[2]: 0=Data, 1=Instruction";
            PPROT[0] is Normal/Privileged) and the AMBA APB4 spec, instruction is bit 2.
  Impact:   Example logic flags privileged access while claiming to flag instruction access;
            misleading in a section titled "Error Handling".
```

```
[CONFIRMED] Multiple examples use non-legal partial-prefix wildcard connections
  File:     docs/markdown/RTLAmba/apb/apb_slave.md and docs/markdown/RTLAmba/apb/apb_master.md
  Says:     ".s_apb_*(apb_*)", ".cmd_*(mem_cmd_*)", ".rsp_*(backend_rsp_*)" (apb_slave.md: Memory
            Interface, Multi-Register Bank, Clock Domain Optimization);
            ".m_apb_*(apb_m_*)", ".m0_apb_*(apb_m_*)", ".s0_apb_*(slave0_apb_*)" (apb_master.md:
            APB Crossbar Integration)
  Actually: SystemVerilog has `.*` and `.name` shorthands only; prefixed wildcards like `.s_apb_*`
            do not exist. Additionally, the Multi-Register Bank example connects `.cmd_ready(
            bank_cmd_ready[i])` where `bank_cmd_ready` is never declared, and never muxes read
            data back (rsp_valid is OR-reduced but rsp_prdata is left undriven).
  Impact:   Examples cannot be compiled as written, even after filling in the ellipses.
```

```
[CONFIRMED] apb_master timing table understates first-transfer setup by one cycle
  File:     docs/markdown/RTLAmba/apb/apb_master.md
  Says:     "Setup Phase | 1 clock cycle" and "Total Latency | 2+ clock cycles | Minimum transaction time"
  Actually: rtl/amba/apb/apb_master.sv FSM: in IDLE with r_cmd_valid it asserts m_apb_PSEL and moves
            to SETUP; SETUP asserts PSEL again; ACCESS asserts PSEL+PENABLE. A transfer starting from
            idle therefore holds PSEL high with PENABLE low for TWO cycles and completes no earlier
            than the third cycle. (Back-to-back continuations via `w_cmd_count > 1 -> SETUP` do have
            one setup cycle and a 2-cycle total, which is presumably what the table describes.)
  Impact:   Low. Latency budgets computed from the table are one cycle optimistic for the first
            transfer of a burst. Worth a "steady-state" qualifier.
```

```
[SUSPECTED] apb_xbar_thin "zero cycles of added latency" is incompatible with registered arbiter grants
  File:     docs/markdown/RTLAmba/apb/apb_xbar.md
  Says:     "apb_xbar_thin adds zero cycles of latency... An uncontended transfer completes in exactly
            the downstream slave's own transfer time" and "The only registers are the per-slave,
            per-master grant-ACK flops."
  Actually: apb_xbar_thin.sv muxes slaves by `arb_gnt_valid`/`arb_gnt_id` from
            arbiter_round_robin_weighted. That module's source is not in the bundle, but its sibling
            rtl/common/arbiter_round_robin.sv (same port list, same WAIT_GNT_ACK protocol) drives
            grant/grant_id/grant_valid from an `ALWAYS_FF_RST` block -- i.e., a fresh grant appears
            one cycle after the request. If the weighted variant is structured the same way, a new
            arbitration adds 1 cycle before s_apb_psel asserts, and the grant-ACK flops are not the
            only sequential logic in the path.
  Impact:   Latency-critical integrators (the page's stated audience: "the lowest-latency choice")
            would budget one cycle too few. Needs verification against arbiter_round_robin_weighted.sv.
```

---

## Unverifiable claims (generated crossbar RTL not in bundle)

`apb_crossbar.md`'s decode slice (`slave_sel = cmd_paddr[17:16]`), 64 KB region size, `BASE_ADDR` default/alignment rule, and the no-decode-error-slave behavior could not be checked against `apb_xbar_1to1/2to1/1to4/2to4`. The bundled `apb_xbar_rlb_1to10.sv` (same apb_slave + decode + apb_master architecture) is consistent with the doc's "unmapped addresses stall" claim -- its `m_cmd_ready` is gated by `addr_in_range` and it has no default slave -- which lends plausibility but is not proof for the generated family.

---

## POSSIBLE RTL BUGS

**A. `STRB_WIDTH = 32 / 8` default in `apb_slave.sv` and `apb_slave_cg.sv`.** Inconsistent with `apb_master.sv` and `apb_slave_cdc.sv`, which both use `DATA_WIDTH / 8`. Looks like a hardcoding slip; harmless only at the default data width. (Doc side flagged above.)

**B. `DEPTH=6` breaks `apb_slave_cdc` / `apb_slave_cdc_cg` at elaboration.** `CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH`, so `DEPTH=6` instantiates `gaxi_fifo_async` with `DEPTH=6, USE_JOHNSON=0`, tripping its elaboration `$error`: "USE_JOHNSON=0 (Gray) requires a power-of-2 DEPTH, got 6." Meanwhile `apb_slave.md` documents `{2,4,6,8}` as supported and `apb_slave_cdc.md` says powers of two are merely "preferred" for the FIFO. Either the CDC FIFO depth should round up to 8, or the docs should exclude 6 for the CDC variants. (Confirmed by arithmetic on the bundled source; not simulated.)

**C. `apb_master_stub` first/last side FIFO can silently overflow -- reintroducing the exact bug it was added to fix.** The FIFO is `DEPTH=CMD_DEPTH`, written on every `cmd_valid && cmd_ready`, read on every `rsp_valid && rsp_ready`; `fl_in_ready` is connected to nothing. Commands accepted but responses undelivered can reach `CMD_DEPTH (6) + 1 (FSM in flight) + RSP_DEPTH (6) = 13` when the user stalls `rsp_ready`: after 6 undelivered responses fill the side FIFO, the 7th accepted command's framing write is silently dropped (`gaxi_fifo_sync`: `w_write = wr_valid && wr_ready`), permanently misaligning first/last -- the failure mode the RTL comment and the doc describe fixing ("pairs command N's response with command N+1's framing bits... hanging the FSM"). The doc's claim "it never backpressures the command path more than that buffer already does" is true only because it never backpressures at all. The side FIFO needs depth `CMD_DEPTH + RSP_DEPTH + 1`, or its `wr_ready` must gate `cmd_ready`. (Confirmed by code analysis of the enqueue/dequeue rates; not simulated.)

**D. `apb_xbar_monitored.sv` width mismatch on THRESHOLDS.** `.THRESHOLDS({NUM_SLAVES{4'h4}})` supplies 16 bits (S=4) to a `MXMTW = M*MTW = 12`-bit port (M=3); it works only because the truncated value happens to be uniform 4s. Should be `{NUM_MASTERS{4'h4}}`. Benign today, silently wrong weights if the configuration changes. (This file is an integration example, not one of the documented modules.)

---

## Overall assessment

This book has plainly been through a serious correction pass: the DEPTH-as-entry-count corrections, the unmapped-address stall documentation, the `USE_2_PHASE_CDC` deprecation story, and the removal of fabricated latency/LUT/PSLVERR figures (per `apb_crossbar.md`'s revision history) are all accurate against the RTL I could check, and the FSM, CDC, and clock-gating descriptions are faithful -- I verified the wake-up pipeline arithmetic (`idle_count + 3` cycles to gate, 3-cycle wake) and the slave's ≥2-wait-state timing directly against the state machines. The remaining defects are concentrated and consistent: (1) quick-start and integration **code examples** were not updated alongside the prose (wrong port names, a nonexistent parameter, leftover log2 comments, illegal wildcard syntax); (2) both stub pages document the packed command field order with `paddr`/`pwdata` swapped versus the RTL, with `apb_slave_stub.md` contradicting itself between sections; and (3) the `apb_xbar_thin` "zero latency" headline claim is likely one cycle optimistic pending a check of the weighted arbiter. The stub first/last FIFO (item C) deserves simulation before the book ships, since it undermines the fix both the RTL comment and the documentation describe.