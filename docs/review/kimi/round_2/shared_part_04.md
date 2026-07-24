# Review: `shared_part_04` — AMBA Shims (axi4_to_apb_shim, axi4_to_apb_convert, peakrdl_to_cmdrsp, README)

I checked every port list, parameter table, packet-width formula, FSM description, and behavioral claim against the three RTL modules and their instantiated dependencies (`axi_gen_addr`, `gaxi_fifo_async`, `gaxi_fifo_sync`, `apb_master_stub`, `apb_master`, `gaxi_skid_buffer`, `axi4_slave_stub`). Findings ranked by value.

---

## Findings

```
[CONFIRMED] Docs describe a CDC implementation (cdc_handshake) that the RTL no longer uses
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_shim.md (also README.md)
  Says:     Architecture: "├── cdc_handshake (command) ... ├── cdc_handshake (response)";
            Behavior: "- Uses `cdc_handshake` module (Gray-code pointer-based)";
            Related Modules: "**[cdc_handshake](../cdc/cdc.md#cdc_4_phase_handshake)**";
            Constraints: "set_max_delay -from [get_pins */cdc_handshake/src_*] -to [get_pins */cdc_handshake/dst_*] 10.0"
            README: "**AXI to APB CDC:** - Uses `cdc_handshake` module" and the same
            "*/cdc_handshake/src_*" constraint pattern.
  Actually: axi4_to_apb_shim.sv instantiates NO cdc_handshake. Both crossings are
            `gaxi_fifo_async` (u_cmd_cdc_fifo: wr=aclk/rd=pclk; u_rsp_cdc_fifo:
            wr=pclk/rd=aclk, N_FLOP_CROSS=2). The RTL comment states the handshake was
            *replaced*: "CDC: gray-pointer async FIFOs ... an independent reset of one
            side cannot fabricate or swallow a transfer the way the previous 2-phase
            handshake could. That failure mode offsets the response stream permanently."
            The shim's own parameter `USE_2_PHASE_CDC` is annotated "deprecated, ignored".
  Impact:   The most damaging defect in this unit. The architecture diagram, behavior
            section, related-module link, and both constraint examples all describe a
            removed implementation. The SDC patterns reference hierarchy
            (*/cdc_handshake/src_*, dst_*) that matches nothing, so a reader copying
            them gets silently unconstrained CDC paths. The docs also miss the
            reset-independence rationale that motivated the redesign.
```

```
[CONFIRMED] peakrdl_to_cmdrsp documents four named protocol assertions that do not exist in the RTL
  File:     docs/markdown/RTLAmba/shims/peakrdl_to_cmdrsp.md
  Says:     "- ✅ **Assertions Included:** Comprehensive protocol checking (simulation only)"
            and a section listing "1. **cmd_valid_stable:** ... 2. **cmd_data_stable:** ...
            3. **rsp_valid_stable:** ... 4. **rsp_data_stable:** ..."
  Actually: peakrdl_to_cmdrsp.sv ends with:
                // =========================================================================
                // Assertions
                // =========================================================================
            followed by `endmodule` — the section is empty. No assertion of any kind exists.
  Impact:   A reader relying on the documented simulation-time protocol checking gets none;
            cmd/rsp handshake violations will pass silently.
```

```
[CONFIRMED] APB command packet width formula is wrong (+4 vs actual +6) and contradicts the doc's own field list
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_convert.md
  Says:     "APBCmdWidth = APBAW + APBDW + APBSW + 4 bits", followed by a field list of
            last, first, pwrite, pprot (3 bits), pstrb, paddr, pwdata.
  Actually: RTL: `parameter int APBCmdWidth = APBAW + APBDW + APBSW + 3 + 1 + 1 + 1`
            and `r_cmd_data = {last, first, pwrite, pprot[2:0], pstrb, paddr, pwdata}`.
            Overhead = pprot(3) + pwrite(1) + first(1) + last(1) = 6 bits. The doc's own
            field list sums to 6 (1+1+1+3), so the page contradicts itself. For the default
            32/32 config: doc formula gives 32+32+4+4 = 72; RTL is 74.
  Impact:   Anyone hand-sizing a cmd/rsp bus or writing a custom consumer from the formula
            is 2 bits short, misaligning every field above pwdata.
```

```
[CONFIRMED] Shim doc claims WLAST is used for burst completion; the RTL ignores WLAST entirely
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_shim.md
  Says:     "**Burst Decomposition:** ... - WLAST signal tracked to determine burst completion"
  Actually: In axi4_to_apb_convert.sv, `r_s_axi_wlast` is unpacked from the W packet
            (`assign {r_s_axi_wdata, r_s_axi_wstrb, r_s_axi_wlast, r_s_axi_wuser} = r_s_axi_w_pkt;`)
            and never referenced again. Burst completion is decided solely by the AWLEN-loaded
            counter: `if (r_burst_count == 0) begin ... w_apb_cmd_pkt_last = 1'b1; end`.
  Impact:   A reader believes early/missing WLAST is detected or used; it is not — a master
            with a broken WLAST will not be caught, and burst length is trusted blindly
            from AWLEN.
```

```
[CONFIRMED] Doc claims FIXED bursts are "converted to INCR"; RTL implements FIXED natively
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_convert.md
  Says:     "- **FIXED (0x00):** Same address (APB limitation: converted to INCR)"
  Actually: axi_gen_addr.sv: `2'b00: next_addr = curr_addr;   // FIXED burst` — the address
            is held constant, i.e., true FIXED behavior, no conversion to INCR.
  Impact:   Wrong expected address sequence for FIFO-style FIXED-burst accesses; a
            testbench written from the doc would check incrementing addresses the RTL
            never produces.
```

```
[CONFIRMED] "Error accumulation" claim is false for width-converted reads
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_convert.md
  Says:     "**Error Accumulation:** - Multiple APB PSLVERR errors OR'd together
            - Entire AXI transaction marked with error if any APB beat fails"
  Actually: `w_resp_rd = (w_pslverr) ? 2'b10 : 2'b00;` uses only the *current* APB
            response's error. The sticky accumulator `r_pslverr` feeds only `w_resp_wr`
            (`w_resp_wr = (w_pslverr | r_pslverr) ? 2'b10 : 2'b00;`). RVALID fires when the
            last slice of an AXI word arrives (pointer == AXI2APBRATIO-1), so for
            AXI_DATA_WIDTH > APB_DATA_WIDTH the RRESP reflects only the *last* APB slice's
            PSLVERR; errors on earlier slices of the same AXI word are dropped. Writes do
            accumulate as documented. (Doc's own code snippet shows the discrepancy.)
  Impact:   Overstates read error coverage exactly in the width-conversion configurations
            the module advertises. See also POSSIBLE RTL BUGS (b).
```

```
[CONFIRMED] SIDE_DEPTH documented as a hard constraint tied to burst length; RTL just throttles
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_convert.md and README.md
  Says:     convert: "- `SIDE_DEPTH` must be ≥ maximum AXI burst length (typically 16)"
            README: "- `SIDE_DEPTH` ≥ max(AXI burst length × width ratio)"
  Actually: Side-FIFO pushes are gated by `r_side_in_ready` (not-full) in both READ and
            WRITE states (`if (r_cmd_ready && r_side_in_ready)`), so a full FIFO stalls
            command issue; entries are popped on every consumed APB response. Depth is a
            throughput knob, not a correctness constraint — there is no overflow or deadlock
            path for small depths. The docs' own defaults/examples contradict the rule:
            convert default SIDE_DEPTH=6, shim default 4, and README Pattern 2 uses
            SIDE_DEPTH=8 — all below the 16 (or 32 for 16-beat × 2:1) the rule "requires".
  Impact:   Readers oversize the FIFO believing correctness depends on it.
```

```
[CONFIRMED] Side FIFO purpose overstated as "out-of-order response reconstruction"
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_convert.md
  Says:     "**Purpose:** - Preserves ID for out-of-order response reconstruction"
  Actually: A single APB FSM processes one transaction at a time and IDLE is held until
            the previous sequence fully drains: `if (~r_side_out_valid) // let the last
            command sequence clear out before the next`. Responses are strictly in order;
            no reordering/interleaving logic exists. The ID is preserved for pass-through
            only.
  Impact:   Minor, but implies a capability (ID-based reordering) a reader might design
            against.
```

```
[CONFIRMED] Internal contradiction: burst-latency row contradicts the same page's throughput claim
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_convert.md
  Says:     Latency table: "| AXI burst (AWLEN=15, 1:1 width) | 68-80 | 16 beats × 4-5 cycles |"
            Throughput section, same page: "**Maximum Throughput (same width):**
            - 1 APB transfer every 2 cycles (SETUP + ACCESS phases)"
  Actually: Recomputation from the page's own numbers: 16 beats × 2 cycles/beat = 32 cycles
            + fixed unpack/response overhead (~5) ≈ 37, not 68–80. The 4–5 cycles/beat in
            the table note directly contradicts the 2 cycles/beat throughput claim. The RTL
            supports the 2-cycle figure: apb_master goes ACCESS→SETUP back-to-back whenever
            more commands are queued (`if (w_cmd_count > 1) w_apb_next_state = SETUP;`).
  Impact:   The burst latency figure is ~2× the page's own math; readers cannot tell which
            to believe.
```

```
[CONFIRMED] regblk_req described as a 1-cycle strobe and "kept deasserted" when stalled; RTL does neither
  File:     docs/markdown/RTLAmba/shims/peakrdl_to_cmdrsp.md
  Says:     Port table: "| `regblk_req` | Output | 1 | Request strobe (valid for 1 cycle) |"
            Stall handling: "1. If stall asserted when cmd_valid: ... - Keep regblk_req
            deasserted"
  Actually: `assign regblk_req = (cmd_state == CMD_WAIT_ACK) || ((cmd_state == CMD_IDLE) && cmd_valid);`
            — req pulses during the initial IDLE cycle *even when stalled* (a 1-cycle pulse
            before CMD_STALLED is entered), and is then held high for the entire
            CMD_WAIT_ACK wait — as many cycles as the register block takes to ack. It is
            only "1 cycle" when ack returns immediately. The "Write Transaction with Stall"
            timing diagram (req asserted only after stall clears) omits the initial pulse.
  Impact:   Waveform-level expectations are wrong for delayed-ack or stalled accesses;
            minor since PeakRDL ignores req while stalled.
```

```
[CONFIRMED] Undocumented depth constraint on APB_CMD_DEPTH / APB_RSP_DEPTH (clamp-to-4 and power-of-2)
  File:     docs/markdown/RTLAmba/shims/axi4_to_apb_shim.md
  Says:     Only constraint given: "- All DEPTH_* parameters must be ≥ 2"
  Actually: `localparam int CDC_CMD_DEPTH = (APB_CMD_DEPTH < 4) ? 4 : APB_CMD_DEPTH;` (values
            < 4 are silently overridden for the CDC FIFO), and gaxi_fifo_async with the
            default USE_JOHNSON=0 raises an elaboration-time `$error` unless DEPTH is a
            power of 2: "USE_JOHNSON=0 (Gray) requires a power-of-2 DEPTH". So
            APB_CMD_DEPTH=6 — permitted by the doc — fails elaboration; =2 is silently
            ignored for the CDC path.
  Impact:   A user following the documented "≥ 2" rule hits a build error or gets a
            different FIFO depth than requested. (Note the same parameters also feed
            apb_master_stub's skid buffers, so e.g. 6 is meaningful there — the failure
            is specific to the CDC FIFO path.)
```

```
[SUSPECTED] All resource-usage tables (LUT/FF counts) are unsourced
  File:     All three module pages and README.md
  Says:     e.g. "axi4_to_apb_shim (32/32) | ~800 | ~600 | 0", "peakrdl_to_cmdrsp | ~50 | ~100",
            "~400 LUTs, ~300 FFs" for the convert core, plus a per-module breakdown that
            includes "2× cdc_handshake: ~200 LUTs".
  Actually: No synthesis run, device, or tool version is cited anywhere; I cannot verify
            any of these numbers from the material provided. The breakdown line item for
            "2× cdc_handshake" reinforces Finding 1's staleness.
  Impact:   Adjacent to the already-known-weak timing tables; flagged once here rather
            than per-row.
```

---

## POSSIBLE RTL BUGS

**(a) Unresolved editing instructions left in `axi4_to_apb_convert.sv`.** Both the READ and WRITE branches of the combinational FSM contain literal edit directives:

```
// REPLACE THIS SECTION:
if (r_apb_last_state == IDLE)           // ← OLD LOGIC - REMOVE
    w_apb_cmd_pkt_first = 1'b1;         // ← OLD LOGIC - REMOVE
// WITH THIS NEW LOGIC:
if (r_axi_rd_data_pointer == 0 && r_burst_count == r_s_axi_arlen)
    w_apb_cmd_pkt_first = 1'b1;
```

The "old" logic was never removed. It is functionally harmless today (the only cycle `r_apb_last_state == IDLE` is true inside READ/WRITE is the first beat, where the new condition is also always true), but the source is in a mid-edit state and the dead code's continued harmlessness depends on that invariant.

**(b) Read-path error accumulation looks unfinished.** `r_pslverr` is maintained as a sticky accumulator (`r_pslverr <= r_pslverr | w_pslverr;  // TODO: only assert w_pslverr when rsp is vld`) but is used *only* for `w_resp_wr`; `w_resp_rd` ignores it. Result: for `AXI2APBRATIO > 1`, a PSLVERR on any APB read slice other than the last slice of an AXI word is silently dropped from RRESP. Given the register exists and the doc claims OR-accumulation, this looks like an RTL bug (missing `| r_pslverr` in `w_resp_rd`) rather than just a doc overstatement — and the inline TODO confirms the author considers it unfinished.

**(c) Inconsistent `SideSize` between shim and convert.** `axi4_to_apb_shim.sv`: `parameter int SideSize = 1+IW+2+1+UW`; `axi4_to_apb_convert.sv`: `parameter int SideSize = 1+IW+1+UW`. The shim's version (with a spurious `+2`) is unused in the shim body, so it's dead rather than harmful, but it suggests a field was dropped from the side packet without cleaning up the parent.

**(d) Stale width comments in `axi4_to_apb_shim.sv`.** The `apb_master_stub` instantiation comments read `// ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 4` and `// DATA_WIDTH + 2`; the actual parameters passed are `APBAW+APBDW+APBSW+6` and `APBDW+3`. These comments are the likely origin of doc Finding 3 (the +4 formula).

**(e) Dead inputs/parameter.** `r_s_axi_aw_count` and `r_s_axi_ar_count` are inputs to `axi4_to_apb_convert` but never used; `USE_2_PHASE_CDC` in the shim is annotated "deprecated, ignored" (the docs correctly omit it — noting here for hygiene only).

---

## Overall accuracy

The three module pages are structurally sound: every documented port exists with the right direction and width, the parameter tables match RTL defaults (SIDE_DEPTH=6/4, DEPTH_* values, ADDR/DATA widths), the FSM descriptions (3-state APB FSM, 2-state response FSM, peakrdl cmd/rsp FSMs and their transitions) match the RTL, and the strobe-to-bit-enable example (`4'b1100 → 32'hFFFF_0000`) recomputes correctly. The code examples use real port names and would elaborate if the elided sections were filled in. However, the book was clearly not updated after a significant RTL rework of the shim's CDC: the `cdc_handshake` → `gaxi_fifo_async` replacement (done, per the RTL comment, to fix a reset-desync bug that corrupted the response stream) left the architecture diagram, behavior text, related-module links, README CDC notes, and the SDC constraint examples all describing the removed implementation — and the synthesis constraints now match no hierarchy, which is actively harmful if copied. Beyond that, the peakrdl page advertises four named assertions that simply do not exist, the command-packet width formula is arithmetically wrong and self-contradictory, WLAST/FIXED-burst/error-accumulation claims misdescribe the logic, the SIDE_DEPTH "constraint" is refuted by the throttling mechanism and by the docs' own defaults, and the RTL itself shows signs of the same unfinished edit pass (OLD LOGIC/REPLACE markers, stale +4/+2 comments, a dead SideSize parameter). The performance and area tables throughout are unsourced estimates consistent with the known-weak areas already flagged.