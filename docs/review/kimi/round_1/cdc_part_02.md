# Review: cdc_part_02 — APB5 Slave CDC and CDC+CG pages

Both pages were checked line-by-line against `rtl/amba/apb5/apb5_slave_cdc.sv`, `apb5_slave_cdc_cg.sv` and the dependency chain (`gaxi_fifo_async`, `fifo_control`, `cdc_synchronizer`, `amba_clock_gate_ctrl`, `clock_gate_ctrl`, `counter_bingray`, `gaxi_skid_buffer`). These are unusually accurate pages; the findings are few but one is a genuine trap for a reader.

---

## Findings

```
[CONFIRMED] DEPTH documented as "one of {2, 4, 6, 8}", but DEPTH=6 fails elaboration
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc.md
  Says:     "| DEPTH | int | 2 | Skid-buffer depth of the wrapped `apb5_slave`; one of {2, 4, 6, 8} |"
  Actually: DEPTH also feeds `localparam int CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH;`, which is
            passed to both `gaxi_fifo_async` instances. Those use the default `USE_JOHNSON=0`
            (Gray), and gaxi_fifo_async contains an elaboration-time check:
              if ((USE_JOHNSON == 0) && ((DEPTH & (DEPTH - 1)) != 0))
                  $error("... requires a power-of-2 DEPTH, got %0d ...");
            DEPTH=6 → CDC_FIFO_DEPTH=6 → 6 & 5 = 4 ≠ 0 → $error. The set that actually
            elaborates is {2, 4, 8} (2 maps to FIFO depth 4). The {2,4,6,8} set is the
            gaxi_skid_buffer constraint, which the doc applied to the whole module without
            accounting for the Gray-pointer FIFO.
  Impact:   A reader instantiating with DEPTH=6 -- a value the doc explicitly blesses --
            gets a build-time error. Doc should say {2, 4, 8} (or note that non-power-of-2
            depths above 4 are rejected by the async FIFO).
```

```
[CONFIRMED] Reset section contradicts itself; the "transaction time out" claim is the wrong half
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc.md
  Says:     "...instead of fabricating or swallowing a transfer." (paragraph 1), then two
            sentences later: "A transfer already accepted on the APB side but not yet read
            out will not be delivered, so the APB master may see a transaction time out."
  Actually: "Not delivered" *is* being swallowed, so the page contradicts itself -- and the
            second claim is the incorrect one. Trace: for u_cmd_cdc_fifo, the write side is
            clocked/reset by pclk/presetn; only the read side uses aresetn. Pulsing aresetn
            zeroes the read pointer and the read-domain *copy* of the write pointer
            (wr_ptr_gray_cross_inst: .d(r_wr_ptr_gray), .rst_n(axi_rd_aresetn)), but
            r_wr_ptr_gray itself is driven live by the still-running pclk-domain counter.
            Within N_FLOP_CROSS=2 aclk cycles after aresetn deasserts, the copy re-converges
            to the true write pointer, fifo_control's rd_empty deasserts, and rd_valid
            re-presents the entry. The command *is* delivered (late), the backend responds,
            and the APB transfer completes. The same applies symmetrically to the response
            FIFO. The "quiesce the bus first" advice that follows is still sound (see RTL
            bug B below for the corner that genuinely justifies it).
  Impact:   A reader designing reset strategy would believe a backend-only reset can hang
            the APB master and add unnecessary recovery logic (or avoid a legitimate
            one-sided-reset use the hardware actually supports).
```

```
[SUSPECTED] parity_error_* grouped under the "aclk domain" backend interface; they are pclk-domain pulses
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc.md
  Says:     "Same command/response interface as [apb5_slave](apb5_slave.md) - operates in
            the `aclk` domain. `wakeup_request`, `parity_error_wdata` and
            `parity_error_ctrl` are also present."
  Actually: wakeup_request is genuinely an aclk-domain input (synchronized internally --
            correct). But parity_error_wdata/ctrl are assigned combinationally inside
            apb5_slave from pclk-domain signals
            (`assign parity_error_wdata = (s_apb_PSEL && s_apb_PENABLE) ? ... : 1'b0;`)
            and are wired straight through apb5_slave_cdc with no synchronizer. They are
            single-pclk-cycle pulses. The doc never says "aclk domain" for them explicitly,
            but listing them under a section introduced as "operates in the aclk domain"
            implies it (and the RTL port comment states it outright -- see RTL bug A).
  Impact:   An integrator who connects these flags to backend (aclk) logic creates a CDC
            violation and will likely miss the 1-cycle pulses entirely.
```

```
[CONFIRMED] Off-by-one: "max idle = 2^N-1 cycles" for CG_IDLE_COUNT_WIDTH
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc_cg.md
  Says:     "| CG_IDLE_COUNT_WIDTH | int | 4 | Width of idle counter (max idle = 2^N-1 cycles) |"
  Actually: clock_gate_ctrl loads cfg_cg_idle_count and gates when the counter reaches 0,
            i.e. cfg_cg_idle_count + 1 cycles after last activity (clock_gate_ctrl's own
            header: "Latency: cfg_cg_idle_count + 1 clocks from last wakeup to gating").
            Max cfg value is 2^N-1, so max idle time is 2^N cycles (16 for N=4), not 2^N-1.
  Impact:   Negligible; one-cycle error in a parenthetical on a tunable power knob.
```

### Checked and verified correct (no action needed)

- All parameter names, types, and defaults in both tables, including `CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH` quoted verbatim, the absence of `CMD_DEPTH`/`RSP_DEPTH`/`SYNC_STAGES`, `USE_2_PHASE_CDC` being ignored, and fixed `N_FLOP_CROSS(2)`.
- All port names in both usage examples exist with the stated widths/directions; the examples would compile (with the usual "..." elisions).
- The wake-up path description in `apb5_slave_cdc_cg.md` matches the RTL exactly: `r_aclk_activity_sync1/2` 2-flop synchronizer over `cmd_valid || rsp_valid || wakeup_request`, OR-ed with `s_apb_PSEL || s_apb_PENABLE` into `r_wakeup`, then the flop inside `amba_clock_gate_ctrl`, then the ICG in `clock_gate_ctrl`. The "2 register stages, first usable edge 3 ungated pclk cycles" figure traces correctly (trigger edge → r_wakeup → cg_ctrl r_wakeup → combinational w_gate_enable → next ICG edge). The claim that wake-up latency is independent of `cfg_cg_idle_count` is correct.
- Latency estimate in `apb5_slave_cdc.md` ("2-3 destination-clock cycles per direction") is consistent with registered Gray pointer + 2-flop sync + registered `rd_empty`.
- The cross-family statement "Activity is registered once (AXI4...) or twice (APB, APB5...)" is consistent with this module; the other families' RTL was not in this bundle, so that part is unverified here.

---

## POSSIBLE RTL BUGS

**A. `parity_error_*` domain comment and export are wrong/unsafe (both files).** `apb5_slave_cdc.sv` declares `// Parity error flags (aclk domain, active when ENABLE_PARITY=1)` on the ports, but the flags are combinational functions of pclk-domain APB inputs inside `apb5_slave`, passed through with no synchronizer. Either the comment/domain intent is wrong (consumer must be pclk-domain, in which case the doc's interface grouping misleads) or the design is missing a synchronizer/pulse-stretcher for aclk-domain consumers. Same comment in `apb5_slave_cdc_cg.sv`.

**B. The header comment in `apb5_slave_cdc.sv` overstates the one-sided-reset guarantee.** "an independent reset of one side cannot fabricate or swallow a transfer" holds for *pointer self-consistency* (no lockup, no permanent desync), but not for transfer counting: pulsing `aresetn` after a command has been *read* but before its response is consumed resets the cmd read pointer to 0, and the entry is re-presented after re-sync -- the backend executes the command **twice**. Symmetrically, a response written but not yet read can be dropped when the aclk-side write pointer resets. The hardware recovers cleanly; the claim of "cannot fabricate or swallow" is too strong, and it is the source of the doc's muddled reset paragraph (finding 2). Related minor comment issue: "power of 2 preferred" for `CDC_FIFO_DEPTH` understates the constraint -- under the default Gray encoding a non-power-of-2 depth is an elaboration `$error`, not a preference.

---

## Overall assessment

These two pages are well above average for this library: the parameter tables, the FIFO sizing formula, the fixed 2-flop synchronization, the wake-up staging, and the 3-cycle wake latency all check out against the RTL, and the usage examples use real ports and legal parameters. The defects worth fixing before release are the `DEPTH=6` elaboration trap (a reader-acts-on-it error), the self-contradictory reset paragraph whose "timeout" consequence is backwards, and the misleading placement of the pclk-domain parity-error flags on the aclk backend interface -- which mirrors an actual RTL domain-comment bug worth fixing at the source.