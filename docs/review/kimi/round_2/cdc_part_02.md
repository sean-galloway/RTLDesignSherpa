# Review: cdc_part_02 (APB5 Slave CDC / CDC+CG pages)

I checked every parameter, port, FIFO-sizing formula, synchronizer-stage count, wake-up latency figure, and the reset-behavior narrative against `apb5_slave_cdc.sv`, `apb5_slave_cdc_cg.sv`, and the dependency RTL (`gaxi_fifo_async`, `fifo_control`, `glitch_free_n_dff_arn`, `counter_bingray`, `amba_clock_gate_ctrl`, `clock_gate_ctrl`, `apb5_slave`, `gaxi_skid_buffer`). Four findings, two of them significant.

---

## Findings

```
[CONFIRMED] DEPTH=6 is documented as legal but fails elaboration
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc.md
  Says:     "| DEPTH | int | 2 | Skid-buffer depth of the wrapped `apb5_slave`;
            one of {2, 4, 6, 8} |"
  Actually: The wrapper computes CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH and
            feeds it to gaxi_fifo_async with USE_JOHNSON left at its default 0
            (Gray). gaxi_fifo_async contains an elaboration-time generate check:
              if ((USE_JOHNSON == 0) && ((DEPTH & (DEPTH - 1)) != 0))
                  $error("...requires a power-of-2 DEPTH, got %0d...", DEPTH);
            Recomputation: DEPTH=2 -> FIFO 4 (4&3=0, OK); DEPTH=4 -> 4 (OK);
            DEPTH=8 -> 8 (OK); DEPTH=6 -> FIFO 6, 6&5=4 != 0 -> $error fires.
            {2,4,6,8} is the gaxi_skid_buffer constraint, valid for the bare
            apb5_slave, but the CDC wrapper narrows it to {2,4,8} because the
            FIFO depth is max(DEPTH,4) and Gray encoding requires power-of-2.
            No USE_JOHNSON override is exposed on apb5_slave_cdc.
  Impact:   A reader who sets DEPTH=6 per the table gets a build failure at
            elaboration. Same exposure in apb5_slave_cdc_cg, though that page
            does not print the {2,4,6,8} set.
```

```
[CONFIRMED] One-sided-reset description is wrong: commands are re-presented
            (not dropped -> no timeout), and the response FIFO fabricates
            phantom responses on the APB side
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc.md
  Says:     "gaxi_fifo_async resets each domain's own pointer *and* that
            domain's crossed copy of the remote pointer from the local reset,
            so a one-sided reset leaves that side self-consistent ... instead
            of fabricating or swallowing a transfer."
            and
            "A transfer already accepted on the APB side but not yet read out
            will not be delivered, so the APB master may see a transaction
            time out."
  Actually: The "crossed copy of the remote pointer" is a live synchronizer
            (glitch_free_n_dff_arn, N=2) that keeps sampling the *non-reset*
            domain's pointer after reset deasserts; it does not stay at zero.
            Trace, cmd FIFO (wr=pclk, rd=aclk, CDC_FIFO_DEPTH=4, 3-bit
            pointers), one unread command (wr=1, rd=0), pulse aresetn only:
            rd_ptr->0 and synced wr->0 (empty) momentarily; two aclk edges
            later the synchronizer re-captures the live wr pointer (=1),
            fifo_control's empty equation (!xor && rd==wr) goes false and
            rd_valid reasserts -> the command IS delivered ~2 aclk cycles
            after reset. It is not discarded and there is no timeout.
            Worse, rsp FIFO (wr=aclk, rd=pclk): once any traffic has flowed,
            rd_ptr=N!=0 and it lives in the pclk domain, so an aresetn-only
            pulse leaves it at N while wr->0. Two pclk edges later the pclk
            side's synced copy of wr is 0 with rd=N, the empty compare fails,
            and rd_valid asserts for (2^(AW+1) - N) phantom reads (N=1 ->
            7 reads). apb5_slave's FSM consumes the first stale entry as the
            response to the next command (BUSY: `if (r_rsp_valid)` -> PREADY,
            PRDATA <= stale mem contents). So a one-sided reset CAN fabricate
            transfers -- the exact thing the doc says it cannot do. A
            presetn-only pulse fabricates phantom commands on the aclk side
            by the symmetric argument.
  Impact:   An integrator believes an aresetn-only pulse is benign (at worst
            a lost transaction) when in reality it can deliver stale/garbage
            responses to the APB master after any prior traffic. The closing
            advice "quiesce the bus first" is sound; the mechanism and the
            timeout claim are not. The milder echo in apb5_slave_cdc_cg.md
            ("The async FIFOs tolerate a one-sided reset without corrupting
            the pointer state") inherits the same misconception.
```

```
[CONFIRMED] parity_error_wdata/parity_error_ctrl are grouped with the
            aclk-domain backend interface but are pclk-domain combinational
            pulses
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc.md
  Says:     "### Backend Interface -- Same command/response interface as
            apb5_slave - operates in the `aclk` domain. `wakeup_request`,
            `parity_error_wdata` and `parity_error_ctrl` are also present."
  Actually: In apb5_slave (which generates them, in the pclk/gated-pclk
            domain):
              assign parity_error_wdata = (s_apb_PSEL && s_apb_PENABLE) ?
                  (w_expected_wdata_parity != s_apb_PWDATAPARITY) : 1'b0;
            i.e. combinational functions of pclk-domain APB inputs, asserted
            only during the APB access phase. wakeup_request genuinely is an
            aclk-domain input (correctly described elsewhere on the page),
            but the parity-error outputs are not in the aclk domain at all.
            The RTL port comment ("// Parity error flags (aclk domain, ...)")
            in apb5_slave_cdc.sv has the same error, which is presumably
            where the doc got it.
  Impact:   A backend that samples these with aclk faces an unsynchronized
            single-pclk-cycle pulse crossing: missed or metastable error
            indications. The doc should state they are pclk-domain.
```

```
[SUSPECTED] "CG idle=16" configuration is not expressible at the documented
            default CG_IDLE_COUNT_WIDTH=4
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc_cg.md
  Says:     "| CG idle=16 | Good | 2 register stages; first usable edge 3
            ungated pclk cycles |" (with CG_IDLE_COUNT_WIDTH default 4,
            "max idle = 2^N-1 cycles")
  Actually: cfg_cg_idle_count is ICW=4 bits wide by default, so the maximum
            load value is 15; 16 requires CG_IDLE_COUNT_WIDTH>=5. The table
            does not say the width was changed for that row.
  Impact:   Minor. A reader using defaults cannot select the "Good" row;
            writing 4'd16 would truncate to 0 (gate after the first idle
            cycle), the opposite of the intended effect.
```

## POSSIBLE RTL BUGS

1. **One-sided reset hazard in the async FIFOs (functional).** As traced in Finding 2, the reset-robustness claim written into `apb5_slave_cdc.sv` ("a domain reset in isolation leaves that side self-consistent (both pointers 0 => empty) instead of fabricating or swallowing a transfer") is incorrect at the system level: after an aresetn-only pulse, the response FIFO's pclk read side sees the write pointer jump backward (N -> 0) and generates `2^(AW+1) - N` phantom `rd_valid` beats of stale memory contents, which `apb5_slave` will consume as real responses. The design has no flush/protection mechanism for independent resets; the comment (and both doc pages) overstate the safety. Given the comment cites a real harness that pulses only the core-side reset, this looks like a latent data-corruption bug, not just a comment issue.

2. **Incorrect domain label on parity-error ports.** The port comments in `apb5_slave_cdc.sv` and `apb5_slave_cdc_cg.sv` say `// Parity error flags (aclk domain, ...)` but the signals are combinational outputs of pclk-domain logic inside `apb5_slave`. If any consumer actually hooks them to aclk-domain logic, that is an unsynchronized CDC of a one-cycle pulse. At minimum the comment is wrong; arguably the error flags need a synchronizer or sticky-register if aclk-domain consumption is intended.

## What checked out

The parameter tables, defaults, and port lists for both modules match the RTL exactly (including `USE_2_PHASE_CDC` being ignored, the absence of `CMD_DEPTH`/`RSP_DEPTH`/`SYNC_STAGES`, `aclk`/`aresetn` naming, and `STRB_WIDTH = DATA_WIDTH/8`). The `CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH` quote is verbatim-correct. Both `N_FLOP_CROSS(2)` instantiations confirmed. The CG wake-up analysis is accurate: the aclk-domain OR (`cmd_valid || rsp_valid || wakeup_request`) passes a 2-flop synchronizer, then the wrapper `r_wakeup` flop, then the flop inside `amba_clock_gate_ctrl`, then a combinational ICG enable — so "2 register stages; first usable edge 3 ungated pclk cycles" for a PSEL trigger and "about two more" for an aclk trigger both count correctly against the RTL. The "~2–3 destination cycles + 1 source cycle" crossing-latency figure matches the N=2 synchronizer plus the registered `rd_empty` in `fifo_control`. Both code examples use only existing parameters and legal port names and would compile. The ICG/FPGA guidance and the "resets must be synchronized externally" statements are correct.

## Overall

These two pages are unusually careful and mostly accurate — the parameter mechanics, CDC structure, and the clock-gating wake-up analysis all survive line-by-line verification. The serious problem is the reset-behavior narrative: it presents a one-sided reset as a well-understood, mostly-safe operation with a wrong failure mode (dropped command / timeout), when the actual RTL behavior is command re-presentation on one FIFO and stale-response fabrication on the other. Because the same incorrect claim exists as a comment in the RTL itself, the docs faithfully transcribed a design misconception rather than inventing one — but a reader acting on the documented behavior could ship a reset sequence that corrupts APB reads. Second in priority is the DEPTH=6 elaboration failure. The remaining items (parity-error domain labeling, the idle=16 table row) are minor.