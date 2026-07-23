# Review: `apb5` book

I verified every parameter table, port list, packet width, FSM description, parity claim, and clock-gating latency figure in the 9 documents against the RTL in this unit, including the dependencies (`gaxi_skid_buffer`, `gaxi_fifo_async`, `amba_clock_gate_ctrl`, `clock_gate_ctrl`, `cdc_synchronizer`). Packet-width arithmetic was recomputed: master CPW/RPW = 80/42 ✓, master stub 82/44 ✓, slave stub 80/41 ✓ — all correct. Clock-gating wake-up latency (two register stages + combinational ICG enable → first usable gated edge 3 `pclk` cycles) checks out against `amba_clock_gate_ctrl` + `clock_gate_ctrl`. Parity coverage tables match the generate blocks exactly.

## Findings

```
[CONFIRMED] DEPTH=6 is documented as legal for apb5_slave_cdc but fails elaboration
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc.md
  Says:     "| DEPTH | int | 2 | Skid-buffer depth of the wrapped `apb5_slave`; one of {2, 4, 6, 8} |"
  Actually: The module computes `localparam int CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH;` and
            instantiates `gaxi_fifo_async #(.DEPTH(CDC_FIFO_DEPTH), .N_FLOP_CROSS(2))` with
            USE_JOHNSON at its default of 0. gaxi_fifo_async contains an elaboration-time check:
            `if ((USE_JOHNSON == 0) && ((DEPTH & (DEPTH - 1)) != 0)) $error("...Gray requires a
            power-of-2 DEPTH...")`. DEPTH=6 → CDC_FIFO_DEPTH=6 → 6 & 5 ≠ 0 → build fails.
            Only {2, 4, 8} actually work. The same restriction applies to apb5_slave_cdc_cg
            (identical localparam), whose page does not state a legal set but also does not
            warn about it.
  Impact:   A reader who sets DEPTH=6 on either CDC module — a value the doc explicitly lists
            as legal — gets an elaboration error. The base skid-buffer modules genuinely accept 6;
            only the CDC wrappers cannot.
```

```
[CONFIRMED] apb5_master FSM diagram: IDLE note "PSEL=0" is wrong; ACCESS exit conditions omit the response-FIFO-ready term
  File:     docs/markdown/RTLAmba/apb5/apb5_master.md
  Says:     "state IDLE { note right of IDLE : PSEL=0, PENABLE=0 }" and
            "ACCESS --> IDLE : PREADY & cmd_fifo_empty / ACCESS --> SETUP : PREADY & !cmd_fifo_empty"
  Actually: In RTL, the IDLE state drives PSEL high whenever a command is queued:
              IDLE: begin
                  if (r_cmd_valid) begin
                      m_apb_PSEL = 1'b1;
                      w_apb_next_state = SETUP;
            so PSEL=1 during the IDLE cycle (this is also the first of two PSEL-only bus
            cycles — see POSSIBLE RTL BUGS). The ACCESS transitions are additionally gated by
            the response skid buffer:
              if (m_apb_PREADY) begin
                  if (r_rsp_ready) begin ... if (w_cmd_count > 1) SETUP; else IDLE; ...
                  else w_apb_next_state = ACCESS;   // stays in ACCESS despite PREADY
            The doc's transition labels omit the r_rsp_ready condition entirely.
  Impact:   A reader tracing waveforms against the state diagram will see PSEL assert one
            state "early" and will not understand why the master can hold ACCESS with PREADY
            high. Moderate documentation inaccuracy on the page's central FSM figure.
```

```
[CONFIRMED] apb5_master_stub: documented first/last "transaction tracking" is not implemented — markers are a combinational pass-through of the current cmd_data
  File:     docs/markdown/RTLAmba/apb5/apb5_master_stub.md
  Says:     "First/last markers for transaction tracking" and "The first/last bits in packets
            enable: Transaction boundary detection / Burst transaction support / Testbench
            synchronization"
  Actually: RTL unpacks first/last combinationally from the live cmd_data and repacks them
            into rsp_data the same way:
              assign {cmd_last, cmd_first, cmd_pwrite, ...} = cmd_data;
              assign rsp_data = {cmd_last, cmd_first, rsp_pslverr, rsp_pwakeup, ...};
            The wrapped apb5_master FIFOs only {pwrite..pwuser}; first/last are never stored
            with the command. With CMD_DEPTH up to 6, when a response emerges the first/last
            bits belong to whatever command is currently on cmd_data — typically a newer one —
            not the command that produced the response.
  Impact:   Any testbench that relies on rsp first/last to match responses to queued commands
            (exactly the documented use case) reads corrupt markers whenever more than one
            command is in flight. Also listed under POSSIBLE RTL BUGS.
```

```
[CONFIRMED] Minor: stub's wakeup_pending port misdescribed
  File:     docs/markdown/RTLAmba/apb5/apb5_master_stub.md
  Says:     "| wakeup_pending | 1 | Output | Wake-up signal active |"
  Actually: The port is wired straight to apb5_master's wakeup_pending, which is a sticky flag:
            `if (m_apb_PWAKEUP) r_wakeup_pending <= 1'b1; else if (r_apb_state != IDLE)
            r_wakeup_pending <= 1'b0;` — it is not the live PWAKEUP level. apb5_master.md
            documents the same port correctly ("Sticky flag: PWAKEUP was seen...").
  Impact:   Small; a reader might sample it expecting the real-time PWAKEUP state.
```

```
[CONFIRMED] Minor: "CG idle=16" row in the latency table is not representable at the module's default counter width
  File:     docs/markdown/RTLAmba/apb5/apb5_slave_cdc_cg.md
  Says:     "| CG idle=16 | Good | 2 register stages; first usable edge 3 ungated pclk cycles |"
            (parameter table on the same page: "CG_IDLE_COUNT_WIDTH | int | 4 | Width of idle
            counter (max idle = 2^N-1 cycles)")
  Actually: With the default CG_IDLE_COUNT_WIDTH=4, cfg_cg_idle_count is 4 bits and tops out at
            15 (clock_gate_ctrl header: "For IDLE_CNTR_WIDTH=4: max count = 15 clocks"). 16
            requires ICW≥5, which the table does not mention. The sister page apb5_master_cg.md
            explicitly notes the 15-cycle maximum at the default width, so the two pages are
            inconsistent in what they present as a configuration.
  Impact:   Trivial; a reader copying "idle=16" into the default module silently gets 0
            (truncated), i.e. the most aggressive gating, not the least.
```

```
[SUSPECTED] Minor: FSM prose/labels describe capture timing and port names loosely in the two slave pages
  File:     docs/markdown/RTLAmba/apb5/apb5_slave.md and apb5_slave_stub.md
  Says:     apb5_slave.md: "1. SETUP Phase: PSEL=1, PENABLE=0 - Capture address and control"
            apb5_slave_stub.md state diagram: "IDLE --> XFER_DATA : PSEL & PENABLE & cmd_ready"
            and "XFER_DATA --> IDLE : rsp_valid"
  Actually: apb5_slave captures only on the PENABLE rising edge, i.e. the first ACCESS cycle,
            not during SETUP: `if (s_apb_PSEL && s_apb_PENABLE && !r_penable_prev && r_cmd_ready)`
            with the comment "Only capture on rising edge of PENABLE (SETUP->ACCESS transition)".
            In apb5_slave_stub the guards use internal skid-buffer signals `r_cmd_ready`
            (skid wr_ready) and `r_rsp_valid` (skid rd_valid), not the like-named module ports;
            the transition only correlates with the backend cmd_ready port when the skid
            buffer fills.
  Impact:   Low. Waveform-level readers may be confused about which cycle the command is
            captured, and stub users may believe the FSM stalls directly on the backend
            cmd_ready/rsp_valid ports.
```

## POSSIBLE RTL BUGS

1. **Two-cycle SETUP phase on `apb5_master` (SUSPECTED spec deviation).** Because the FSM asserts `m_apb_PSEL=1` while still in IDLE (when `r_cmd_valid`) and then spends a full cycle in SETUP with `PSEL=1, PENABLE=0` before ACCESS, the bus sees PSEL high for two complete cycles before PENABLE rises. AMBA APB defines the SETUP phase as exactly one cycle. This library's own slaves tolerate it (they capture on the PENABLE rising edge), but a strict third-party slave or protocol monitor would flag it.

2. **`apb5_master` hang when the response skid FIFO is full at PREADY (SUSPECTED, by analysis).** In ACCESS, if `m_apb_PREADY && !r_rsp_ready`, the master holds `PSEL=1, PENABLE=1` and stays in ACCESS waiting for PREADY — but the transfer already completed on the slave side. `apb5_slave` returns to IDLE and can only re-capture on a *rising edge* of PENABLE, which never comes (PENABLE is held high), so PREADY never re-asserts: the bus deadlocks with the response FIFO full. Reachable when the backend withholds `rsp_ready` for ≥ `RSP_DEPTH` responses while the master continues issuing commands. With `apb5_slave_stub` as the slave the outcome differs but is also wrong: the stub's IDLE has no rising-edge check (`if (s_apb_PSEL && s_apb_PENABLE && r_cmd_ready)`), so it re-captures and re-executes the *same* command, producing a duplicate transaction. The root cause is the master starting transactions without regard to response-FIFO space.

3. **`apb5_master_stub` first/last not pipelined with the command** — the mechanism behind Finding 3 above; the markers should be carried through the command FIFO alongside `{pwrite..pwuser}` if they are to mean anything.

Also noted but trivial: the RTL comment in `apb5_master` says "Write data parity (odd parity per byte)" while the logic implements even parity (parity bit = XOR reduction, so field+bit has even popcount) — the docs describe the behavior correctly, so only the RTL comment is mislabeled.

## Overall accuracy

This book is in good shape — clearly revised against the RTL after earlier review rounds. The things a reader acts on are overwhelmingly correct: all parameter defaults and legal sets (except DEPTH=6 on the CDC modules), all port lists, the packet bit layouts and recomputed widths, the parity coverage/granularity/qualification tables, the PWAKEUP direction note, the `max(DEPTH,4)` CDC FIFO sizing, the fixed 2-flop synchronization, and the 3-cycle wake-up / `cfg+3` gating-engage latency math. The power-savings table is honestly labeled as an analytical estimate. The confirmed defects are concentrated in three places: the `apb5_master` FSM figure (which also hides a genuine two-cycle-SETUP RTL quirk), the master stub's first/last tracking claim (which the RTL does not implement), and the DEPTH=6 elaboration trap on the CDC variants. Fixing those three, plus the handful of minor port-description items, would make the book accurately reflect the hardware.