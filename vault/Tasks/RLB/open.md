# RLB — Open (accepted, not started)

---

### RLB-016: an unmapped APB address hangs the RLB bus

**Priority:** P2. Not a defect in any block -- it is the subsystem's response
to an address nobody implements, and today that response is "never answer".
**Status:** open, found 2026-09-14 while building the rlb_top smoke tests.

`apbx_xbar_rlb_1to10` drives `m_cmd_ready` only inside
`if (m_cmd_valid && addr_in_range)`, where

    addr_in_range = (paddr >= BASE_ADDR) && (paddr < BASE_ADDR + 32'h0000A000)

so an access outside the 40KB window is never accepted. `apb4_slave` leaves
IDLE only `if (... && r_cmd_ready)` and asserts `s_apb_PREADY` only in BUSY on
`r_rsp_valid`, so PREADY never asserts and the transfer never completes. There
is no timeout anywhere in that path.

The response-mux default DOES have `m_rsp_pslverr = 1'b1` for an invalid
select, but it cannot fire: `r_slave_sel` only updates on an ACCEPTED command,
and an out-of-range command is never accepted. The error path is unreachable
for the case it was written for.

Contrast the RESERVED window (slave 9), which is correct: rlb_top ties it to
`PRDATA=0xDEADBEEF, PSLVERR=1, PREADY=1`, so a reserved access is reported
rather than hanging. That is the behaviour an out-of-range access should have.

NOT COVERED BY A TEST, deliberately. The APB master BFM's completion loop is
unbounded, so probing an unmapped address would hang until the cocotb timeout
killed the whole test, and hand-driving the bus to dodge that would break the
"always use the BFMs" rule. `rlb_top_tests.py` documents the omission.

Fix shape, when someone wants it: give the crossbar a default responder for
`!addr_in_range` that accepts the command and answers with PSLVERR, exactly as
the reserved window already does.
