# RLB — Open (accepted, not started)

---

### RLB-014: the 800-line core cap is honored in the breach

**Priority:** P3. Hygiene and reviewability, not a defect — every block is
green. Raised 2026-09-14 by the uart_16550 verification agent and confirmed
by measurement.
**Status:** open, and it is a POLICY question for the owner, not a fix an
agent should take unilaterally.

Measured `wc -l` on the nine RLB cores:

```
1706  rtc/rtc_core.sv
1328  pm_acpi/pm_acpi_core.sv
 888  smbus/smbus_core.sv
 842  uart_16550/uart_16550_core.sv     <- 759 before the RLB-013 features
 705  hpet/hpet_core.sv
 666  pic_8259/pic_8259_core.sv
 552  ioapic/ioapic_core.sv
 331  pit_8254/pit_core.sv
 227  gpio/gpio_core.sv
```

Four are over the repo's 800-line guidance. smbus is the pointed one: it was
held to exactly 800 during the #58 review and has since grown to 888.

**The obvious cut in uart is blocked by DV.** The tests whitebox
`r_tx_state`, `r_tx_wr_ptr`, `r_tx_rd_ptr`, `w_tx_fifo_count`, `w_tx_bit` and
the RX equivalents at `u_uart_core` scope, so extracting TX or RX breaks tests
that an RTL agent may not edit. That constraint is why round 2 split modem and
intr instead, and the sweep confirmed that split was DV-safe (zero references
into `u_intr` or `u_modem`). Any split here is a DV change first and an RTL
change second.

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
