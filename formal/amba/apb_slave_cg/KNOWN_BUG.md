# Suspected Bug: apb_slave_cg Wakeup Latency

## Summary

The `apb_slave_cg` module may gate the clock mid-transaction under specific
conditions because the wakeup signal path has **2 cycles of register delay**
before the clock gate ungates.

## The Path

1. `apb_slave_cg.r_wakeup` is a flop clocked by the ungated `pclk`:
   ```
   r_wakeup <= s_apb_PSEL || s_apb_PENABLE || cmd_valid || rsp_valid;
   ```
2. This drives `amba_clock_gate_ctrl.user_valid`, which is then flopped again
   inside `amba_clock_gate_ctrl`:
   ```
   r_wakeup <= user_valid || axi_valid;
   ```
3. Only *then* does the wakeup reach `clock_gate_ctrl.wakeup`, which reloads
   the idle counter and ungates the clock.

## The Race

Scenario with `cfg_cg_idle_count = 0` and clock currently gated:
- Cycle 0: gated, `s_apb_PSEL` asserts on the bus
- Cycle 1: `apb_slave_cg.r_wakeup` goes high (one flop delay)
- Cycle 2: `amba_clock_gate_ctrl.r_wakeup` goes high (second flop delay)
- Cycle 3: `clock_gate_ctrl` ungates the clock

This means PSEL is held for **3 cycles** before the underlying apb_slave sees
its clock edge. With a compliant APB master this is fine (PSEL is held until
PREADY), but:

1. **Assertions of the form "no gating during any cycle where PSEL was seen
   in the recent past" fail** -- because gating can persist for 1-2 cycles
   after PSEL first asserts.
2. **If `cfg_cg_idle_count = 0`** the countdown is so aggressive that gating
   re-engages as soon as `r_wakeup` flickers, and the 2-stage latency becomes
   visible in BMC within 5-6 cycles.

## Is This A Functional Bug?

Not strictly -- APB's `PREADY` wait-state semantics allow arbitrary latency
from PSEL to PREADY. The master will hold PSEL until PREADY is asserted, and
the gated slave will eventually wake up.

However, it is a **correctness hazard** because:
- It violates the intuitive property "clock is running during any bus activity"
- It exposes the design to regressions if anyone adds logic that depends on
  the clock being live immediately when PSEL rises
- The two-flop wakeup path should be collapsed to a single flop or made
  combinational in the gating controller

## Recommended Fix

Option A: Drive `amba_clock_gate_ctrl.user_valid` directly from the
combinational OR (skip the local `r_wakeup` flop):
```systemverilog
// Remove local r_wakeup register, use combinational OR
wire w_wakeup = s_apb_PSEL || s_apb_PENABLE || cmd_valid || rsp_valid;
```

Option B: Inside `amba_clock_gate_ctrl`, drive `clock_gate_ctrl.wakeup`
directly from `(user_valid || axi_valid)` rather than from the registered
`r_wakeup`.

## Formal Proof Handling

The formal wrapper `formal_apb_slave_cg.sv` omits the strict
"no gating during PSEL" property and instead verifies:
- Reset clears `s_apb_PREADY` and `apb_clock_gating`
- `s_apb_PREADY` is single-cycle pulse (APB slave FSM invariant)
- `cfg_cg_enable=0` implies no gating
- Cover points demonstrate gating + transactions can coexist

The relaxed property `ap_no_gate_inflight` is preserved as a cover point
(`cp_no_gate_when_psel`) rather than an assertion.
