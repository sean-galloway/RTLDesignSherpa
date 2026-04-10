# Suspected Bug: apb5_slave_cg Wakeup Latency

## Summary

Same issue as `apb_slave_cg` -- the wakeup path has 2 cycles of register
delay before `amba_clock_gate_ctrl` ungates the clock:

```
apb5_slave_cg.r_wakeup (flop)  ->
amba_clock_gate_ctrl.r_wakeup (flop)  ->
clock_gate_ctrl.wakeup (comb)
```

With aggressive `cfg_cg_idle_count=0` settings, this 2-cycle latency means
the clock can remain gated for 1-2 cycles after the master asserts PSEL on
the bus. APB wait states hide this from the master, but it violates the
intuitive "no gating during bus activity" property.

See `formal/amba/apb_slave_cg/KNOWN_BUG.md` for full details and recommended
fix (collapse the two wakeup registers).
