<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# The Context Switch Sequence, Cycle by Cycle

The config_manager FSM (§2.5) driven by HIVE-C firmware. Typical budget:
10-20 cycles; never more than 25.

```
Cycle  Action
  1    switch_controller receives CONFIG_PREPARE (AXIL write from firmware).
  2    Prepare broadcast issued on the control network; SERVs stop local
       injection and (if in data path) assert quiesce request to routers.
 3-8   Drain: routers flush in-flight packets (5-10 cycles). switch_controller
       polls STATUS.active_packets for all participating tiles.
  9    All-zero confirmed (or hardware interlock satisfied — see §2.5 open item).
 10    SET_ROUTING_MODE PKT_CONFIG assembled (payload = context id,
       tile mask = all); injected on the HIVE-C config path.
 11    Broadcast consumed by every router in the same cycle (atomic point:
       MODE_SELECT registers update simultaneously).
 12    config_registers.switch_status = ACTIVE_CONTEXT.
 13    CONFIG_ACTIVATE broadcast; routers resume under the new routing.
14-20  Margin for slower drain; beyond 25 cycles the FSM raises
       switch-timeout sticky error and requires firmware rollback (HAS §5.4).
```

**Why the atomic point works:** every router updates `MODE_SELECT` on the
same broadcast beat. There is no skew window in which different routers
hold different contexts — the switch is a single point in time (cycle 11
above), not an interval. This is the property the formal inventory asserts
as "context switch atomicity."

**Quiesce verification:** the FSM and firmware read the aggregated IDLE
signal through the PeakRDL config register (§2.5) — all participating
routers report idle before `SET_ROUTING_MODE` issues. The check is a
readable status, not a hardware refusal: correct switching is firmware
discipline, with a hard interlock left as optional future hardening.

---

**Last Updated:** 2026-10-13
