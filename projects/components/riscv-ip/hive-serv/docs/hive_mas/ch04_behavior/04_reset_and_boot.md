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

# Reset and Boot Behavior

From `system_rst_n` release to a supervising HIVE system.

```
Phase  Action
  A    Staged deassertion (§1.3): host → HIVE-C → Delta → SERVs.
  B    HIVE-C fetches first instructions; firmware init: AXIL windows,
       interrupt enables, injection queue clear.
  C    Firmware loads Context 0 default (systolic) into the config space;
       config_manager reports ACTIVE_CONTEXT = 0.
  D    SERVs release, run monitor firmware init, begin tap sampling and
       periodic reporting.
  E    System-ready after ~100 cycles of the slowest clock (serv_clk).
       host_if accepts commands; CDA injection enabled.
```

**Boot invariants:**
- No CDA packet may enter Delta before phase C completes (injection queue
  held in reset-clear until firmware enables it — a formal-friendly
  one-bit condition).
- Routers must be in Context 0 from first ingress; a router that sees a
  packet while `MODE_SELECT` is undefined raises `ERROR_FLAGS` (protocol
  violation path, HAS §4.2).
- SERVs that have not finished init must not block the control network
  uplink (their arbiter slot is granted and frames are simply empty/NAK —
  fairness holds even during boot).

**Soft-reset behavior** mirrors the staged sequence for the affected
domain only; a SERV soft reset is invisible to Delta traffic (its tap is
passive), and a Delta soft reset drains through the config_manager quiesce
path rather than raw reset assertion wherever in-flight packets exist.

---

**Last Updated:** 2026-10-12
