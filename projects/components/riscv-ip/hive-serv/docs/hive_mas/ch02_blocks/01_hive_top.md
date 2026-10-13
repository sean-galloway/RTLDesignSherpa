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

# hive_top

Top-level integration of the four blocks. `hive_top` owns the external port
list (HAS Chapter 4), the parameter surface (Chapter 6 of this book), and
the instantiation of everything below. It contains no logic of its own
beyond parameter propagation and the reset staging tree.

## Composition

| Instance | Module | Count | Role |
|----------|--------|-------|------|
| `u_hive_c` | `hive_c_controller` | 1 | Master controller (Block 1) |
| `u_serv[k]` | `serv_monitor` | `SERV_COUNT` (16) | Per-tile monitors (Block 2) |
| `u_ctrl_net` | `control_network` | 1 | HIVE-C ↔ SERV star (Block 3) |
| `u_cfg_mgr` | `config_manager` | 1 | Contexts and switching (Block 4) |

: Subordinate instances

## Structural Rules

- `hive_top` does not create clocks; it takes the four domain clocks and
  `system_rst_n` from the system top (PLL/BUFG decisions live there).
- Every CDC FIFO listed in §1.2 is instantiated in the *sending* block and
  documented in that block's interface section; `hive_top` only routes the
  clock/reset pairs to them.
- The Delta-facing AXIS ports of `hive_c_controller` and each
  `serv_monitor` cross into `delta_clk` inside the sender, so `hive_top`
  presents only `delta_clk`-domain AXIS toward Delta — Delta never sees a
  foreign clock.
- All monitor observation ports (Ocelus tap-outs, per Chapter 5) are
  exported up through `hive_top` as a flat observability bus so system
  integration can attach the monitor system without touching block
  internals.

---

**Last Updated:** 2026-10-12
