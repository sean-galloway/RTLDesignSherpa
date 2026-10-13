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

# config_manager (Block 4)

Owns the four virtual routing contexts and the atomic-switch orchestration.
Lives in `hive_c_clk` with a `delta_clk` register interface; the PKT_CONFIG
broadcast path carries context changes to the routers.

```
config_manager
├── config_registers.sv     # Mode select, status, soft-reset, error sticky
├── context_memory.sv       # 4 contexts × per-tile routing tables (BRAM)
└── switch_controller.sv    # PREPARE / SET_ROUTING_MODE / ACTIVATE FSM
```

: Config manager module tree

## Submodules

**`context_memory`.** Four contexts × 16 tiles × routing-table entry
(BRAM; 2 BRAM blocks in the budget). Contexts 0-2 hold hardwired-mode
metadata only (the routing functions are hardwired in Delta's routers);
Context 3 holds full per-tile tables via `ROUTE_TABLE_n` writes. Reset
default: Context 0 loaded/selected.

**`config_registers`.** The HIVE-side configuration space (HAS §4.3):
active context, per-context valid bits, switch-status RO bits, error
sticky flags, soft-reset outputs. Exposed to HIVE-C firmware over the AXIL
window and to the observation bus.

**`switch_controller`.** The three-phase FSM (HAS §5.4):

```
IDLE ──CONFIG_PREPARE──► DRAIN ──quiesce_confirmed──► SWITCH
                                                        │ SET_ROUTING_MODE broadcast
                                                        ▼
                                              ACTIVE ◄── CONFIG_ACTIVATE
```

- `DRAIN`: broadcasts prepare, then polls router `STATUS` registers
  (or receives SERV tap confirmation) until all participating routers
  report `active_packets == 0`. Timeout → error sticky, abort.
- `SWITCH`: emits one PKT_CONFIG broadcast (command 0x0000_0001, payload =
  context id, tile mask = all). The broadcast is a single packet consumed
  by all routers in the same cycle — that simultaneity is what makes the
  switch atomic.
- Hardware interlock (open item): the HAS requires firmware to verify
  quiesce before `SET_ROUTING_MODE`; a hardware interlock in
  `switch_controller` that refuses the mode update until
  `active_packets == 0` everywhere is the preferred hardening and should be
  added before Phase 3 bring-up.

## Interfaces

AXIL register window (from `hive_c_controller`), PKT_CONFIG injection
request to HIVE-C's CDA/config injection path (the manager does not own an
AXIS master; it borrows the HIVE-C injection path or a SERV flood —
implementation decision in Phase 2), observation bus out.

---

**Last Updated:** 2026-10-12
