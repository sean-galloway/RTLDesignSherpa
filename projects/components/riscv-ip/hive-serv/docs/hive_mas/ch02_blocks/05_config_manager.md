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

- Quiesce status via IDLE register (decided 2026-10-13): an **IDLE signal**
  from the fabric — an aggregated quiescent indication covering the
  participating routers — is routed into a **PeakRDL-managed configuration
  register** for reading by HIVE-C firmware (and the host). Firmware
  verifies IDLE before issuing `SET_ROUTING_MODE`. The register bank
  follows the repo's PeakRDL convention (`rdl/` sources generating regmap,
  decode, and docs, as in `projects/components/legacy-ip/retro_legacy_blocks/rdl/`).
  A hard interlock that refuses the mode update in hardware remains
  optional future hardening, not a Phase-3 gate.
- `DRAIN`: broadcasts prepare, then polls the IDLE register until all
  participating routers report idle. Timeout → error sticky, abort.
- `SWITCH`: emits one PKT_CONFIG broadcast (command 0x0000_0001, payload =
  context id, tile mask = all). The broadcast is a single packet consumed
  by all routers in the same cycle — that simultaneity is what makes the
  switch atomic.
- Injection request path remains **TBD** (owner, 2026-10-13): whether
  PKT_CONFIG broadcasts ride the HIVE-C injection path or a SERV flood.

## Interfaces

AXIL register window (from `hive_c_controller`), PKT_CONFIG injection
request to HIVE-C's CDA/config injection path (the manager does not own an
AXIS master; it borrows the HIVE-C injection path or a SERV flood —
implementation decision in Phase 2), observation bus out.

---

**Last Updated:** 2026-10-13
