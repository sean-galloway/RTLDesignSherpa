# HIVE Testplans

Phase-1 unit testplans for the HIVE control plane, per the house rule:
**testplans before RTL** — coverage is meaningless without them. Scenarios
map to `dv/tests/test_*.py` cocotb tests and to the hive HAS/MAS v0.2
contracts. Status lifecycle: `planned` -> `verified` (with measured line
coverage backfilled, kestrel convention).

| Testplan | Scope | Block |
|---|---|---|
| [hive_c_loader](hive_c_loader_testplan.yaml) | VexRiscv wrapper, tightly-coupled memories, kestrel-pattern loader | 1 |
| [hive_descriptor_gen](hive_descriptor_gen_testplan.yaml) | Mailbox → 256-bit CDA descriptor assembly, ordering, stall | 1 |
| [hive_axis_cda_master](hive_axis_cda_master_testplan.yaml) | CDA AXIS injection protocol (tuser/tdest/tlast, handshake) | 1 |
| [hive_serv_monitor](hive_serv_monitor_testplan.yaml) | Router taps, counters, trigger logic, packet injector | 2 |
| [hive_ctrl_network](hive_ctrl_network_testplan.yaml) | AXIS-shaped 32-bit control frames, star fan-out, arbitration | 3 |

Phases 2-3 plans (control network at 16 slaves, config_manager context
switching, delta seam, full integration) are written when those blocks are
scheduled; the config_manager plan in particular lands **after** the owner
decides the open PKT_CONFIG injection-path item (MAS §2.5).

Levels follow the repo grid: gate (smoke), func (feature-complete), full
(exhaustive / corner + random), plus the regression level wrapper
(TEST_COUNT seeds) from make/tests.mk.
