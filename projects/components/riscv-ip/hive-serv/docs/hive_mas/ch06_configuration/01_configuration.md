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

# Parameters, Defines, and Filelists

## Hardware Parameters (`includes/hive_config.svh`)

```systemverilog
// System shape
parameter int MESH_SIZE = 4;           // NxN mesh (SERV_COUNT must equal MESH_SIZE^2)
parameter int SERV_COUNT = 16;         // number of SERV monitors
// Delta-shared fabric parameters (must match Delta's configuration)
parameter int ROUTER_BUFFER_DEPTH = 8; // flits per input VC
parameter int NUM_VIRTUAL_CHANNELS = 2;
parameter int FLIT_WIDTH = 128;        // bits
// Configuration manager
parameter int NUM_CONTEXTS = 4;        // routing configurations
// Monitoring
parameter int SERV_MEM_SIZE = 2048;    // bytes per SERV (I + D)
parameter int CONGESTION_THRESHOLD = 6;// trigger at 75% of buffer depth
parameter int STATS_REPORT_INTERVAL = 1000; // cycles
// Performance knobs
parameter bit ENABLE_PIPELINE_BYPASS = 1;
parameter bit ENABLE_ADAPTIVE_ROUTING = 0;  // future: load balancing
```

: Hardware parameter surface

Rules: `SERV_COUNT == MESH_SIZE**2` is a static assertion in `hive_top`.
Delta-shared parameters must be passed down identically to the Delta
instantiation (one config include at system top, not two).

## Software Knobs (`sw/common/hive_config.h`)

```c
#define MAX_INFLIGHT_DESCRIPTORS  8
#define PRIORITY_LEVELS           4
#define AGING_THRESHOLD           1000  // cycles
#define DESCRIPTOR_BATCH_SIZE     4
#define STATS_AGGREGATION_PERIOD  10000 // cycles
```

## Planned Filelist Layout

```
hive-serv/
├── rtl/
│   ├── includes/            # hive_config.svh + packages (above)
│   ├── top/hive_top.sv
│   ├── hive_c_controller/
│   ├── serv_monitor/
│   ├── control_network/
│   ├── config_manager/
│   └── common/
├── dv/
│   ├── testplans/           # arrive with RTL (kestrel testplan convention)
│   └── tests/               # cocotb, one directory per FUB + integration
├── models/                  # SimPy performance models (HAS ch.6 targets)
└── sw/
    ├── hive_c_fw/           # main.c, rapids_mgr.c, ... (HAS ch.5)
    └── serv_fw/             # monitor image (hand-optimized assembly)
```

: Planned repository layout

## Scaling Knobs

`MESH_SIZE`/`SERV_COUNT` scale the PoC (4×4) toward the Kintex-7 8×8
expansion (HAS §7): RTL is generate-based over `SERV_COUNT`, and the
control-network arbiter is a generic N-way. `NUM_CONTEXTS` grows to 8 in
the expansion; `context_memory` sizing derives from it.

---

**Last Updated:** 2026-10-12
