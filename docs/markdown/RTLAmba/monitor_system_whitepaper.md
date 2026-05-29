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

# Monitor System Whitepaper

**Status:** STUB -- outline only, to be filled in
**Target length:** 2-3 pages
**Audience:** SoC integrators who want to deploy the monitor system in a new design
         and need to know which knobs they own and how to spend them.

This is *not* a status snapshot of the current implementation -- for that, see
the per-module docs under `docs/markdown/RTLAmba/shared/` (monbus_axil_group,
arbiter_monbus_common, axi_monitor_base, etc.) and the integration patterns in
`projects/components/bridge/` and `projects/components/stream/`.

This paper instead frames the monitor system as a *design surface*: a fixed
spine (packet format, transport, drain paths) with several explicitly
parameterizable axes that an integrator chooses per deployment. Each section
below names one such axis, describes the *current default*, and sketches the
*tweaks* a designer might make to fit their tracking needs.

---

## 1. Identity space allocation

The 128-bit monbus packet carries five identifiers: PROTOCOL, PKT_TYPE,
EVENT_CODE, UNIT_ID, AGENT_ID, CHANNEL_ID. PROTOCOL / PKT_TYPE / EVENT_CODE
are enums and largely fixed. **UNIT_ID, AGENT_ID, and CHANNEL_ID are the
designer's to allocate.**

### UNIT_ID

- **Current use:** simple two-value scheme inside the bridge generator --
  UNIT_ID=2 for master-side wrappers (axi4_slave_*_mon), UNIT_ID=1 for
  slave-side wrappers (axi4_master_*_mon).
- **Tweak: drop one level.** Instead of allocating UNIT_ID at the interface
  boundary, allocate it inside the unit -- each unit then gets up to 16
  internal sub-busses / sub-blocks it can independently identify, e.g. a
  scheduler with multiple internal pipelines, or an engine with separate
  source / sink / completion paths. The cost is that "which interface did
  this come from" now has to be encoded in AGENT_ID instead.
- **Tweak: hierarchical.** Top bits encode subsystem (bridge/stream/rapids),
  bottom bits encode position within that subsystem. Works when the on-chip
  monbus is aggregated at multiple levels.

### AGENT_ID

- **Current use:** `(port_idx << 4) | chan_bit` inside the bridge generator,
  where chan_bit selects write (1) vs. read (0). 8 bits total = up to 16
  ports x 2 channels.
- **Tweak: per-port subagents.** When a port hosts multiple logical agents
  (e.g. a master that splits into descr / sink / source streams), use the
  upper nibble for port_idx and the lower nibble for subagent. Today the
  bridge generator only consumes 5 of the 8 bits; the other 3 are free for
  designer use.

### CHANNEL_ID

- **Current use:** mostly 0 -- not yet exploited.
- **Tweak:** carry per-burst metadata that's useful for offline analysis,
  e.g. ARID/AWID echo for OOO debug, or a virtual-channel id for QoS work.

---

## 2. Where to insert monitoring

- **Current default:** per-port wrappers at every bridge-top boundary. Catches
  protocol-level errors (SLVERR / DECERR / orphan / timeout) and aggregates
  on the monbus_arbiter inside the bridge.
- **Tweak: mid-fabric.** Add monitor wrappers on internal converter
  boundaries when you need to localize where a violation entered the
  fabric -- the bridge generator already supports the necessary axi4_*_mon
  variants; it just doesn't auto-instantiate them on internal boundaries.
- **Tweak: root of tree.** Skip per-port monitors entirely and place a
  single monitor at the SoC's NoC root if the integrator cares only about
  aggregate behavior. Trades resolution for area.

---

## 3. Timestamp policy

- **Current default:** monbus_axil_group runs a free-running 64-bit
  counter and stamps each captured record with its own arrival time.
  Records are always 3 beats: `[pkt[63:0], pkt[127:64], ts[63:0]]`. The
  endpoints (parser, host scripts) do not care where the timestamp
  originated -- they treat it as an opaque ordering key.
- **Tweak: hybrid global + local.** A future direction is for the SoC to
  distribute a single global microsecond counter to every monitor wrapper,
  while each wrapper additionally keeps a higher-resolution local
  cycle counter. The 64-bit ts field then splits, e.g.
  `{global_us[47:0], local_cyc[15:0]}`, giving cross-subsystem
  correlation (global) and per-wrapper resolution (local) in the same
  field width. The transport layer stays unchanged.
- **Tweak: external time source.** Some deployments want PTP / IEEE-1588
  time. Replace the group's internal counter with a synchronizer onto
  an external time bus; record layout stays 3 beats.

---

## 4. Drain path selection

- **Current default:** monbus_axil_group exposes two drain paths --
  - `s_mon_axil_*` (slave AXIL): IRQ-driven, slice-counter read, intended
    for CPU consumption.
  - `m_mon_axil_*` (master AXIL): bulk-trace writes to a memory region,
    intended for post-mortem capture (e.g. stream_char's debug_sram).
  Per-packet-type routing is controlled by `cfg_*_err_select`.
- **Tweak: hybrid.** Route PktTypeError + PktTypeTimeout to the IRQ path
  (mix, not flood), everything else to the bulk path. This is what
  stream_char's smoke tests already exercise.
- **Tweak: drop one path.** A deployment that only wants forensic capture
  can tie off `s_mon_axil_*` and let everything flow through the
  bulk-trace path; conversely a deployment that only cares about
  real-time alerts can tie off `m_mon_axil_*`. The group's filter logic
  cleanly handles either configuration.

---

## 5. Packet-type filtering

- **Current default:** all per-port and group masks default to 0 (= no
  drop, no mask). Integrators selectively raise bits to suppress noise.
- **Pitfall:** enabling completion + performance packet types
  simultaneously overwhelms the bus. See
  `docs/AXI_Monitor_Configuration_Guide.md`.
- **Tweak:** profile-driven masks -- expose `pkt_mask` / `err_select` as
  CSRs on a control APB, let firmware reconfigure at runtime depending
  on whether the system is in functional-verify mode, perf-tuning mode,
  or production-quiet mode.

---

## 6. Aggregation topology

- **Current default:** a tree of `monbus_arbiter` instances merges
  per-wrapper streams into the bridge-level monbus_axil_group input.
  Arbiter policy is round-robin with grant locking on the multi-beat
  packets.
- **Tweak: weighted.** Replace the standard arbiter with the WRR
  variant (`arbiter_wrr_pwm_monbus`) when one wrapper is known to be
  much higher-volume than others (e.g. a 512b sink path vs. a 32b
  config-CPU read path) and the integrator wants to bound starvation
  on the low-volume side.
- **Tweak: protocol partitioning.** Use separate monbus_axil_group
  instances per protocol family (one for AXI, one for AXIS) when the
  group's filter masks aren't enough -- e.g. when each protocol has its
  own consumer FIFO budget. The bridge generator already supports the
  monbus_axis_group sibling.

---

## TODO (writing-up checklist)

- [ ] Pull representative numbers from a real deployment (stream_char on
      Nexys A7) for the perf section -- packets / sec on bulk path,
      IRQ-rate on err path, etc.
- [ ] Add one block diagram per section showing the as-built and the
      tweaked configuration side-by-side.
- [ ] Cross-link each section to the relevant per-module spec under
      `docs/markdown/RTLAmba/shared/`.
- [ ] Expand the timestamp section into its own appendix once the
      hybrid-global scheme is prototyped.
- [ ] Add a section on test/verification considerations -- e.g. the
      slave-BFM SLVERR-injection pattern used by
      `test_bridge_1x2_rd_monitor_error_inject.py` -- so integrators
      know how to validate their tweaks in simulation.

---

**Maintained By:** RTL Design Sherpa Project
**Review Frequency:** As architectural decisions evolve
