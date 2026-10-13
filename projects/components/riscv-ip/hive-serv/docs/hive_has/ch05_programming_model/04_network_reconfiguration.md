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

# Network Reconfiguration Workflow

Network topology switching is HIVE-C firmware driving the Configuration
Manager hardware through a fixed three-command protocol. The sequence is
identical every time; only the context ID changes.

## Atomic Switch Protocol

```
1. HIVE-C issues CONFIG_PREPARE
   - Target tiles flush in-flight packets
   - Routers enter quiescent state (5-10 cycles)

2. HIVE-C broadcasts SET_ROUTING_MODE (PKT_CONFIG, command 0x0000_0001)
   - Target tile mask = all participating tiles
   - Payload = context ID (0-3)
   - All tiles simultaneously update MODE_SELECT

3. HIVE-C issues CONFIG_ACTIVATE
   - Tiles resume operation under the new routing
```

Total latency 10-20 cycles, deterministic; budget < 25 cycles including
quiesce. Overhead target < 1% for workloads whose phases run 1000+ cycles.

## Worked Flow: Mesh to Tree Reduction

1. Host command (or scheduler policy): "switch to tree reduction mode"
2. HIVE-C broadcasts `CONFIG_PREPARE` over the control network; SERV
   monitors quiesce their local injection
3. Routers drain in-flight packets (5-10 cycles; SERV taps confirm
   occupancy at zero via the STATUS registers)
4. HIVE-C broadcasts `SET_ROUTING_MODE`, payload = context 2, tile mask =
   all 16 tiles — one PKT_CONFIG packet updates every router in the same
   cycle
5. HIVE-C issues `CONFIG_ACTIVATE`; the network resumes with the E-W
   reduction tree active

## Safety Rules

- **Never switch without quiesce.** A `SET_ROUTING_MODE` issued while
  packets are in flight is a protocol violation; the Configuration Manager
  does not hardware-enforce the drain, so firmware must verify the fabric
  IDLE status register (below) before step 2. A hardware interlock is
  optional future hardening (MAS §2.5).
- **Context 3 tables must be loaded before activation.** Custom routing
  entries are written via `Update Router Table Entry` (0x0000_0002) packets
  while the router is quiescent.
- **Rollback:** on `CONFIG_ACTIVATE` failure (tile error flags), firmware
  re-runs the sequence back to the previous context; there is no partial
  commit by construction (single-cycle mode register update).

---

**Last Updated:** 2026-10-13
