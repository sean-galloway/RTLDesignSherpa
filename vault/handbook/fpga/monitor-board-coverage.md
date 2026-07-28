---
title: Monitor board coverage
summary: See every packet type from every agent on silicon via a config-defined dense tally; rate-match, don't hammer.
---

# Monitor message coverage on the board

Goal of the STREAM monitor-validation environment: not throughput hammering but
**seeing every monbus message type emitted by every agent**, with producer and
drain rates matched (we can always emit faster than the drain empties). The
[[uart-harness]] reads the monitor tally SRAMs over AXIL/UART; the monitor group
writes its own SRAM.

## The counting problem the tally must solve

A monbus message identity is `{protocol[3:0], pkt_type[3:0], event_code[7:0]}`
plus `agent_id[15:0]`. A direct-mapped count matrix over the full grid is
hopeless: `pkt_type(16) x event_code(256) x protocol(5) = 20480` cells, of which
only ~245 tuples are ever legal (~1.2 percent dense - AXI 75, ARB 64, AXIS 52,
APB 42, CORE ~12). Crossing that with `agent_id` (16 bits) to prove "every agent
fired" would be ~99 percent empty.

## Design: config-defined dense tally (profile mode)

`monbus_pkt_tally` gains a **profile / dense-index mode**:
- **Per-unit legal-message profiles** (params, CSR-overridable): bind each agent
  to the tuples it may legally emit - `AXI_MON_PROFILE` (the 75 AXI tuples) for
  the datapath/desc-AXI monitors, `CORE_SCHED_PROFILE` / `CORE_DESC_PROFILE` for
  the schedulers / descriptor engines.
- **Sparse identity -> dense index via the tally's `monbus_cam`**: the legal
  `{agent, protocol, pkt_type, event_code}` tuples load into the CAM; the payload
  is a dense bin index. Count SRAM depth = number of legal tuples (STREAM ~= 290
  bins ~= 1 KB, vs a 256 KB direct map). Dense, and it carries agent + protocol +
  full event with no aliasing.
- **UNEXPECTED catch-all bin**: any packet whose tuple is not in a unit's profile
  increments a global bin (+ first-event latch). The sparsity removed becomes a
  spec-violation detector: an out-of-profile message (wrong event code, untracked
  agent, a protocol a unit should not speak) is a first-class signal.
- **Runtime reprogram**: if a build's legal set overflows BRAM, CSR-load a slice
  of units per run, sweep, reprogram for the next slice - fits the
  run-scenarios-in-sequence model.

Contract: the Python `parse()` coverage matrix uses the same profile->index map,
so hardware counts match `parse()` exactly (the silicon twin, see [[coverage]]).

## Coverage oracle: protocol + agent, not just type

Because the count matrix folds `agent_id` out unless profile mode is on, the
verification asserts on `(protocol, agent_id, pkt_type, event_code)` tuples. In
sim, decode probed `mon_valid` through `parse()` (agent-resolved, free); on the
board, sweep the dense tally. A final **all-agents-hit gate**: every agent in the
roster shows a nonzero bin and `UNEXPECTED == 0`.

STREAM agent roster (8 channels; there is no channel-count boundary - the old
8-channel engine wedge was fixed): desc-AXI monitor **8**, rd datapath **9**, wr
datapath **10**, descriptor engines **16-23**, schedulers **48-55**. Test-slave
monitors live in a reserved band **below** STREAM (`0x0001`/`0x0002`) so a
combined stream+slave analysis keys unambiguously by agent id - keep them there.

## Scenario sequence (run after bring-up)

Each scenario is self-contained: **program CSRs -> tiny DMA -> FREEZE_TRACE ->
sweep -> assert tuple set -> clear**. Bring-up (ping + desc_ram round-trip) runs
once. A table-driven runner (`SCENARIOS = [{name, mon_cfg_writes, workload,
expected_tuples}]`) makes 8->32 scenarios just a list length. Phases: completion
(scheduler CORE, desc-engine CORE, datapath AXI, slave-side), AddrMatch (rd/wr
DEBUG ranges), Error (allowlist-miss `AXI_ERR_ADDR_RANGE`, CORE descriptor
error), timing classes (timeout / threshold via `axi_response_delay`, perf),
perf-window / histogram / debug, and a full-agent sweep (all 8 channels) as the
all-agents-hit gate. Stimulus knobs: generalize the post-reset CSR list
(`addr_range_writes` -> `mon_cfg_writes`) to program any class enable/threshold;
a runtime slave-delay CSR feeds `axi_response_delay` for timeout/threshold.

Prereq (landed): stream_core aggregates the rd/wr datapath monitors onto
`mon_valid` via a 3-client `monbus_arbiter` (they were tied off), so datapath
AddrMatch/Error/Perf reach the tally at all. Utilization/rate methodology:
`DMA_UTILIZATION_MEASUREMENT.md` (four-bucket bus meter). Registers by name:
[[registers-by-name]].
