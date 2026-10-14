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

# l1_control: Blocking Pipeline FSM

**Module:** `l1_control.sv`
**Location:** `projects/components/cache-ip/common-ip/rtl/fub/`
**Status:** Landed (Task 3: CPU path; Task 4: snoop-during-fill service +
pending-fill bypass leaf); scored against the Task 2 gem5-derived oracle at
gate/func/full, geometries s16w2 + s128w4

---

## Overview

`l1_control` is the cache's only state machine. It owns the blocking pipeline, the tag-array port-A schedule, the pending-fill bypass register, victim-way selection, and the handshakes to `l1_fill`, `l1_drain`, `l1_victim`, and `l1_snoop_resp`. Because the cache is blocking, there is exactly one CPU transaction in flight at any time; snoops are serviced concurrently on tag-array port B.

---

## State Encoding

`l1_pkg` defines a 3-bit cache-line state field for `M`, `E`, `S`, `I`. One extra code is reserved for a future MOESI `O` state; the control FSM v1.0 implements only MESI.

```systemverilog
typedef enum logic [2:0] {
    STATE_I = 3'b000,  // Invalid
    STATE_S = 3'b001,  // Shared
    STATE_E = 3'b010,  // Exclusive
    STATE_M = 3'b011,  // Modified
    STATE_O = 3'b100,  // Reserved for future MOESI Owned state
    // 3'b101, 3'b110, 3'b111 reserved
} cache_state_t;
```

The 3-bit width is intentional: it gives one reserved code for `O` and three spare codes for future transient/stable elaborations without widening the tag store.

### FSM states inside l1_control

The FSM itself is one-hot encoded. Stable states are the ones that can persist between CPU requests; transient states exist only while a miss or snoop is in progress, mirroring the gem5 Ruby `MESI_Two_Level-L1cache.sm` philosophy that every in-flight condition is an explicit enumerated state.

| State | Type | Meaning |
|-------|------|---------|
| `CTRL_IDLE` | stable | Waiting for a CPU request from `l1_cpu_frontend`. |
| `CTRL_LOOKUP` | transient | Tag/state lookup on port A; hit/miss decision. |
| `CTRL_HIT_RD` | transient | Read hit: fetch data from `l1_data_array` port A, return response. |
| `CTRL_HIT_WR` | transient | Write hit: update data, promote to M, return response. |
| `CTRL_MISS_VICTIM` | transient | Miss: ask `l1_repl` for victim way; read victim state. |
| `CTRL_MISS_DRAIN` | transient | Victim is dirty: stage it in `l1_victim`, launch `l1_drain`. |
| `CTRL_MISS_FILL` | transient | Launch `l1_fill`, wait for RLAST. |
| `CTRL_FILL_WRITE` | transient | Write fill data into `l1_data_array` port A; install tag + state. |
| `CTRL_REPLAY` | transient | Re-present original request from front-end latch; it now hits. |
| `CTRL_SNOOP` | transient | Service a snoop on port B (can preempt / interleave with miss states). |
| `CTRL_ERROR` | stable | Sticky fatal error; cleared only by reset. |

The FSM is not a minimal two-state controller; the explicit transient states are the formal proof surface. Each state asserts exactly the control signals that are legal for that state, and illegal states default to `CTRL_ERROR`.

---

## Pipeline Staging

The HAS deferred pipeline staging to the MAS. This section fixes it.

### Stage 0: Request latch

`l1_cpu_frontend` accepts a GAXI request and holds `{addr, we, be, wdata}` in a register. `l1_control` sees a single `req_valid` pulse and the latched request fields. The front end does not accept a new request until `req_ready` is returned.

### Stage 1: Tag lookup (`CTRL_LOOKUP`)

On the cycle after request acceptance, `l1_control` drives `ctrl_tag_a_set`; the tag array returns per-way `{tag, state}` combinationally on `ctrl_tag_a_tag_state`. The lookup also selects the victim way from `l1_repl` combinatorially so that the victim is known on the same cycle the hit/miss decision is made.

### Stage 2: Hit or miss decision

- **Hit:** transition to `CTRL_HIT_RD` or `CTRL_HIT_WR`. The data array is accessed in the same cycle as the state check (the set/way was already decoded from the lookup).
- **Miss:** transition to `CTRL_MISS_VICTIM`.

### Stage 3: Miss handling

1. `CTRL_MISS_VICTIM`: read the victim tag/state from the tag array and, if dirty, copy the victim line data from `l1_data_array` port A into `l1_victim`.
2. `CTRL_MISS_DRAIN`: if the victim is M, launch `l1_drain` with the address and data from `l1_victim`. Wait for the drain-done handshake.
3. `CTRL_MISS_FILL`: launch `l1_fill` with the missing line address. The pending-fill bypass register is loaded now.
4. `CTRL_FILL_WRITE`: on `fill_done`, write the fill data into `l1_data_array` port A and install the tag + new state in `l1_tag_array` port A.
5. `CTRL_REPLAY`: re-assert `req_valid` to the hit path using the original latched request; the next cycle is `CTRL_LOOKUP` again and the line is present.

### Snoop interleaving

`l1_control` resolves CPU-vs-snoop contention with snoop priority. A pending snoop can cause the CPU pipeline to stall for one cycle at safe boundaries (after a tag-array access completes, never mid-burst). The snoop path uses `tag_b_*` and `data_b_*` ports exclusively; it never needs port A except when a snoop triggers an invalidation or downgrade, which is applied on the next available port-A cycle.

Landed behavior (Task 4): the grant is restricted to safe waiting states —
`CTRL_IDLE`, `CTRL_MISS_FILL` (once the bypass is armed, or while an
upgrade waits on its acknowledge), and `CTRL_MISS_DRAIN` — so the pipeline
stalls exactly one cycle at the boundary plus the CD transfer time. The
response reference state resolves as: pending-fill bypass match (answered
at the post-fill `pf_state`, CD beats sourced from the fill way and gated
per-beat by `pf_data_valid`, stalled until the beat arrives) > the stale
victim entry during a fill (no transfer — the writeback already completed,
gem5 `M_I × WB_Ack → I`) > the port-B tag hit (installed state; a dirty
victim still draining is served at M from the staged copy, `SINK_WB_ACK`).
An invalidating/downgrading snoop on the pending line is remembered
(`pend_vld`/`pend_state`, invalidation-sticks) and applied at fill commit;
on an installed line it is written on port A inside the service. CR
presentation after CDLAST is `l1_snoop_resp`'s contract, not control's.

---

## Key Control Signals

Landed port names (the table is checked against `l1_control.sv`). Read
data (tag/state, hit read data) is combinational on the landed arrays, so
the port-A schedule is address + write strobe, no read enable.

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `ctrl_tag_a_set` | to `l1_tag_array` | Port A lookup set index. |
| `ctrl_tag_a_tag_state` | from `l1_tag_array` | Per-way `{tag, state}` lookup result. |
| `ctrl_tag_a_wr_en` | to `l1_tag_array` | Port A write enable (init walk / install / promotion). |
| `ctrl_tag_a_wr_tag_state` | to `l1_tag_array` | Port A write data {tag, state}. |
| `ctrl_tag_a_wr_way_onehot` | to `l1_tag_array` | Way select for write (all-ones on the init walk). |
| `ctrl_data_a_addr` | to `l1_data_array` | Port A address {set, beat}. |
| `ctrl_data_a_way` | to `l1_data_array` | Port A read way (hit way or victim way). |
| `ctrl_data_a_rdata` | from `l1_data_array` | Hit read data (combinational). |
| `ctrl_data_a_wr_en` | to `l1_data_array` | CPU write-merge enable (hit / replayed D-4 merge). |
| `ctrl_data_a_wr_wdata` | to `l1_data_array` | Merge write data. |
| `ctrl_data_a_wr_be` | to `l1_data_array` | Per-byte merge enables. |
| `ctrl_repl_req` | to `l1_repl` | Request replacement decision (one-cycle pulse per miss). |
| `ctrl_repl_way` | from `l1_repl` | Selected victim way. |
| `ctrl_repl_hit` / `ctrl_repl_update` | to `l1_repl` | Policy update: hit service / fill install (upgrade fires hit). |
| `ctrl_victim_load` | to `l1_victim` | Strobe: stage the dirty victim line from the data array. |
| `ctrl_fill_start` | to `l1_fill` | Launch a fill for this line address. |
| `ctrl_fill_addr` | to `l1_fill` | Line-aligned fill address. |
| `ctrl_req_class` | to `l1_fill` / `amber_ace_issue` | Request class of the in-flight miss (READ_SHARED / READ_UNIQUE / CLEAN_UNIQUE). |
| `ctrl_fill_done` | from `l1_fill` | Fill completed (RLAST accepted). |
| `ctrl_fill_beat_valid` / `ctrl_fill_beat_idx` | from `l1_fill` | Received-beat strobe + index; feeds the bypass `pf_data_valid` (MAS ch02/06). |
| `ctrl_drain_start` | to `l1_drain` | Launch a drain from `l1_victim`. |
| `ctrl_drain_done` | from `l1_drain` | Drain completed (B handshake). |
| `ctrl_tag_b_req` | to `l1_tag_array` (via core mux) | Port-B ownership: high in the snoop grant cycle and throughout `CTRL_SNOOP`. |
| `ctrl_tag_b_set` | to `l1_tag_array` | Port-B lookup set (snoop set). |
| `ctrl_tag_b_tag_state` | from `l1_tag_array` | Per-way `{tag, state}` snoop lookup result (combinational). |
| `ctrl_data_b_addr` / `ctrl_data_b_way` | to `l1_data_array` | Port-B CD read `{set, beat}` at the hit way (or the fill way for a bypass hit). |
| `ctrl_data_b_rdata` | from `l1_data_array` | CD beat data (combinational). |
| `ctrl_snoop_req` | from `l1_snoop_resp` | Snoop address + type valid; held until `ctrl_snoop_ready`. |
| `ctrl_snoop_ready` | to `l1_snoop_resp` | Control accepts the snoop this cycle (safe-boundary grant). |
| `ctrl_crresp` | to `l1_snoop_resp` | 5-bit CRRESP result, combinational at the grant cycle (latched by the adapter). |
| `ctrl_cddata` / `ctrl_cdlast` / `ctrl_cdvalid` | to `l1_snoop_resp` | CD beat data/last/valid (each beat gated servable; CR is presented by the adapter after CDLAST). |
| `ctrl_cdready` | from `l1_snoop_resp` | CD beat accepted. |
| `ctrl_req_ready` | to `l1_cpu_frontend` | Ready for the next CPU request (IDLE, init done). |
| `ctrl_rsp_valid` | to `l1_cpu_frontend` | Response valid (one-cycle pulse). |
| `ctrl_rsp_data` | to `l1_cpu_frontend` | Response read data / write echo. |
| `ctrl_init_busy` / `ctrl_init_set` | status | Init-walk in progress / current set. |
| `ctrl_state` | status | FSM state (pkg `ctrl_state_t` encoding, observability). |

---

## Miss-Path Decision K-map

The combinational decision that launches drain/fill/replay is captured in the kmap workbook:

- **Outputs:** `start_drain`, `start_fill`, `replay_now`.
- **Axes:** `{hit, victim_dirty, pending_bypass_match}`.
- **Sheet:** `K-maps amber control` in [`amber_signal_contracts.xlsx`](../../amber_signal_contracts.xlsx), generated by [`gen_amber_contracts_kmaps.py`](../../gen_amber_contracts_kmaps.py).

The sheet is marked **PROPOSED** because it is a micro-architecture decision owned by this chapter. The RTL (`l1_control`) has landed, but the workbook does not yet carry its `rtl_sop`, so the derived cover has not been diffed against it (Chapter 5).

---

**Last Updated:** 2026-10-07 (Task 4: snoop service + bypass integration)
