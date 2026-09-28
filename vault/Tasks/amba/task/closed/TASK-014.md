# TASK-014: Add Address Range and ID Filtering

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-015** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P3
**Status:** COMPLETE 2026-08-30. All four features implemented, and the
address filter is proven by a mutation-checked test, not just present.
  * address-range filtering -- 9cfd06e8 (mechanism), 576c26c1 (gating on both
    the packet AND retire paths), e3fa51e0 (test), 94e0eb72 (exposed on all
    twelve wrappers)
  * runtime ID filtering -- fd3b9646
  * ID filtering, filter enable/disable -- already existed
The hazard section below is kept: it is why the design filters at REPORT time
rather than at admission, and anyone "simplifying" it will reintroduce the
orphan-error and slot-leak failures.
**Owner:** TBD

**Description:**
Add optional filtering capabilities to reduce monitor packet traffic.

**Features:**
- [x] Address range filtering (monitor only specific regions) -- DONE.
      Filters at report time; see the hazard below for why not at admission.
- [x] Transaction ID filtering (monitor only specific masters) --
      `ID_FILTER_ENABLE` / `ID_MATCH_BASE` / `ID_MATCH_COUNT` in
      `axi_monitor_base`, gating cmd/data/resp valids into the trans_mgr
      (`id_owned()`), threaded up through `axi_monitor_filtered`.
- [x] Configurable filter enable/disable -- packet-type mask (level 1) and
      event-code mask (level 3) in `axi_monitor_filtered`.
- [x] Runtime filter updates -- DONE (fd3b9646). cfg_id_filter_enable /
      cfg_id_match_base / cfg_id_match_count override the params when
      enabled; tied low the parameter path is bit-identical. AXI-Lite has no
      IDs, so the four axil4 wrappers tie them off rather than expose them.

**HAZARD -- why address filtering is not a mirror of the ID filter.**

The ID filter works because ALL THREE channels carry an ID, so cmd, data and
resp filter consistently. ADDRESS EXISTS ONLY ON THE COMMAND CHANNEL. Gating
`cmd_valid` on address would admit no command while that transaction's data
and resp beats still arrive, landing in the monitor's unmatched-data path --
which is DELIBERATELY ungated (a monitor must never stall returning data, see
axi_monitor_base) and emits orphan errors. The result would be MORE packet
traffic, which is the opposite of this task's purpose.

Doing it correctly needs per-ID admitted state so data/resp filter the same
way the command did. Note a single bit per ID is not sufficient: one ID can
have multiple outstanding transactions whose addresses straddle the range, so
it is a per-ID count, not a flag.

**DECIDED 2026-08-30: filter at REPORT time, not at admission.** The costing
is what settles it. Admission filtering needs a counter per POSSIBLE id --
`2**ID_WIDTH` counters of `clog2(MAX_TRANSACTIONS+1)` bits, so 256 x 5 =
1280 flops at the common ID_WIDTH=8/MAX_TRANSACTIONS=16, scaling as 2**IW
(~20k flops at ID_WIDTH=12). And it duplicates state the monitor already
holds: `bus_transaction_t` latches `.addr` per entry
(`next.addr = 32'(cmd_addr)` in trans_mgr).

Report-time filtering instead: let the command allocate normally, so data and
resp still match their entry and the orphan hazard above disappears entirely;
carry one "filtered" bit per TABLE ENTRY, set at allocation from the address
compare; suppress emission for entries carrying it. Cost is
`MAX_TRANSACTIONS` flops -- 16 at default, ~80x smaller, and it scales with
table depth rather than exponentially with ID width. The tradeoff is narrow
and acceptable: it cuts PACKETS but not CAM occupancy, and packets are what
this task is about ("reduce monitor packet traffic").

**Implementation plan, pinned against the RTL:**

1. Do NOT widen `bus_transaction_t`. It is shared across every monitor, and
   every producer would have to set the new field or it reads X.
2. Do NOT gate `state_change`. It looked like the natural hook and was NOT:
   `axi_monitor_base` drove `w_state_change_detected` from trans_mgr and
   NOTHING CONSUMED IT -- a dead output. (Only the two
   `formal/amba/axi_monitor_trans_mgr*` harnesses bound it, to assert it is
   zero after reset. The apb4/apb5 `w_state_change` signals are unrelated
   locals.) **DELETED 2026-08-31** on its own account, per this bullet: the
   output, its `r_trans_table_prev`/`r_state_change` flops, the base-level
   net, both formal harness bindings (P3 + cp_state_change), and the six
   places `axi_monitor_trans_mgr.md` still described it -- including a
   Related-Modules row claiming the REPORTER consumed it, which was never
   true. Proofs re-run PASS with 4 covers still reached; monitor suite 20/20
   at FULL.
3. Add a `logic [MAX_TRANSACTIONS-1:0] filtered_mask` OUTPUT from trans_mgr,
   set per entry at allocation, and take it as an INPUT on the reporters,
   which already receive `trans_table` and scan it themselves. Gate their
   emit decision with `!filtered_mask[i]`.
4. New knobs: `ADDR_FILTER_ENABLE` param (default 0 -> bit-identical build)
   plus runtime `cfg_addr_filter_{enable,low,high}`, threaded
   base -> filtered -> the axi4_*_mon wrappers the same way `N_ADDR_RANGES`
   already is.

NOT STARTED as RTL. This spans trans_mgr + base + the reporters + the twelve
wrappers + cocotb + formal, and a half-applied version of it is worse than
none -- it would silently drop packets.

**Use Case:**
- Reduce packet congestion in high-traffic systems
- Focus monitoring on specific subsystems
- Debug-specific master/slave combinations

---


**VERIFIED AND CLOSED 2026-09-15.** The entry had said COMPLETE since
2026-08-30 but stayed in `open.md`. Re-checked against the RTL rather than
trusting the status line, because a sibling entry (COMMON-026) carried the
same shape and the tracker had drifted there too:

* address-range filtering -- `ADDR_FILTER_ENABLE` parameter plus
  `cfg_addr_filter_enable` / `cfg_addr_filter_low` / `cfg_addr_filter_high`
  ports in `rtl/amba/monitor/axi_monitor_base.sv`, with the TASK-015
  rationale comment still in place at the declaration.
* ID filtering -- `ID_FILTER_ENABLE` / `ID_MATCH_BASE` / `ID_MATCH_COUNT`
  and the `id_owned()` gate.
* runtime override -- `cfg_id_filter_enable` / `cfg_id_match_base` /
  `cfg_id_match_count`.
* enable/disable masks -- `axi_monitor_filtered.sv` present, 19 mask
  references.

All four features the task lists are in the tree. The HAZARD section above is
kept deliberately: it records why filtering happens at REPORT time rather than
at admission, and anyone "simplifying" it would reintroduce the orphan-error
and slot-leak failures it documents.

---
