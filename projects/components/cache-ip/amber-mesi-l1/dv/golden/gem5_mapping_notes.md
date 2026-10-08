# gem5 → amber FSM mapping notes

**Source:** `projects/components/cache-ip/References/gem5-ruby-protocols/MESI_Two_Level-L1cache.sm`
(gem5 Ruby `MESI_Two_Level` L1 cache controller, SLICC; line numbers below are
the 2026-10 in-repo checkout).

**Derived artifact:** `dv/golden/amber_fsm_oracle.py`, pinned against
`rtl/includes/amber_pkg.sv` (HAS Table 3.0 decode) by
`dv/tests/test_amber_oracle.py` (row-by-row table + pkg-pin simulation).

These notes record the mapping as **derivation, not extraction**: gem5 is a
two-level *directory* protocol controller; amber is a *broadcast snoopy* L1
behind an ACE-shaped responder. Where the domains differ, the landed
`amber_pkg` Table 3.0 decode (the binding snoop-decode authority per the MAS)
and MAS ch02/02 ordering rules win, and the divergence is called out below.

## 1. State collapse (DECISION D-11)

gem5 keeps in-flight conditions as TBE transient states; amber's blocking
CTRL FSM realizes the same conditions as pipeline states (one transaction in
flight, MAS ch02). Collapse mapping:

| gem5 state | Meaning (gem5 desc, .sm:95-101) | amber CTRL state |
|---|---|---|
| `IS` | issued GETS, no response yet | `CTRL_MISS_FILL` (read miss) |
| `IM` | issued GETX, no response yet | `CTRL_MISS_FILL` (write miss) |
| `SM` | issued UPGRADE, waiting acks | `CTRL_MISS_FILL` (upgrade, no data) |
| `IS_I` | GETS raced an Inv; data comes, line stays Invalid | `CTRL_MISS_FILL` + post-commit `STATE_I` install |
| `M_I` | replacement PUTX sent, waiting WB_Ack | `CTRL_MISS_DRAIN` |
| `SINK_WB_ACK` | victim re-snooped while WB outstanding | `CTRL_MISS_DRAIN` (victim bypass) |

gem5 states with **no amber counterpart (out of scope, D-11):**

- `PF_IS / PF_IM / PF_SM / PF_IS_I` — hardware prefetch transients
  (`enable_prefetch := "False"`, .sm:53); amber v1.0 has no prefetcher.
- `LLSC_E / LLSC_M` — LL/SC lock states (.sm:110-111); no LL/SC in amber v1.0.
- `NP` — "not present" is indistinguishable from `I` at the tag-state level;
  folded into `I` (gem5 itself transitions `{NP,I}` together everywhere).

Entry edges the 10-event oracle domain does not name: `M_I` is entered when a
*different* line's miss selects this (formerly M) line as victim — gem5
`L1_Replacement` (.sm:1271 E, .sm:1308 M). `L1_Replacement` is internal to
amber's `CTRL_MISS_VICTIM`, so the per-line oracle exposes `M_I` as an
initial-condition state for DV rather than a transition edge.

## 2. Event mapping

| gem5 event (.sm:115-151) | amber oracle event | Note |
|---|---|---|
| `Load`, `Ifetch` | `CPU_RD` | amber has a single CPU port (no I/D split); Ifetch ≡ Load |
| `Store` | `CPU_WR` | |
| `Fwd_GETS` | `SNOOP_READ_SHARED` | peer read-shared |
| `Fwd_GET_INSTR` | `SNOOP_READ_ONCE` | closest IHI0022 analog; see §4 divergences |
| `Fwd_GETX` | `SNOOP_READ_UNIQUE` | |
| `Inv` | `SNOOP_CLEAN_INVALID` / `SNOOP_MAKE_INVALID` | gem5 has one Inv flavor; split per IHI0022, see §4 |
| *(no gem5 counterpart)* | `SNOOP_CLEAN_SHARED` | clean probe; IHI0022 only |
| `Data`, `Data_all_Acks`, `DataS_fromL1`, `Data_Exclusive` | `FILL_DONE` | plus `Ack`/`Ack_all` for the SM upgrade — all collapse to "the outstanding request completed"; S-vs-E outcome is the `fill` qualifier |
| `WB_Ack` | `DRAIN_DONE` | |

gem5 events not mapped: `L1_Replacement`/`PF_L1_Replacement` (internal, §1),
`PF_*` and `LLSC_*` (out of scope), `Data`/`Ack` partial-ack counting
(directory ack-counting artifact; amber's blocking fill completes on RLAST →
one `FILL_DONE`), `Load_Linked`/`LLSC_*`.

## 3. Transition groups (stable states) — gem5-cited

All citations are `transition(...)` blocks in `MESI_Two_Level-L1cache.sm`.

- **I × cpu_rd → IS, cpu_wr → IM**: .sm:1106 (`{NP,I} Load IS`,
  `a_issueGETS` .sm:586), .sm:1174 (`{NP,I} Store IM`, `b_issueGETX`
  .sm:657). Miss-request classes map to MAS Table 2.8.1: GETS →
  `READ_SHARED`, GETX → `READ_UNIQUE` (write-allocate fetches the line;
  D-4 merges the store on replay), upgrade → `CLEAN_UNIQUE`.
- **S/E/M × cpu_rd hit**: .sm:1222 (`{S,E,M} Load`, `h_load_hit` .sm:873).
- **E/M × cpu_wr hit → M**: .sm:1264 (`{E,M} Store M`, `hh_store_hit`
  .sm:899, sets Dirty).
- **S × cpu_wr → SM (upgrade)**: .sm:1244 (`S Store SM`, `c_issueUPGRADE`
  .sm:695).
- **E × RS/RO → S**: .sm:1292 (`E {Fwd_GETS,Fwd_GET_INSTR} S`,
  `d_sendDataToRequestor` + `d2_sendDataToL2`).
- **E × RU → I**: .sm:1286 (`E Fwd_GETX I`).
- **E × CI/MI → I, no data**: .sm:1279 (`E Inv I`, comment "don't send
  data", `fi_sendInvAck` .sm:810).
- **M × RS → S**: .sm:1338 (`M {Fwd_GETS,Fwd_GET_INSTR} S`, `d`+`d2`).
- **M × RU → I**: .sm:1332 (`M Fwd_GETX I`).
- **M × CI → I, dirty to L2**: .sm:1321 (`M Inv I`, `f_sendDataToL2`
  .sm:782).
- **S × invalidate snoops (RU/CI/MI) → I**: no `Fwd_GETX` transition leaves
  S in gem5 — the directory invalidates sharers itself: .sm:1256 (`S Inv I`,
  `fi_sendInvAck`). Broadcast amber sees the peer's READ_UNIQUE directly;
  CRRESP/next-state are identical (no transfer, → I).
- **S × RS/RO → S, CS → S, I × any snoop → I**: no gem5 transition exists
  (the directory serves peer reads and never probes I/S-with-clean lines);
  the safe no-transfer decode comes from the binding HAS Table 3.0 rows.

## 4. Divergences from gem5 (amber/IHI0022 wins; recorded, not silently taken)

1. **M × ReadOnce → Invalid** (oracle + pkg). gem5 lumps `Fwd_GET_INSTR`
   with GETS and keeps the sharer: .sm:1338 → S. IHI0022 ReadOnce is a
   "don't keep" read: transfer dirty data, drop the line. HAS Table 3.0 M
   row pins `DT+PD, → I`. (E × RO agrees both ways: E → S.)
2. **M × MakeInvalid: no data transfer**. gem5's single `Inv` writes dirty
   data back (.sm:1321); IHI0022 forbids DataTransfer on MakeInvalid (the
   requester overwrites the whole line). HAS Table 3.0 M row: no transfer,
   → I. gem5's `Inv` maps to amber's `CLEAN_INVALID` (which *does*
   transfer, .sm:1321 ↔ pkg `DT+PD+IS`); `MAKE_INVALID` has no gem5 analog.
3. **Invalidating snoop during IM/SM commits Invalid**. gem5 keeps the
   fetch/upgrade alive under directory serialization: .sm:1475 (`IM Inv
   IM`, then .sm:1497 `IM Data_all_Acks M` ends M) and .sm:1526 (`SM Inv
   IM`). Amber's broadcast fabric applies the snoop's state change *after
   the fill commits* (MAS ch02/02 "Snoop vs Fill Ordering"), so the line
   installs I — exactly gem5's own `IS_I` resolution (.sm:1390:
   `u_writeDataToL1Cache` runs, state I). `SM` converts to a full
   exclusive fetch (IM) per .sm:1526; a *downgrade* snoop during IM
   (RS/CS) commits S and the replayed write re-upgrades (composes with
   .sm:1244). Ordering-equivalent to gem5's "Fwd arrives after the store
   completed" serialization. **Task 4 pin (2026-10-07):** once the
   post-commit effect is armed it is *sticky* — a later shared-domain
   snoop is still answered at the original post-fill state (the bypass
   register answers at `pf_state`, never at the pending effect) and the
   fill commits the armed effect unchanged; gem5's own `IS_I` repeat
   handling answers at the fill state too (.sm:1364 pattern). This closes
   the `_im_step` pending-clear corner the Task 2 review flagged as
   UNCITED: the oracle previously *cleared* a pending `'I'` on a
   fixed-point snoop (the fill would have committed M, un-invalidating
   the race); `_im_step` now keeps the effect (matching `_is_step`'s
   existing branch), pinned by five new table rows in
   `test_amber_oracle.py` and the `ImStepPendingClearCorner` directed RTL
   test. A second snoop inside the killed-upgrade window (SM converted to
   IM before the re-fetch commits) is answered at the installed S state in
   the RTL vs gem5's converted-IM M — a one-cycle window, recorded in the
   control testplan gaps.
4. **Snoop during a fill is answered at the post-fill state** (the
   pending-fill bypass, MAS ch02/02). gem5 cannot see this case — a
   forwarded request never targets a line the directory knows is only
   in-flight (no `IS/IM × Fwd_*` transitions exist). All transient-snoop
   CRRESPs are therefore derived as `Table 3.0 ref_state = post-fill state`
   (pf_state for IS/IS_I/IM, installed S for SM, victim M for
   M_I/SINK_WB_ACK), which the pkg-pin simulation asserts cell-by-cell.
5. **M_I × CleanShared / MakeInvalid / repeat Fwd_***: gem5 defines only
   `Fwd_GETX` (.sm:1352), `Fwd_GETS/INSTR` (.sm:1357), and `Inv` (.sm:1327)
   from M_I, plus `Inv` from SINK_WB_ACK (.sm:1562). The remaining cells are
   derived: the victim buffer holds the line until WB_Ack and re-serves it
   (Review Focus 3); CleanShared drains the dirty data and keeps the line
   out; MakeInvalid answers no-transfer (IHI0022) and does not cancel the
   in-flight drain. **Contrast, not support**: gem5's SINK_WB_ACK × Inv
   (.sm:1562) is `fi_sendInvAck` — ack-only, *no data* — because gem5's WB
   already delivered the dirty data to the directory before the Inv
   arrived. Amber's SINK_WB_ACK × snoop answers are data-full (DT per
   Table 3.0 at the victim's M state): the dirty data is still local in
   the victim buffer and must be re-served on CD. `.sm:1562` is therefore
   cited as contrast wherever a SINK_WB_ACK snoop row references it.
6. **E × CleanShared stays E** (pkg `IS+WU`, no transfer). gem5 has no
   clean-probe transaction; the row is IHI0022/Table 3.0 only. Same for
   `S × CleanShared` (no-op). The same Table-3.0-only status covers
   **M × CleanShared → S (`DT+PD+IS`)** explicitly: gem5 has no clean-shared
   probe that downgrades a dirty line — its only dirty-downgrade path is
   `Fwd_GETS` (.sm:1338), which also transfers to the *requestor*; the
   write-back-to-memory-only reading of CleanShared on M exists solely in
   HAS Table 3.0.
7. **CRRESP `IsShared` on M × CleanInvalid** (pkg sets IS=1 where gem5's
   writeback at .sm:1321 carries no such notion): the pkg follows the
   cocotb-framework 1.2.0 ACE BFM default handler family matrix — the pkg
   is binding, the oracle matches it, end of story.
8. **IS_I × exclusive-fill-data: gem5 installs E; amber commits Invalid**.
   `.sm:1438` is `transition(IS_I, Data_Exclusive, E)` — the directory was
   blocked when it sent the exclusive data, so gem5 installs the line
   **E** even though an Inv already raced the fetch. Amber commits I: the
   invalidating snoop claimed the line and the invalidation sticks (MAS
   ch02/02 post-commit application — the same policy class as divergence
   3). Note gem5's own two response flavors disagree once an Inv raced:
   `Data_all_Acks` → I (.sm:1390) but `Data_Exclusive` → E (.sm:1438).
   Amber sides with the invalidation-sticks reading for both.

## 5. Completions

- **IS × FILL_DONE**: gem5 splits on the response source: `Data` /
  `DataS_fromL1` → S (.sm:1374/.sm:1404), `Data_Exclusive` → E (.sm:1456).
  The oracle's `fill` qualifier ('S'/'E') is that response property; for IM
  it is always M (.sm:1497, `hhx_store_hit` merges the store — D-4), for SM
  the upgrade ack → M (.sm:1537). gem5's partial-ack states (`IM × Data →
  SM` .sm:1485, `Ack` counting .sm:957) are directory artifacts; amber's
  blocking fill has no partial-ack condition (single outstanding
  transaction, RLAST-or-B-completion semantics).
- **IS_I × FILL_DONE → I (amber, both fill flavors)**: gem5's
  `Data_all_Acks` path installs I — data still written to the entry, state
  Invalid (.sm:1390) — but its `Data_Exclusive` path installs **E**
  (.sm:1438): the two gem5 response flavors disagree once an Inv raced,
  and amber commits Invalid in both cases (divergence 8,
  invalidation-sticks). The .sm:1390 flavor remains the strongest evidence
  that amber's post-commit-invalidation (divergence 3) is the same
  resolution gem5 already uses for the read-miss race.
- **M_I/SINK_WB_ACK × DRAIN_DONE → I**: .sm:1315 (`M_I WB_Ack I`),
  .sm:1567 (`SINK_WB_ACK WB_Ack I`).
- **CPU access during any transient → stall**: .sm:1072
  (`{IS,IM,IS_I,M_I,SM,SINK_WB_ACK} {Load,Store,...}` →
  `z_stallAndWaitMandatoryQueue` .sm:988) — the blocking contract.

## 6. What the pkg-pin simulation proves

`dv/tests/test_amber_oracle.py::test_amber_oracle_pkg_pin` drives the landed
`amber_snoop_kmap` (the module wrapper over `amber_pkg.amber_snoop_crresp` /
`amber_snoop_next_state`, compiled via `amber_snoop_kmap.f` → `amber_pkg.f`)
with every snoop row of the oracle's table — stable rows at their own state,
transient rows at their §4 reference state — and compares the SystemVerilog
outputs against `oracle.step()`. FULL additionally sweeps all reserved
encodings: the pkg decode must return the contracted safe default (no
transfer, → I) while the oracle must refuse them (`AmberOracleError`),
which is exactly how the split responsibility (crash-proof decode vs
error-trapping FSM) is specified to stay in sync.
