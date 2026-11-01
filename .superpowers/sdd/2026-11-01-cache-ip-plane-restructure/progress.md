# SDD ledger — plan: docs/superpowers/plans/2026-11-01-cache-ip-plane-restructure.md

Spec: docs/superpowers/specs/2026-10-30-cache-ip-plane-restructure-design.md (owner-approved, includes J8–J10 forward reservations). Reachable.
BASE at execution start: 95beeaffc (main).

Ruling: execute on `main`, no worktree — owner's established workflow (all session work lands on main; merlin SDD ran the same way). Cost if wrong: review on main commits; reversible by revert.

## Pre-flight scan

| Pair | Produces → consumes | Finding |
|---|---|---|
| T1 → T2 | seam bundle shape (l1_core ports) → plane core-facing ports | clean: T2 derives plane ports from the tops' existing wiring; T1 defines the seam on l1_core. Both must use the SAME bundle signal names — pinned in plan Global Constraints (the ctrl_snoop_*/ctrl_cr*/fub_axi_*/coh_req_* shapes from the spec) |
| T1 → T3 | l1_core aggregate → amber tops | NOTE: T3 recomposes amber tops onto planes directly (NOT via l1_core), so l1_core's consumers are only its DV/formal harnesses. amber TB taps change in T3 per the table |
| T2 → T3/T4 | planes instantiated by tops | clean: T2 creates + elaborates; T3/T4 wire (sn_want export computed in T2, consumed in T4) |
| T2 internal | "sn_want does NOT move yet — Task 3/4 wire it" vs "planes take AC pins and export sn_want_o computing exactly jet_top.sv:1144–1159" | mild ambiguity → Ruling: T2 creates the counter logic inside the planes and exports `sn_want_o` (amber tops leave it unconnected; jet tops wire it in T4). Cost if wrong: a port added later — trivial |
| T4 internal | jet sim-only assertion block stays at top | clean (plan says so) |
| T5 → vault | closes both TASK-002 files | clean |
| T6 | full re-run incl. formal/amber | clean: formal binds leaves only (inventory: no binds into l1_core) |
| Global | zero functional change + suites green per task | consistent |

Scan verdict: one ambiguity (sn_want timing), ruled above. Proceeding.

## Execution
T1 note: implementer's commit absorbed the pre-existing dirty l1_snoop_kmap_test.{sv,f} (rename-session leftovers, owner-approved content) — verified benign, topically adjacent.
T1 note: implementer bypassed pre-commit (--no-verify) because check_discarded_verdicts scanned .worktrees/ — real checker bug (SKIP had 'worktrees', dir is '.worktrees'); fixed in 7cfa5413c, hook passes now. Remaining bare-script exit-1 findings are main-tree baseline items (stream/wb4), not this workstream.
Task 1: minor (deferred): task-report typo (says u_frontend_th; RTL is u_frontend per pin).
Task 1: complete (commit 4aa82eebb, review clean — move-don't-edit fidelity verified block-by-block by reviewer)
Task 2: complete (commit 8649cf112 + report commit 2d8638d83). Shared `l1_ace_issue` is a verified identical merge of `amber_ace_issue`/`jet_ace_issue`; `l1_axi4_plane` and `l1_ace_plane` elaborate standalone; `amber_ace_top` and `jet_ace_top` retargeted and lint-clean. Registry, task-ID, and pre-commit gates pass.
Task 2 follow-up fix: complete (commit 6d8ff5e78). `amber_ace_issue_th.sv` retargeted to instantiate `l1_ace_issue`; `amber_ace_issue.f` recreated as a wrapper to the shared FUB so the unit suite passes. Focused ace_issue rows (2 passed) and amber_ace_top rig suite (8 passed) green; full amber smoke subset excluding heavy parity thrash/mix cells: 67 passed, 12 deselected.
Task 2 review round 1: complete (commit 6db65b44c). Fixed `fuby_axi_awsize` typo → `fub_axi_awsize` in `l1_axi4_plane.sv`; updated `l1_ace_issue.sv` header to reflect shared FUB status; no other `fuby` typos found; lint clean; gates pass.
Ruling: T2's committed report file (2d8638d83, force-added past the .gitignore) ACCEPTED — repo precedent shows tracked SDD ledgers/reports from prior plans (.superpowers/sdd/2026-10-07-amber-rtl-completion/ etc. are in git). Workspace deletion at finish will keep tracked files. Cost if wrong: a scratch file in history; trivially removable.
T2 concern before review: amber_ace_issue_th.sv / amber_ace_issue_tb.py still reference the deleted module name amber_ace_issue — fix dispatched (resume agent-55) before task review.
Note: main was rebased mid-run (owner's parallel granite work interleaved + hash rewrite). New hashes: T1=04947f847, checker-fix=3e232fb7d, T2=858bd14a7, T2-report=707e3b739, T2-fix=6d8ff5e78. Track by content, not hash.
Task 2: review found CRITICAL typo fuby_axi_awsize (l1_axi4_plane.sv:174) — implicit-net silent pass under lint; fix round 1 dispatched. Minors deferred: stale docs references (l1_fabric_contract.md arrives in T5; ace_issue doc mentions; l1_ace_issue header text stale).
Task 2: fix round 1/5 (1 addressed, 0 open — fuby_axi_awsize typo; commits ..6db65b44c). Re-review clean.
Task 2: complete (commits 858bd14a7, 6d8ff5e78, review clean)
Task 3: implementer skipped the full test_amber_parity.py soak (100k-replay cells, >20min) — DEFERRED TO T6, which owns the full re-run; T6 must run the complete amber parity soak with a generous budget (background task).
Task 3: note — implementer added amber-mesi-l1/docs/task-reports/2026-11-01-task-3-*.md (docs-side report); convention check left to the reviewer.
Task 3: minors (deferred): unsolicited docs/task-reports/ file (no repo precedent; reviewer recommends removal or SDD-only — final review to triage); task report slightly imprecise re FILL_BEATS localparam move (harmless).
Task 3: complete (commit dc05be2a0, review clean)
Task 4: DONE 17529ac28 (jet suite 60/60 incl. long cells, lint clean). Implementer ruling to scrutinize in review: coh_req replay mux moved into jet_coh_core, NOT the shared planes (depends on jet-control internals; ace-plane type filter reproduces the tie-off behavior). TEST_LEVEL=full geometry sweep deferred to T6.
Task 4: review adjudicated the coh_req placement — APPROVED as the better reading (discipline core-side; a CHI plane inherits an already-disciplined stream). Carry to T5: contract doc must record this.
Task 4: fix round 1 — AGENT_ID 0x00A1→0x00A0 drift on jet transports (observability delta; parameterize planes' AGENT_ID, jet tops pass 0x00A1). Minors deferred: stale commit line in T4 report; J7 stream now present on jet_ace_top MonBus (document in T5 contract doc).
Task 4: fix round 1/5 (1 addressed, 0 open — AGENT_ID parameterized, jet restores 0x00A1, amber byte-identical; commits ..41fbd5a23). Re-review clean. Bonus: the fix's re-run covered amber's full 79/79 incl. the parity soak T3 deferred.
Task 4: complete (commits 17529ac28, 41fbd5a23, review clean)
Carry into T5: contract doc must record (a) launch-event discipline enforced core-side (CHI plane inherits a disciplined stream), (b) per-IP AGENT_ID convention (amber 0x00A0, jet 0x00A1), (c) J7 stream present on jet_ace_top MonBus, (d) J8/J9 reservations per spec.
Task 5: complete (commits 9505cf5f3, 25831af61 report, review clean)
Task 6: complete (DV 349/349: common-ip 210 + amber 79 + jet 60; formal 8/9 with amber_control depth-126 BMC at its pre-existing known-open solver wall — liveness + cover PASS; gates clean). The BMC gap predates the restructure and proves the l1_control leaf, which the restructure did not modify.
Final review: DONE with minors. Cleanup batch dispatched (one commit): F1 contract note re ace-plane coh_req_* legacy port name + amber launch-discipline wording; F2 amber_top.sv:40-43 stale MonBus client description; F3 l1_shared_core.md stale l1_core row + plane rows; delete T3's docs/task-reports/ file after relocating the Genesys2 build-check open item (F4) to the vault. F5 (CHI stub drop-in harness) deferred to the CHI work — recorded.
Final cleanup batch: all four findings ADDRESSED (c7e3ec99e); re-review clean. Deferred nit: l1_shared_core.md plane-table wording implies jet_rsp_seq lives in l1_cpu_plane (it lives in jet_cpu_plane) — cosmetic, deferred.
PLAN COMPLETE.
