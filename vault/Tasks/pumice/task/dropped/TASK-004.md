# TASK-004: pumice is AT REST: what a future session needs to know
> **Was `PUMICE-029` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** DROPPED 2026-09-25 (content moved, see below) — was open 2026-09-10 (informational; do not close, it is the handover)
**Priority:** read before touching pumice

pumice met its targets on 2026-09-10 and was deliberately put down. This block
is the handover, not a work item.

**NEXT ACTION when work resumes: [[ISSUE-001]]** — the ~49-cycle read latency,
about 2x LiteDRAM's on the same board and PHY. It is the largest identified
defect left and it also closes the small-burst read shortfall, so it is one
fix for two symptoms. Everything else on this page is either informational or
a smaller, independent item.

**Where it landed.** Nexys A7, 75 MHz / DDR2-300 / BL4 on x16, peak 600 MB/s:
write 570.3, read 571.3, concurrent read+write 570.1 total (2.00x LiteDRAM
through the identical harness). 14/14 integrity, WNS +0.285 ns on 94 060
endpoints, 219 controller tests plus the 31-test char gate green. Board build:
`PUMICE_SYS_75=1 make bitstream` in `build-perf` (WITHOUT that define you get
66.67 MHz and every number is wrong).

**The three things most likely to waste a future session:**

1. **The sim cannot run the board's geometry** ([[PUMICE-028]]). The core suite
   is BL8 / 64-bit beat / device == beat, so one DRAM burst is FOUR bus beats
   and any per-sub-command rate limit is divided by four before a bandwidth
   assertion sees it. That is precisely how a 2x read throttle shipped green.
   If a board number and a sim number disagree, suspect this FIRST.
2. **Regenerate the bridges on every build, and re-run the gate after.**
   ([[PUMICE-027]], closed 2026-09-11.) The two-writer hazard that stood here
   was fixed entirely by a bridge-generator change -- master-unique fabric IDs
   plus a slave-side CAM keyed on the returning BID -- with no pumice edit at
   all. `ddr2_char_framework/bin/regen_bridges.sh` reproduces the committed RTL
   byte-identically today; if it ever does not, the generated fabric has moved
   under the harness, and the char suite is the thing that will tell you.
3. **The spec collateral dates instantly.** The design/ tables and waves were
   written mid-campaign and asserted a 15%-of-peak controller with five live
   defects long after the board reached 95%. Both halves are now gated
   (`docs/check_kmap_rtl_sync.py`, `design/check_waves.py`) and the generators
   refuse to emit on failure -- but the gates only cover what they cover. Date
   every claim, or re-run it.

**Known-open performance items, none blocking:**
* Read latency ~49 cycles vs LiteDRAM's 24.7 -- now filed as [[ISSUE-001]],
  the largest identified defect left. It also explains the small-burst read
  shortfall (AxLEN 1/2/4 at 16/31/60% of peak): Little's law against the read
  generator's 8-burst budget, five points predicted within 2%.
* The three runtime axes are characterized but NOT tuned -- nobody has picked
  defaults per workload class from the sweep ([[TASK-002]]).
* Area: pumice_top is 12 224 LUT / 7 878 FF, ~5x LiteDRAM's controller+PHY for
  equal streaming bandwidth. That is the deliberate research-controller trade
  and is now stated at the top of AT-A-GLANCE.md; it is the obvious target if
  anyone ever wants a product part.

**Operational traps that cost real time here:**
* `PUMICE_SYS_75=1` or the build is 66.67 MHz.
* `ddr2_char_macro` did not thread `RD_RET_DEPTH`; board default is now 64 via
  `PUMICE_RD_RET_DEPTH`. Check a parameter is actually PASSED before believing
  the flow sets it.
* `ddr2_char.num_gen` defaulted to 1 while the board carries 2 per direction.
  Call `sync_gen_config()`; never trust a hardcoded count.
* The char-framework sim is the board gate before any pumice RTL commit
  ([[TASK-003]]).

Related: [[project_pumice_read_ceiling_fixed]],
[[project_litedram_same_harness_ab]], [[project_pumice_char_suite]].

---


## 2026-09-25 — DROPPED as a task; the content MOVED, it was not discarded

Sean: *"if a task can't be closed, that means it is a rule that should be
elsewhere."* This was never a work item — it had no completion condition, so
it would have sat in the open lane forever, inflating the count and training
readers to skim it.

Content now lives at: **projects/components/memory-controllers/pumice-ddr2-lpddr2/CLAUDE.md**

Dropped here rather than closed, because "closed" implies work finished. No
work was done; the record moved to where the repo's own convention says it
belongs (area facts beside the code, method in the handbook — see the root
CLAUDE.md).
