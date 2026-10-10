# TASK-001: Advanced scheduling / refresh modes for DDR4/LPDDR4 (from the DDR2 papers)
> Roadmap: `vault/Tasks/memory-controllers/ADVANCED_MODES_ROADMAP.md`
> Migrated 2026-09-25 from `projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/TASKS.md` (tooling TOOL-001). That file was a stub: "To be populated as RTL work begins."

**Priority:** P3 — there is no ddr4-lpddr4 RTL yet; this is the design-requirements survey that precedes it.
**Status:** closed 2026-10-04 — survey executed and owner-reviewed; findings
and dispositions below (Bhati 2016 trade-offs cited throughout)
**Owner:** TBD

Config-bit-selectable, OFF-by-default, faithful-DRAM-model red→green each; commodity here
because LPDDR4/DDR5 add controller-directed per-bank refresh + bank groups + FGR.

- [ ] **`refpb_ooo`** — out-of-order per-bank refresh (idle / lowest-queue bank, not round-robin). Commodity via LPDDR4 controller-directed per-bank refresh. *(Chang DARP #1)* — **Disposition: EVALUATE AT BRING-UP**.
- [ ] **`refpb_wrp`** — write-refresh parallelization (REFpb the lowest-queue bank during a write-drain window). *(Chang DARP #2)* — **Disposition: EVALUATE AT BRING-UP**.
- [ ] **`darp`** = `refpb_ooo` + `refpb_wrp`. *(Chang 2014/2016)* — **Disposition: EVALUATE AT BRING-UP**.
- [ ] **Refresh pausing** — pause a refresh bundle at `tRPC = tRFC/N` pause points, resume via a checkpointed row counter; forced-refresh at the `8×tREFI` deadline. **Research / model-only** (no JEDEC standard; needs a modified DRAM refresh FSM). *(Nair 2014)* — **Disposition: MODEL-ONLY**.
- [ ] **`sarp` / `dsarp`** — subarray access-refresh parallelism. **Research / model-only** (DRAM array microarchitecture). *(Chang SARP/DSARP)* — **Disposition: MODEL-ONLY**.
- [ ] **DDR4-native (new commodity):** Fine-Granularity Refresh (FGR 1x/2x/4x, MR3), bank-group scheduling (tCCD_L vs tCCD_S), commodity LPDDR4 per-bank refresh. Already specified in andesite HAS Ch 3.4 / Ch 3.1 — **Disposition: ADOPT**.

## Survey findings

### 1. `refpb_ooo` — out-of-order per-bank refresh

Mechanism: instead of tracking the device's internal round-robin bank counter, the controller nominates the bank that is idle or has the lowest queue occupancy for the next REFpb. LPDDR4's per-bank refresh command carries the bank address on the CA bus (JESD209-4), so the controller can legally choose.

JEDEC status: commodity-legal under JESD209-4; DDR4 has no controller-directed per-bank refresh, so this policy is LPDDR4-only here.

Benefit and cost: the win is fewer refresh-induced stalls, because the scheduler can target banks that are not currently demanded. The cost is extra scheduling state (bank occupancy / idle tracking) and the starvation risk of a bank that is never the "lowest occupancy." The task file's own citations (Chang DARP #1) describe the algorithm; Bhati 2016 does not quantify it.

Interaction with inherited base and andesite work: this hangs directly on the LPDDR4 controller-directed per-bank hook specified in andesite HAS Ch 3.4. The policy is layered on top of scoria's landed Modes A/B/C (elastic refresh, TCR, ZQCS placement), which remain the policy base; the JEDEC ±8 postpone/pull-in credit ceiling is untouched.

Recommendation: **EVALUATE AT BRING-UP**. Implement behind a CSR policy hook, reset OFF, with telemetry so a sweep can show when it wins over round-robin.

### 2. `refpb_wrp` — write-refresh parallelization

Mechanism: during a write-drain window, issue REFpb to the lowest-queue bank so that refresh consumes a bank that is not on the read path while writes keep the data bus busy. Like `refpb_ooo`, this requires the controller to name the bank, so it is legal only where controller-directed per-bank refresh exists.

JEDEC status: commodity-legal under JESD209-4; not available on DDR4.

Benefit and cost: the win is higher write-heavy throughput, because refresh overlaps with write traffic instead of stealing read slots. The cost is tighter scheduler coupling between write-drain watermarks and refresh grants, and the possibility of pushing read latency if write-drain windows are extended to absorb refreshes. The task file's own citations (Chang DARP #2) describe the algorithm; Bhati 2016 does not quantify it.

Interaction with inherited base and andesite work: reuses the same LPDDR4 bank-selection hook as `refpb_ooo` and the write-batch watermark logic inherited from pumice/scoria. It does not alter the elastic/TCR/placement base.

Recommendation: **EVALUATE AT BRING-UP**. Ship as an independent enable so it can be combined with or measured separately from `refpb_ooo`.

### 3. `darp` = `refpb_ooo` + `refpb_wrp`

Mechanism: the DARP family combines out-of-order per-bank refresh with write-refresh parallelization so that refreshes are both steered away from hot banks and overlapped with write-drain activity.

JEDEC status: commodity-legal under JEDEC209-4 because both halves are pure scheduling policies on top of controller-directed REFpb; there is no new DRAM command.

Benefit and cost: the benefit is additive when a workload has both bank-parallelism and write pressure. The cost is the combined scheduling complexity and the usual risk of policy interactions: the bank chosen for write-refresh parallelization may not be the same as the bank chosen by out-of-order logic, so the scheduler must have a clear arbitration rule.

Interaction with inherited base and andesite work: both halves hang on the LPDDR4 per-bank policy hook in andesite HAS Ch 3.4. The elastic/TCR/placement base supplies the credit and timing envelope; DARP only changes which bank is refreshed and when.

Recommendation: **EVALUATE AT BRING-UP**. Implement as two separate enable bits (`refpb_ooo` and `refpb_wrp`) so the combined `darp` mode can be composed and measured, not hard-wired.

### 4. Refresh pausing (Nair 2014)

Mechanism: a refresh bundle is broken at Refresh Pause Points spaced at `tRPC = tRFC/N`; a checkpointed row counter lets the DRAM resume later, and a forced-refresh deadline at `8×tREFI` guarantees retention.

JEDEC status: research / model-only. No JEDEC standard defines a pausable auto-refresh command; commodity DRAMs treat REF as atomic for the full `tRFC` window.

Benefit and cost: the win is lower tail latency for critical reads that would otherwise wait for an entire `tRFC`. The cost is a modified DRAM refresh FSM, redefined refresh-command semantics, and the retention risk of any pause/resume bug. Bhati 2016 lists "Pausing" in its applicability matrix as controller-only modification, performance benefit "difficult to say," and self-refresh co-existence as supported; it does not provide quantitative trade-offs.

Interaction with inherited base and andesite work: this is incompatible with the inherited JEDEC ±8 credit window in the commodity sense, because it replaces the atomic refresh with a preemptible operation. It can only run in a faithful DRAM model that implements the pause FSM.

Recommendation: **MODEL-ONLY**. Gate it behind a PHY capability strap so firmware cannot enable it against a device that does not implement the pause FSM.

### 5. `sarp` / `dsarp`

Mechanism: subarray-level access-refresh parallelism allows the controller to access an idle subarray inside a bank that is currently being refreshed, treating refresh as a subarray-granularity operation rather than a bank-granularity one.

JEDEC status: research / model-only. It requires changes to the DRAM array microarchitecture; no commodity DDR4 or LPDDR4 part exposes subarray-selective refresh.

Benefit and cost: the win is higher bank-level parallelism than even per-bank refresh. The cost is DRAM die overhead and timing-impact: the project roadmap (`ADVANCED_MODES_ROADMAP.md`) cites Chang SARP/DSARP as adding +0.71% die area and +13.8% `tFAW`/`tRRD`. Bhati 2016 does not quantify SARP/DSARP.

Interaction with inherited base and andesite work: not buildable on commodity DDR4/LPDDR4; it lives in the faithful DRAM model. The scheduler-side hooks for per-bank refresh are irrelevant because the required array structure is not present.

Recommendation: **MODEL-ONLY**. If demonstrated at all, do so in the DRAM model, not in RTL targeted at a JEDEC device.

### 6. Fine-Granularity Refresh (FGR 1x/2x/4x)

Mechanism: DDR4 MR3 selects the refresh granularity. In 1x mode `tREFI` is 7.8 us and one refresh command refreshes the normal row count; 2x halves `tREFI` and refreshes roughly half as many rows per command; 4x quarters `tREFI`.

JEDEC status: commodity DDR4 (JESD79-4).

Benefit and cost: Bhati 2016 Table 2 gives the `tREFI`/`tRFC` pairs for DDR4: 4 Gb devices are 1x 7.8 us/260 ns, 2x 3.9 us/160 ns, 4x 1.95 us/110 ns; 8 Gb devices are 1x 7.8 us/350 ns, 2x 3.9 us/260 ns, 4x 1.95 us/160 ns. The same paper notes that for most workloads the finer-grained options increase energy and degrade performance, although exceptions exist (e.g., the `milc` benchmark, where 4x improves performance). The trade-off is shorter per-refresh busy windows at the cost of more frequent refresh traffic.

Interaction with inherited base and andesite work: already adopted in andesite HAS Ch 3.4. The FGR factor scales the interval arithmetic of the inherited elastic/TCR/placement base; the retention proof must be re-derived per factor, as scoria established for `REFpb`.

Recommendation: **ADOPT** — already in the books. The RTL bring-up must implement the MR3 select and the scaled interval accounting.

### 7. Bank-group scheduling (`tCCD_L` vs `tCCD_S`)

Mechanism: DDR4 partitions banks into groups. Column commands to the same bank group must satisfy `tCCD_L`; column commands to different groups satisfy the shorter `tCCD_S`. A bank-group-aware scheduler prefers cross-group issue when priorities are otherwise equal.

JEDEC status: commodity DDR4 (JESD79-4). LPDDR4 has no bank groups (`/mnt/data/github/dfi-specs/lpddr4/index.md`, corrected 2026-10-04), so this rule is DDR4-only.

Benefit and cost: the win is recovered bandwidth on workloads with stride/bank-parallel patterns. The `ddr4/index.md` cites a Synopsys article giving approximate DDR4-3200 values of ~4 ns for `tCCD_S` and ~6.4 ns for `tCCD_L`. The cost is one extra bank-group tag comparison per scheduling decision. Bhati 2016 does not quantify bank-group scheduling itself, but its conclusion notes that understanding JEDEC-provided timing options is essential for managing refresh and bandwidth penalties at higher densities.

Interaction with inherited base and andesite work: already adopted in andesite HAS Ch 3.1 (delta area 1). The long/short pairs are runtime CSRs in `global_timers` and `cmd_arbiter`. Per-bank-group refresh accounting (`PB-REF`) is intentionally delegated to andesite TASK-007 rather than duplicated here.

Recommendation: **ADOPT** — already in the books. The RTL bring-up implements the L/S-aware scheduler as part of the DDR4 path.

### 8. LPDDR4 controller-directed per-bank refresh

Mechanism: JESD209-4 REFpb carries the bank address on the CA bus, so the controller names the bank. Bhati 2016 notes that eight sequential per-bank refreshes are equivalent to one all-bank refresh for an eight-bank device.

JEDEC status: commodity LPDDR4 (JESD209-4).

Benefit and cost: only the targeted bank is busy during REFpb; the other seven remain accessible. Bhati 2016 Table 2 shows the magnitude for LPDDR3: a 4 Gb device has `tRFCab` = 130 ns and `tRFCpb` = 60 ns; an 8 Gb device has `tRFCab` = 210 ns and `tRFCpb` = 90 ns. LPDDR4 follows the same pattern of much shorter per-bank refresh windows.

Interaction with inherited base and andesite work: already adopted in andesite HAS Ch 3.4. The default is a sequential round-robin, which is one legal policy under JESD209-4; `refpb_ooo`, `refpb_wrp`, and `darp` hang on this hook. The elastic/TCR/placement base still governs when refreshes are requested.

Recommendation: **ADOPT** — already in the books. The RTL bring-up must replace scoria's rotor with explicit bank scheduling for the LPDDR4 path and keep the round-robin as the reset-default policy.

## Survey verdict

The RTL bring-up should build the commodity mechanisms first, because they are already specified in the andesite HAS and are legal on real devices: **FGR 1x/2x/4x** for DDR4, **bank-group scheduling** for DDR4, and **controller-directed per-bank refresh** for LPDDR4. These three are the table stakes and should not be gated behind evaluation flags beyond the runtime CSR selects already defined.

The **DARP family** (`refpb_ooo`, `refpb_wrp`, `darp`) is also commodity-legal on LPDDR4, but it is scheduling policy rather than mandated behavior. These should be **EVALUATED AT BRING-UP** behind independent OFF-by-default CSR enables with telemetry, so one bitstream can sweep them against the round-robin baseline.

**Refresh pausing** and **`sarp`/`dsarp`** have no JEDEC path on commodity DDR4/LPDDR4. They should remain **MODEL-ONLY** demonstrations in the faithful DRAM model, gated by a PHY capability strap so they cannot be armed against a real device.

Per-bank-group refresh accounting (`PB-REF`) is out of scope for this survey; it is tracked in **andesite TASK-007**.
