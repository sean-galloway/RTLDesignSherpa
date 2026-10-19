# AXI3 Converters Implementation Plan (`axi4_to_axi3` / `axi3_to_axi4`)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `axi4_to_axi3` and `axi3_to_axi4` protocol converters (RTL + co-located cocotb DV) to `projects/components/utility-ip/converters/`.

**Architecture:** Top wrapper + `_rd`/`_wr` submodules mirroring `axi4_to_axil4`. Downgrade chops >16-beat bursts into same-ID ≤16-beat AXI3 chunks with worst-response merge; upgrade is pass-through with WID stripped under a single-active-write contract. DV drives both sides with CocoTBFramework AXI4/AXI3 BFMs (RDS-DV #87).

**Tech Stack:** SystemVerilog (Verilator sim), cocotb + cocotb-test, CocoTBFramework BFMs, make/verible lint.

**Spec:** `docs/superpowers/specs/2026-10-10-axi3-converters-design.md`

## Global Constraints

- RTL style: SPDX header + `timescale 1ns/1ps` + `` `include "reset_defs.svh" `` (see `axi4_to_axil4_rd.sv:1-41`); `aclk`/`aresetn` (active-low sync reset via reset macros); `s_`/`m_` prefixed sides.
- AXI3 side port naming: `m_axi3_*` (downgrade) / `s_axi3_*` (upgrade); AXI4 side keeps `s_axi_*` / `m_axi_*`.
- Parameters on every module: `AXI_ID_WIDTH=8`, `AXI_ADDR_WIDTH=32`, `AXI_DATA_WIDTH=32`, `AXI_USER_WIDTH=1`. No data-width conversion.
- AXI3 qualifiers: `AWLEN/ARLEN` 4-bit, `AWLOCK/ARLOCK` 2-bit, **no QoS/REGION**, W carries `WID`. `CACHE`/`PROT`/`USER` pass through.
- DV BFMs come from the RDS-DV dev clone until cocotb-framework 1.2.2 releases: every pytest invocation carries `PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src` (prepends; site-packages still resolves TBClasses etc.).
- Test command form: `TEST_LEVEL=func PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src venv/bin/python -m pytest <test path> -q` from repo root.
- Gates after any SV edit: `make -C projects/components/utility-ip/converters/rtl verible` and `venv/bin/python bin/check_sv_decl_order.py <new .sv files>`; after vault edits: `venv/bin/python bin/check_task_ids.py`.
- Worst-response merge ranks: `DECERR(2'b11) > SLVERR(2'b10) > EXOKAY(2'b01) > OKAY(2'b00)`.
- LOCK maps: AXI4→AXI3 `1'b0→2'b00`, `1'b1→2'b10` (exclusive); AXI3→AXI4 `2'b00→1'b0`, `2'b10→1'b1`, `2'b01→1'b0` (locked collapses to normal, documented).
- Shared tree: commit by explicit pathspec only; never bare `git add`/`git commit`.

## Review Focus

1. **Multi-outstanding AXI4 read IDs** — chopped-chunk R merge state must be per-ID; an R beat of ID A must never consume ID B's chunk counter or worst-response register.
2. **AXI4 W stream arriving before its AW handshake** — AXI4 allows early W; the W-segmentation queue must tolerate W beats for an AW not yet accepted (buffer beats, or assert-and-document; pin: buffer up to one full burst, assert on overflow).
3. **Per-chunk error merge leakage** — a middle chunk's SLVERR must surface only on the transaction-completing beat, never on intermediate beats.
4. **Back-to-back chopped bursts at full rate** — chunk n+1 AR must issue while chunk n R streams (pipelined), no bubble-induced deadlock with `rready` low.
5. **`axi3_to_axi4` WID contract violation** — interleaved/changing WID within one W run must fire the assertion (visible sim failure), not silently corrupt.

---

### Task 1: Tracking scaffolding (GitHub issue + vault area)

**Files:**
- Create: `vault/tracking/projects/components/utility-ip/converters/task/INDEX.md`, `vault/tracking/projects/components/utility-ip/converters/task/open/TASK-001.md`, plus lifecycle dirs `open/ active/ closed/ dropped/` under `task/`, `bug/`, `issue/`
- Modify: `vault/tracking/INDEX.md` (register the utility-ip area)

**Interfaces:**
- Produces: GitHub issue number referenced by all later commits; vault task ID `utility-ip/converters TASK-001`.

- [ ] **Step 1: File the GitHub issue**

`gh issue create --repo sean-galloway/RTLDesignSherpa --title "feat: AXI3 converters (axi4_to_axi3 / axi3_to_axi4)" --label enhancement` — body: implements spec `docs/superpowers/specs/2026-10-10-axi3-converters-design.md`, first customer DE10 leg-bridge f2h seam, DV BFMs available via RDS-DV #87 (84f9066).

- [ ] **Step 2: Create the vault area mirroring `vault/tracking/rtl/amba/monitors/` structure**

TASK-001.md: priority P2, status ACTIVE, "Done when" = plan Task 11's close-out criteria. `bug/` and `issue/` areas get INDEX.md + empty lifecycle dirs (mirror rtl/amba/monitors).

- [ ] **Step 3: Validate**

Run: `venv/bin/python bin/check_task_ids.py`
Expected: clean (area registered, no ID clashes).

- [ ] **Step 4: Commit**

```bash
git add -- vault/tracking/INDEX.md vault/tracking/projects/components/utility-ip
git commit -m "vault: utility-ip/converters task area + TASK-001 (AXI3 converters)"
```

---

### Task 2: `axi4_to_axi3_rd` pass-through core

**Files:**
- Create: `projects/components/utility-ip/converters/rtl/axi4_to_axi3_rd.sv`
- Create: `projects/components/utility-ip/converters/rtl/filelists/axi4_to_axi3_rd.f`
- Create: `projects/components/utility-ip/converters/dv/tbclasses/axi4_to_axi3_rd_tb.py`
- Create: `projects/components/utility-ip/converters/dv/tests/test_axi4_to_axi3_rd.py`

**Interfaces:**
- Produces: module `axi4_to_axi3_rd` (ports below); TB class `AXI4ToAXI3ReadTB`; test `test_axi4_to_axi3_rd`.
- Port map (downgrade master side — reuse verbatim, `_rd` subset):

```
m_axi3_arid[AXI_ID_WIDTH], m_axi3_araddr, m_axi3_arlen[3:0], m_axi3_arsize[2:0],
m_axi3_arburst[1:0], m_axi3_arlock[1:0], m_axi3_arcache[3:0], m_axi3_arprot[2:0],
m_axi3_aruser, m_axi3_arvalid/arready
m_axi3_rid, m_axi3_rdata, m_axi3_rresp[1:0], m_axi3_rlast, m_axi3_ruser, m_axi3_rvalid/rready
```

Slave side is the AXI4 AR/R port set copied from `axi4_to_axil4_rd.sv:56-78` (8-bit `s_axi_arlen`, 1-bit `s_axi_arlock`, qos/region present on inputs, ignored).

- [ ] **Step 1: Write the failing test** — `test_axi4_to_axi3_rd.py` mirroring `test_axi4_to_axil4_rd.py`'s wrapper mechanics (same `get_sources_from_filelist` call, `dut_name="axi4_to_axi3_rd"`, env-parametrized `AXI_DATA_WIDTH/AXI_ADDR_WIDTH/AXI_ID_WIDTH`). TB: `AXI4MasterRead(prefix="s_axi_")` drives in, `AXI3SlaveRead(prefix="m_axi3_")` responds out. Cocotb test cases: `single_beat_read`, `incr_burst_len16` (16 beats, verify `m_axi3_arlen==15`, no chop, data/resp identity), `fixed_burst`, `lock_map` (drive `s_axi_arlock=1`, check `m_axi3_arlock==2'b10`), `id_preserved`.

- [ ] **Step 2: Run to verify it fails**

Run: `TEST_LEVEL=func PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src venv/bin/python -m pytest projects/components/utility-ip/converters/dv/tests/test_axi4_to_axi3_rd.py -q`
Expected: FAIL (no RTL filelist/module yet — compile error).

- [ ] **Step 3: Implement** `axi4_to_axi3_rd.sv` — v1 scope: `s_axi_arlen ≤ 15` passes through with `m_axi3_arlen = s_axi_arlen[3:0]`; len > 15 is **not yet supported** (assertion `ASSERT_A3_RD_LEN16` fires); R channel is pure pass-through. Drop `arqos/arregion`; map lock per Global Constraints.

- [ ] **Step 4: Run to verify it passes** — same command, Expected: PASS.

- [ ] **Step 5: Gates + commit**

```bash
make -C projects/components/utility-ip/converters/rtl verible
venv/bin/python bin/check_sv_decl_order.py projects/components/utility-ip/converters/rtl/axi4_to_axi3_rd.sv
git add -- <the four files>
git commit -m "feat(converters): axi4_to_axi3_rd pass-through core (#<issue>)"
```

---

### Task 3: `axi4_to_axi3_rd` burst chopping + R merge

**Files:**
- Modify: `projects/components/utility-ip/converters/rtl/axi4_to_axi3_rd.sv`
- Modify: `projects/components/utility-ip/converters/dv/tbclasses/axi4_to_axi3_rd_tb.py`
- Modify: `projects/components/utility-ip/converters/dv/tests/test_axi4_to_axi3_rd.py`

**Interfaces:**
- Consumes: Task 2 module/TB.
- Produces: chopping behavior pinned here; Task 10's loopback relies on it.

- [ ] **Step 1: Write failing tests** — add cases: `incr_burst_len17` (verify two ARs: len 15 then len 0, address step `16<<size`), `incr_burst_len64` (4 chunks), `chop_pipelined` (issue back-to-back chopped ARs; check chunk n+1 AR handshakes before chunk n R completes — count cycles), `resp_merge_slverr_middle` (slave BFM forces SLVERR on chunk 2 of 3, OKAY elsewhere; assert per-beat RRESP passthrough on non-final beats and `RLAST` beat RRESP==SLVERR), `resp_merge_decerr_wins` (DECERR on a middle chunk, SLVERR on the last → assert final beat RRESP==DECERR per the rank order), `multi_id_outstanding` (two IDs chopped concurrently, interleaved R — counters must not cross). FIXED bursts: repeat address per chunk.

- [ ] **Step 2: Run, verify new cases FAIL** (assertion fires on len>15).

- [ ] **Step 3: Implement chopping.** Algorithm (pin exactly):

```
remaining = arlen+1; addr = araddr
loop: chunk=min(remaining,16); issue AR(id,addr,chunk-1,...)
      INCR: addr += chunk<<size ; FIXED: unchanged
      remaining -= chunk
```

Issue next chunk's AR as soon as the previous AR handshakes (no waiting for R). Per-ID merge state `{chunks_left, worst}`; R beats forward as-is except `rlast` suppressed until `chunks_left==1`, whose last beat gets `rresp=worst`. WRAP with len>15 hits the assertion (non-goal 6.3 of the spec).

- [ ] **Step 4: Run, verify PASS.** **Step 5: Gates + commit** (`feat(converters): axi4_to_axi3_rd burst chopping + worst-response merge`).

---

### Task 4: `axi4_to_axi3_wr` pass-through + WID

**Files:**
- Create: `rtl/axi4_to_axi3_wr.sv`, `filelists/axi4_to_axi3_wr.f`, `dv/tbclasses/axi4_to_axi3_wr_tb.py`, `dv/tests/test_axi4_to_axi3_wr.py`

**Interfaces:**
- Produces: `axi4_to_axi3_wr`; W master-side ports add `m_axi3_wid` (W port set: `wid, wdata, wstrb, wlast, wuser, wvalid/ready`); B: `bid, bresp, buser`.

- [ ] **Step 1: Failing test** — `AXI4MasterWrite` in, `AXI3SlaveWrite` out. Cases: `single_write` (`m_axi3_wid==awid` every beat), `burst_len16` (one AW, WLAST only on beat 16), `multi_outstanding_writes` (2 IDs, AW/W/B complete independently), `early_w_data` (drive W before AW handshake accepted; converter must buffer or flow through — pin: W segmentation queue accepts early W up to one full burst, assertion on overflow).

- [ ] **Step 2: Verify FAIL. Step 3: Implement** — v1: len ≤ 15, AW pass-through, W beats stamped `m_axi3_wid = awid` of the owning burst, WLAST forwarded, B pass-through, lock/qos/region as in rd.

- [ ] **Step 4: Verify PASS. Step 5: Gates + commit.**

### Task 5: `axi4_to_axi3_wr` chopping + B absorb/merge

- [ ] **Step 1: Failing tests** — `incr_write_len32` (AW len 31 → two AXI3 AWs len15/len0; W stream: WLAST inserted after beats 16 and 32; `wid` constant), `b_absorb` (slave returns per-chunk B; exactly one `s_axi_bvalid` per AXI4 AW, after last chunk B, `bresp==worst`), `b_merge_decerr_first` (first chunk DECERR, rest OKAY → final DECERR), `chop_early_w` (len-33 burst with W leading AW by several beats).
- [ ] **Step 2: Verify FAIL. Step 3: Implement** — W segmentation: FIFO of chunk descriptors `{wid, beats}` pushed at each (chopped or whole) AW handshake in issue order; W beats forward, counting down, `m_axi3_wlast` forced at descriptor expiry. B side: track outstanding chunks per AW in issue order; absorb Bs 1..n−1, forward one with merged worst.
- [ ] **Step 4: Verify PASS. Step 5: Gates + commit.**

### Task 6: `axi4_to_axi3` top wrapper

**Files:** Create `rtl/axi4_to_axi3.sv`, `filelists/axi4_to_axi3.f`; Modify `dv/tests/conftest.py` only if its filelist-name filter needs the new module (check the `axi4_to_axil4` filter pattern at `dv/tests/conftest.py:65`).

- [ ] **Step 1: Failing test** — `test_axi4_to_axi3.py`: combined rd+wr smoke through the top module.
- [ ] **Step 2: FAIL. Step 3: Implement** — wrapper instantiating `_rd` + `_wr`, full 5-channel port set.
- [ ] **Step 4: PASS. Step 5: Gates + commit.**

### Task 7: `axi3_to_axi4_rd`

**Files:** Create `rtl/axi3_to_axi4_rd.sv`, `filelists/axi3_to_axi4_rd.f`, TB + test (mirror Task 2, sides swapped: `AXI3MasterRead(prefix="s_axi3_")` in, `AXI4SlaveRead(prefix="m_axi_")` out).

- [ ] **Step 1: Failing tests** — `arlen_zeroextend` (4-bit 15 → 8-bit 15), `lock_map_down` (`2'b10→1'b1`, `2'b01→1'b0`, `2'b00→1'b0`), `rid_roundtrip`, `burst_len16_passthrough`, plus len values >15 are unreachable by construction (4-bit input) — no chop logic in this direction.
- [ ] **Step 2: FAIL. Step 3: Implement** — AR/R pass-through with qualifier mapping.
- [ ] **Step 4: PASS. Step 5: Gates + commit.**

### Task 8: `axi3_to_axi4_wr` — WID strip under single-active contract

**Files:** Create `rtl/axi3_to_axi4_wr.sv`, `filelists/axi3_to_axi4_wr.f`, TB + test.

**Interfaces:**
- Produces: single-active-write contract — `m_axi3`... `s_axi3_awready` is deasserted while a write burst is active (AW→W run→B); assertion `ASSERT_A3_WID_STABLE` fires if `s_axi3_wid` changes mid-run or differs from the active AWID. This stricter contract is within spec §3.4; h2f (the customer) does not interleave or pipeline writes.

- [ ] **Step 1: Failing tests** — `wid_stripped` (m_axi W has no id), `single_active_backpressure` (second AW held until first B), `wid_mismatch_asserts` (BFM injects wrong WID mid-run; expect sim failure via assertion), `b_passthrough`.
- [ ] **Step 2: FAIL. Step 3: Implement. Step 4: PASS. Step 5: Gates + commit.**

### Task 9: `axi3_to_axi4` top wrapper

- Mirror Task 6: `rtl/axi3_to_axi4.sv`, `filelists/axi3_to_axi4.f`, combined smoke test. Gates + commit.

### Task 10: Loopback equivalence chain

**Files:** Create `dv/tbclasses/axi3_loopback_tb.py`, `dv/tests/test_axi3_loopback.py`; reuse filelists (new chain filelist `filelists/axi3_loopback.f` referencing both converters).

- [ ] **Step 1: Failing test** — chain: `AXI4MasterRead/Write` → `axi4_to_axi3` → `axi3_to_axi4` → `AXI4SlaveRead/Write` (memory model). Cases: `loopback_identity_len1_to_64` (sweep lengths 1,2,15,16,17,31,32,33,64; data/address/strb identity), `loopback_stall_pattern` (random ready/valid stalls, seeded), `loopback_multi_id` (4 concurrent IDs, len mix). Assertion: received == sent per (id,address).
- [ ] **Step 2: FAIL. Step 3: Implement chain TB. Step 4: PASS. Step 5: Gates + commit.**

### Task 11: Docs, full regression, close-out

**Files:** Modify `docs/` (converters MAS source + regenerate PDF per `docs/generate_mas_pdf.sh` convention used by the converters docs dir); `vault/tracking/projects/components/utility-ip/converters/task/open/TASK-001.md` → closed; GitHub issue.

- [ ] **Step 1: MAS** — add AXI3 converter sections (protocol deltas, chop/merge behavior, single-active contract, non-goals) to the converters MAS source; regenerate the PDF with the dir's `generate_mas_pdf.sh`.
- [ ] **Step 2: Full converters DV regression** — `TEST_LEVEL=func PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src venv/bin/python -m pytest projects/components/utility-ip/converters/dv/tests -q` → all green (no regressions in sibling converters).
- [ ] **Step 3: Final gates** — `make -C projects/components/utility-ip/converters/rtl lint-all`; `venv/bin/python bin/check_sv_decl_order.py` on all six new SV files; `venv/bin/python bin/check_task_ids.py`.
- [ ] **Step 4: Close tracking** — move TASK-001 to `closed/` with resolution notes; comment + close the GitHub issue with the commit list.
- [ ] **Step 5: Commit** (`docs(converters): MAS AXI3 sections; close TASK-001`).

## Self-review notes

- Spec §3.3/§3.4/§4/§5/§6/§7 → Tasks 2–11 cover all; deferred items (§4) are vault-recorded in Task 1's area, not built.
- Step granularity: algorithm bodies appear only for chopping/merge and W segmentation (the spec's "genuinely fiddly" parts); everything else is signatures + test assertions.
- Interface consistency: port map fixed in Task 2 and reused verbatim; TB class names follow `<SRC>To<DST><Rd/Wr>TB`; test files `test_<module>.py` throughout.
- Review Focus items 1–5 map to Tests: multi-ID R (T3), early W (T4), merge leakage (T3/T5), pipelined chunk issue (T3), WID assertion (T8).
