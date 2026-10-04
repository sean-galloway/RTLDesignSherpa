# andesite RTL bootstrap (P0+P1: infrastructure + init slice) — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stand up the andesite RTL infrastructure and prove it end-to-end: `andesite_pkg`, the lint/test scaffolding, and the DDR4 init slice (`dfi_cmd_formatter`, `mode_register`, `init_sequencer`) walking the DFI 4.0 BFM through JEDEC init at the design point.

**Architecture:** Mirrored from scoria — shared `rtl/make/area.mk` lint flow, per-FUB filelists, cocotb+pytest model-first tests dispatched by `make/tests.mk`, DFI BFM from RTLDesignSherpa-DV. The books are design authority: MAS ch02 pages define the three P1 blocks; the kmap book's generated tables are the expected values.

**Tech Stack:** SystemVerilog (Verilator lint + simulation), cocotb + pytest, CocoTBFramework DFI BFM (`DFIVersion.V4_0`), Verible style lint.

**Spec:** `docs/superpowers/specs/2026-10-04-andesite-rtl-bootstrap-design.md` (P0/P1 phases; P2-P4 are follow-on plans). Books: `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_{has,mas}/`.

## Global Constraints

- **Naming:** `andesite_` module/file prefix; `clk`/`rst_n` (active-low sync) in the component tree; `r_`/`w_` internal prefixes. No assertions in RTL — checking lives in DV/formal.
- **AREA names:** `AREA := andesite` (rtl/Makefile); test areas `andesite-fub`, `andesite-macro`, `andesite-top`.
- **Lint flags:** exactly what `rtl/make/area.mk` sets (`--lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal`; verible `--rules_config_search --rules=-parameter-name-style,-line-length`). Do not add suppressions per-module without a comment saying why.
- **Filelists:** `$REPO_ROOT`-absolute paths, `+incdir+` first, one filelist per module under `rtl/filelists/{fub,macro,top}/`, master `rtl/filelists/andesite_all.f`.
- **Timing values:** every ns/nCK in tests comes from the BFM (`timings_from_params` / `jedec/ddr4-1600.csv`), never handwritten numbers (HAS Q1).
- **BFM v4.0 port names:** the v4_0 signal catalog uses `dfi_cs`, `dfi_phy_*_cs`, `dfi_wrdata_cs`, `dfi_rddata_cs` — **no `*_cs_n`** (TASK-005 study). RTL DFI port names must match the catalog or the slave bind fails.
- **P1 is DDR4-only.** LPDDR4 paths (CA submodule encodings, MPC, per-bank refresh, inline CKE) are deferred stubs at most — no half-built branches. `memtype_i` exists as a port; only the DDR4 value is exercised.
- **BFM tests need `PYTHONPATH=$RDS_DV/src`** (the venv carries a shadowing installed copy of CocoTBFramework; `$RDS_DV` = `/mnt/data/github/RTLDesignSherpa-DV`).
- **Truth-table authority:** the DDR4 command encodings in `docs/kmaps/generated/01_ddr4_command_table.md` are the expected values for the formatter (anchor: MAS `ch02_blocks/01_cmd_formatter.md` Table 2.3).
- Commit prefix `feat(andesite):`; one commit per task; `python3 bin/check_task_ids.py` PASS before every commit.

## Review Focus

1. **Init-order violations must fail loudly** — the checker asserts the *sequence* (RESET# window, CKE discipline, MR3→MR6→MR5→MR4→MR2→MR1→MR0, ZQCL, tDLLK/tZQinit expiry), not the outcome; a DRAM that "came up" in the wrong order must be a red test.
2. **BFM v4.0 renames** — a testbench written against v3.1 habits (`dfi_cs_n`, `phylvl_req_cs_n`) compiles against nothing; the first BFM-bind failure mode is an AttributeError on signal names, and the fix is never to alias back to the old names.
3. **Timing provenance** — a test that handwrites `tRFC = 160` can pass against a DRAM model that also hardcodes it; the BFM must get its timings from `timings_from_params(**jedec profile)` so the RTL is checked against the same numbers the books cite.
4. **AP is an address input, not a pin** — RDA/WRA/PREA/ZQCL are the same pin encodings as RD/WR/PRE/ZQ with A10=1; a formatter that burns pin rows on the auto-precharge variants breaks the kmap anchor's input model (Task 3's tests pin this).
5. **CSR-vs-constant drift in the init FSM** — the sequencer's wait states count CSR-loaded values; a wait state that falls back to a compiled-in constant will pass at one speed bin and lie at another (Task 5's tests pin this).

---

## File Structure

- `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/Makefile` — 4-line AREA include (mirrors scoria's).
- `rtl/includes/andesite_pkg.sv` — memtype enum (3-bit family design), `dram_op_e` (carried 16 + `OP_MPC`), `decoded_addr_t`, helpers (carried `is_*` functions + `has_auto_pre`).
- `rtl/fub/andesite_dfi_cmd_formatter.sv`, `rtl/fub/andesite_mode_register.sv`, `rtl/fub/andesite_init_sequencer.sv` — the P1 blocks, to the MAS pages.
- `rtl/fub/andesite_smoke.sv` — infra smoke module (Task 1); deleted in P4's cleanup.
- `rtl/filelists/andesite_all.f` + `fub/`, `macro/`, `top/` subtrees.
- `dv/tests/{fub,macro,top}/{Makefile,conftest.py}` — AREA dispatchers mirroring scoria.
- `dv/tests/fub/test_andesite_dfi_cmd_formatter.py`, `test_andesite_mode_register.py`, `test_andesite_init_sequencer.py`; `dv/tbclasses/andesite_{dfi_cmd_formatter,mode_register,init_sequencer}_tb.py`.
- `dv/tests/macro/test_andesite_init_slice.py`; `dv/tb/andesite_init_tb.sv`; `dv/filelists/andesite_init_tb.f`; `dv/tbclasses/andesite_init_tb.py` — the P1 BFM integration.

---

### Task 1: P0 scaffolding — tree, package, filelists, lint smoke

**Files:**
- Create: `rtl/Makefile`, `rtl/includes/andesite_pkg.sv`, `rtl/fub/andesite_smoke.sv`, `rtl/filelists/andesite_all.f`, `rtl/filelists/fub/andesite_smoke.f`
- Test: `make verible` + `make verilator-andesite_smoke` green

**Interfaces:**
- Produces: `andesite_pkg` (memtype enum `MEMTYPE_DDR4 = 3'b010`, `MEMTYPE_LPDDR4 = 3'b110` per family doc 01; `dram_op_e` = scoria's 16 values verbatim plus `OP_MPC = 4'h10` needs a 5th bit — use `logic [4:0]` and carried values unchanged; `decoded_addr_t` with `bg` field added between `rank` and `bank`: `rank[3:0], bg[3:0], bank[3:0], row[17:0], col[13:0]`; helpers `is_column_op/is_write_op/is_read_op/is_refresh_op/has_auto_pre/is_zq_op` carried unchanged). Later tasks import this package by `import andesite_pkg::*;`.

- [ ] **Step 1: Create the tree and the 4-line Makefile**

`rtl/Makefile` exactly mirrors scoria's: `AREA := andesite`, `RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))`, `include $(RDS_ROOT)/rtl/make/area.mk`. Create `rtl/{fub,macro,top,includes,filelists/{fub,macro,top}}` directories.

- [ ] **Step 2: Write the failing lint**

Create `rtl/fub/andesite_smoke.sv` (a module that imports `andesite_pkg` and references `OP_ACT` in a wire — 6 lines) and `rtl/filelists/fub/andesite_smoke.f` (mirror scoria's cmd_arbiter filelist shape: `+incdir+` the includes dir, then `andesite_pkg.sv`, then the module). Master `rtl/filelists/andesite_all.f` `-f`-includes the smoke filelist.

Run: `cd projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl && make verilator-andesite_smoke`
Expected: FAIL — `andesite_pkg.sv` doesn't exist yet (package not found).

- [ ] **Step 3: Implement `rtl/includes/andesite_pkg.sv`**

Per the Interfaces block. The package header comment cites family doc 01 for the memtype design and `scoria_pkg.sv` as the carried-opcodes source. `OP_MPC` gets value `5'h10` with a comment (LPDDR4 breadth consumes it later; encoding on the CA bus is the kmap table's business).

- [ ] **Step 4: Run lint green**

Run: `make verilator-andesite_smoke && make verible`
Expected: PASS, no warnings new relative to scoria's baseline.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl
git commit -m "feat(andesite): P0 scaffolding -- rtl tree, andesite_pkg, filelists, lint smoke"
```

### Task 2: DV scaffolding — test dispatchers and a cocotb smoke run

**Files:**
- Create: `dv/tests/fub/{Makefile,conftest.py}`, `dv/tests/macro/{Makefile,conftest.py}`, `dv/tests/top/{Makefile,conftest.py}`, `dv/tests/fub/test_andesite_smoke.py`
- Consumes: Task 1's `andesite_smoke` filelist.

**Interfaces:**
- Produces: the dispatcher convention later tasks copy: per-area `Makefile` (4 lines: `AREA := andesite-fub` / `andesite-macro` / `andesite-top`, same RDS_ROOT/include lines as scoria's), `conftest.py` wiring `../../` (tbclasses) and `$REPO_ROOT/bin` onto `sys.path`, and the pytest-runner pattern from scoria's `test_scoria_cmd_arbiter.py` (`get_sources_from_filelist` + `run(python_search=[...], simulator="verilator", compile_args=["+define+USE_ASYNC_RESET"], timescale="1ns/1ps")`).

- [ ] **Step 1: Write the failing test**

`test_andesite_smoke.py`: a cocotb test that toggles `clk`, asserts `rst_n` low holds `dut.out_o == 0`, releases reset, ticks 5 clocks, asserts `out_o == 1` — against `andesite_smoke` extended with that behavior (Task 1's module may need the two ports added; that edit lands here, in this task, as part of the test-driven change).

Run: `cd dv/tests/fub && make run-andesite_smoke-func`
Expected: FAIL — no dispatcher/Makefile yet (`make` target missing).

- [ ] **Step 2: Create the dispatchers**

The three Makefiles + three conftest.py files mirroring scoria's (read scoria's `dv/tests/fub/{Makefile,conftest.py}` and copy with `scoria` → `andesite`).

- [ ] **Step 3: Run green**

Run: `make run-andesite_smoke-func`
Expected: PASS (cocotb + verilator pipeline works end-to-end).

- [ ] **Step 4: Commit**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/dv
git commit -m "feat(andesite): DV scaffolding -- test dispatchers and cocotb smoke"
```

### Task 3: `andesite_dfi_cmd_formatter` — the DDR4 truth table at the pins

**Files:**
- Create: `rtl/fub/andesite_dfi_cmd_formatter.sv`, `rtl/filelists/fub/andesite_dfi_cmd_formatter.f`, `dv/tbclasses/andesite_dfi_cmd_formatter_tb.py`, `dv/tests/fub/test_andesite_dfi_cmd_formatter.py`
- Consumes: Task 1's package (`dram_op_e`, `decoded_addr_t`, helpers); Task 2's runner.
- Design authority: MAS `ch02_blocks/01_cmd_formatter.md` (ports in Table 2.2; truth table Table 2.3 — the anchor).

**Interfaces:**
- Produces: module `andesite_dfi_cmd_formatter` with the MAS Table 2.2 ports (`clk`, `rst_n`, `op_i` as `dram_op_e` plus a separate `mpc_op_i` qualifier — or an `op_i` widened to the 5-bit enum; pick the 5-bit enum, MAS Table 2.2's `op_i` width updates in-book at Task 6), `bank_i`, `bg_i`, `row_i`, `col_i`, `rank_i`, `memtype_i`, `parity_en_i`, DFI outputs `dfi_cs`, `dfi_act_n`, `dfi_ras_n`, `dfi_cas_n`, `dfi_we_n`, `dfi_bank`, `dfi_bg`, `dfi_address`, `dfi_cke`, `dfi_parity_in`. **v4.0 names: `dfi_cs`, no `*_cs_n`.** Later tasks and the P1 TB bind these names.
- Produces (tests): `test_andesite_dfi_cmd_formatter.py` with parametrized cases per anchored command.

- [ ] **Step 1: Write the failing tests**

Testbench class drives `op_i`/`bank_i`/`bg_i`/`row_i`/`col_i`/`rank_i`, samples the DFI pins after the registered pipeline latency the MAS Timing section states. Cases, expected values from `docs/kmaps/generated/01_ddr4_command_table.md` (which derives from the anchor): NOP→`cs=0, act_n=1, ras_n=1, cas_n=1, we_n=1`; ACT→`0,1,1,1` with `bg_i` on `dfi_bg` and `row_i` on `dfi_address`; RD→`1,1,0,1`; WR→`1,1,0,0`; MRS→`0,0,0,0` with `col_i` (MR number in `bank_i`, data in `address` — per MAS Table 2.2 semantics); REF→`0,0,0,1`; PRE with `col_i[10]=0` vs PREA `col_i[10]=1`→same pins, address bit differs; ZQCS/ZQCL likewise on A10. AP-invariant case: RDA is RD pins with `col_i[10]=1` — assert no pin change vs RD. Parity case: with `parity_en_i=0`, `dfi_parity_in` constant 0; with `parity_en_i=1` and a known command+address, parity is the XOR per MAS §CA parity (cite the MAS section; if the MAS leaves the polynomial unspecified, assert "parity differs between two commands differing in one address bit" — functional, not a fabricated polynomial).

Run: `make run-andesite_dfi_cmd_formatter-func`
Expected: FAIL — module doesn't exist.

- [ ] **Step 2: Implement `andesite_dfi_cmd_formatter.sv`**

Combinational decode per the anchor (the kmap SOPs are the minimal cover; write the decode readable — the generator will diff `rtl_sop` against the cover at Task 6 and that verdict is allowed to say the RTL is redundant *if* a comment says why) plus one registered pipeline stage; ACT packing per the MAS activate form; parity generation qualified by `parity_en_i`. LPDDR4 (`memtype_i != MEMTYPE_DDR4`): drive the DDR4 pins to the NOP/DES-idle posture and leave the CA bus outputs tied off with a `// TASK-008 follow-on` note — no half-built branch.

- [ ] **Step 3: Run green**

Run: `make run-andesite_dfi_cmd_formatter-func`
Expected: PASS.

- [ ] **Step 4: Lint + commit**

Run: `make verilator-andesite_dfi_cmd_formatter && make verible`
```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/dv
git commit -m "feat(andesite): dfi_cmd_formatter -- DDR4 truth table, ACT packing, parity qualify"
```

### Task 4: `andesite_mode_register` — MR0-MR6 images per memtype

**Files:**
- Create: `rtl/fub/andesite_mode_register.sv`, `rtl/filelists/fub/andesite_mode_register.f`, `dv/tbclasses/andesite_mode_register_tb.py`, `dv/tests/fub/test_andesite_mode_register.py`
- Consumes: Task 1 package; Task 2 runner.
- Design authority: MAS `ch02_blocks/03_mode_register.md` (semantics tables; MR2 carries RTT_WR per the review fix; MR5 carries CA parity + DBI + RTT_PARK).

**Interfaces:**
- Produces: module `andesite_mode_register` with MAS Table 2.6's port set: `clk`, `rst_n`, `memtype_i`, write port (`mr_wr_i`, `mr_sel_i[2:0]`, `mr_data_i[7:0]`), readback (`mr_sel_i`, `mr_data_o[7:0]`, `mr_rdy_o` registered read), and the block outputs the MAS coupling table names: `fgr_factor_o[1:0]`, `mpr_page_o`, `ca_parity_lat_o`, `lpddr4_odt_o`, `rtt_nom_o`, `rtt_wr_o`, `rtt_park_o`, `dbi_rd_o`, `dbi_wr_o`, `gear_down_o`. Later: init_sequencer consumes the write port; odt_ctrl/datapath consume the images.

- [ ] **Step 1: Write the failing tests**

Cases from the MAS field semantics (bit positions per JESD79-4 stay out of the DUT — the block stores 8-bit images per MR and derives the *named* outputs; tests assert the derivation): write MR3 with FGR select encoding 1→`fgr_factor_o==1`, 2→`2`, 4→`3` (the MAS map's encoding); write MR5 with CA-parity-latency nonzero →`ca_parity_lat_o` mirrors it; RTT images mirror MR1/MR2/MR5 fields; reset clears all images to the MAS reset column; readback returns the last written image for the selected MR; write-then-read for MR0..MR6 round-trips.

Run: `make run-andesite_mode_register-func` — Expected: FAIL (no module).

- [ ] **Step 2: Implement `andesite_mode_register.sv`**

Seven 8-bit image registers (MR0-MR6) + the LPDDR4 image bank as a second array (written via the same port when `memtype_i==MEMTYPE_LPDDR4`, semantics per the MAS LPDDR4 section); derived outputs as pure functions of the images per the MAS coupling table. No bit-position inventing: derivations are wiring + tiny functions the MAS semantics pin.

- [ ] **Step 3: Run green + lint + commit**

```bash
make run-andesite_mode_register-func && make verilator-andesite_mode_register
git commit -m "feat(andesite): mode_register -- MR0-MR6 images per memtype, derived policy outputs"
```

### Task 5: `andesite_init_sequencer` — the FSM and the order checker

**Files:**
- Create: `rtl/fub/andesite_init_sequencer.sv`, `rtl/filelists/fub/andesite_init_sequencer.f`, `dv/tbclasses/andesite_init_sequencer_tb.py`, `dv/tests/fub/test_andesite_init_sequencer.py`
- Consumes: Tasks 3-4 (formatter + mode_register instances are wired in the TB, not the DUT — the sequencer drives `op_i` etc. as outputs).
- Design authority: MAS `ch02_blocks/02_init_sequencer.md` (the DDR4 FSM state-list fence; sequencing rules; the Task-006 recovery section stays out of P1 scope — note it as a follow-on, not a stub).

**Interfaces:**
- Produces: module `andesite_init_sequencer` with ports per the MAS interface section: `clk`, `rst_n`, command request outputs (`cmd_op_o` as the 5-bit enum, `cmd_bank_o`, `cmd_addr_o`, `cmd_valid_o`, `cmd_ready_i`), MR write port (matching Task 4's write-side names), `reset_n_o` (to the top-level/PHY), `cke_o`, `init_done_o`, `init_err_o`, CSR timing inputs (`tinit1_i`, `tinit3_i`, `tinit4_i`, `tdllk_i`, `tzqinit_i`, `tmrd_i`, `tmod_i` — widths per the MAS Parameters table), `gear_down_en_i`, and mode-register readback inputs needed for the MR-dependency checks the MAS states name. The P1 TB (Task 6) wires this to Tasks 3-4.

- [ ] **Step 1: Write the failing order-checker test**

The HAS ch06 item-1 checker, procedurally: record every (cycle, op, bank, address) the DUT issues into a list; on `init_done_o`, assert the recorded sequence equals the MAS anchor order — RESET#-assert window ≥ `tinit1_i` cycles, CKE raised only after the `tinit3_i` wait, CKE continuous thereafter, first MRS at MR3 and the full MR3→MR6→MR5→MR4→MR2→MR1→MR0 order with `tmod_i`/`tmrd_i` gaps, ZQCL last, `init_done_o` only after `tdllk_i` and `tzqinit_i` from ZQCL. Inject one fault case (testbench forces `cmd_ready_i` low for one cycle mid-MRS) to prove the checker can go red. Also a wait-state CSR case: run twice with different `tinit3_i` values and assert the observed CKE cycle moves — pins Review Focus 5.

Run: `make run-andesite_init_sequencer-func` — Expected: FAIL (no module).

- [ ] **Step 2: Implement `andesite_init_sequencer.sv`**

The FSM states per the MAS fence; wait states count CSR-loaded values (counters loaded from the CSR inputs at entry — no compiled-in constants); the gear-down branch as the MAS lists it, gated `gear_down_en_i`; `init_err_o` on timeout (CSR-settable watchdog, MAS Timing section) — never block forever.

- [ ] **Step 3: Run green + lint + commit**

```bash
make run-andesite_init_sequencer-func && make verilator-andesite_init_sequencer
git commit -m "feat(andesite): init_sequencer -- DDR4 init FSM, JEDEC order, CSR waits"
```

### Task 6: P1 gate — the init slice walks the DFI 4.0 BFM

**Files:**
- Create: `dv/tb/andesite_init_tb.sv`, `dv/filelists/andesite_init_tb.f`, `dv/tbclasses/andesite_init_tb.py`, `dv/tests/macro/test_andesite_init_slice.py`
- Modify: `docs/kmaps/gen_andesite_kmaps.py` (CITES re-point, one path constant), MAS `ch02_blocks/01_cmd_formatter.md` Table 2.2 `op_i` width note, HAS `ch00_front_matter/00_document_info.md` (revision row), MAS `ch00_front_matter/00_document_info.md` (revision row)
- Consumes: Tasks 3-5; the BFM (`PYTHONPATH=$RDS_DV/src`).

**Interfaces:**
- Produces: the P1 evidence — BFM walk-through green; the generator's formatter citations re-pointed (CITES entries for `01_cmd_formatter.md` lines 91/93/101 move to the `.sv` lines implementing the truth table; lines 143/152 stay MAS-anchored — the CA submodule is deferred); book revision rows recording the RTL landing.

- [ ] **Step 1: Write the failing integration test**

`dv/tb/andesite_init_tb.sv`: toplevel `andesite_init_tb` instantiating Tasks 3-5 (sequencer → formatter → DFI pins out; mode_register on the MR port) — no AXI, no datapath; `dv/tbclasses/andesite_init_tb.py`: build `DFIBase(dfi_version=DFIVersion.V4_0, memory_type=MemoryType.DDR4, timings=timings_from_params(**jedec profile), ...)` and `DFISlavePHY(...)` mirroring scoria's `scoria_core_tb.py` pattern (lines ~147-191) but v4_0/DDR4; jedec profile from the BFM's `jedec/ddr4-1600.csv` (load it the way the DV repo's own tests load vendored CSVs — find one and mirror it). Test: run init; assert `init_done_o`; assert the BFM's DRAM state model reports init complete and **zero violations** under its default `ViolationPolicy`; assert the recorded command stream matches the MAS order (reuse the Task 5 checker logic via a shared helper in `dv/tbclasses/`).

Run: `cd dv/tests/macro && PYTHONPATH=$RDS_DV/src make run-andesite_init_slice-func`
Expected: FAIL first against a trivially-wrong assertion (e.g. assert `init_done_o` within 1 cycle) to prove the harness observes the DUT, then the real assertions.

- [ ] **Step 2: Run the walk-through green**

Expected: init completes at the design point with zero BFM violations.

- [ ] **Step 3: Gear-down configuration**

Parametrize the test with `gear_down_en_i=1`; assert the BFM (G3-closed geardown support) validates the `dfi_geardown_en` entry sequence and both CA rates. If the BFM's geardown modeling exposes a protocol dispute, resolve against the spec PDF (`/mnt/data/github/dfi-specs/DDR_PHY_Interface_Specification_v4_0.pdf` §3.13/§4.18) — a BFM bug is a DV-repo fix commit, never a loosened assertion (record it in the commit message).

- [ ] **Step 4: Re-point the kmap citations**

In `gen_andesite_kmaps.py`: change the `CMD` constant for the three truth-table CITES (currently MAS lines 91/93/101) to `rtl/fub/andesite_dfi_cmd_formatter.sv` with the actual line numbers of the decode (read the file, pin the lines), snippets quoted from the RTL. Keep the two CA-placeholder CITES on the MAS lines. Rerun the generator: exit 0, and the workbook's formatter sheet now cites RTL (the `rtl_sop` verdicts become meaningful — a DIFFERS verdict is acceptable at this gate only if the commit message says why; IDENTICAL is the goal).

- [ ] **Step 5: Book revision rows**

HAS ch00 revision table: add row 0.2 (2026-10-04) — "P1 RTL landed: formatter, mode_register, init_sequencer; init slice walks the DFI 4.0 BFM at DDR4-1600 with zero violations; kmap citations for the command decode re-pointed at RTL." MAS ch00 revision table: add the matching row, status updated from "no RTL exists". MAS `01_cmd_formatter.md` Table 2.2: `op_i` width note corrected to the 5-bit enum with the RTL citation.

- [ ] **Step 6: Full gate + commit**

Run: `python3 bin/check_task_ids.py`; the generator rerun; `make lint-all` in the andesite rtl dir.
```bash
git add -A projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4
git commit -m "feat(andesite): P1 gate -- init slice walks DFI 4.0 BFM; kmap citations at RTL lines"
```

---

## Self-Review notes

- Spec coverage: P0 → Tasks 1-2; P1 → Tasks 3-6. P2-P4 explicitly deferred to follow-on plans (spec §3). Deferred lists untouched.
- Review Focus 1 → Task 5 Step 1 (order checker + injected fault). Focus 2 → Task 6 Step 1 (v4.0 names enforced by construction; BFM bind fails otherwise). Focus 3 → Task 6 Step 1 (timings from the 1600 CSV). Focus 4 → Task 3 Step 1 (AP-invariant case). Focus 5 → Task 5 Step 1 (wait-state CSR case).
- Interface consistency: `dram_op_e` 5-bit decision made once (Task 1) and consumed consistently (Task 3 decode input, Task 5 `cmd_op_o`, Task 6 wiring); MR write-port names defined in Task 4 and consumed by Task 5's port list; DFI pin names (`dfi_cs`, no `_cs_n`) fixed in Global Constraints and Tasks 3/6.
- Proportion: bodies appear only where the books leave a choice (smoke module, checker structure); block internals are cited to MAS pages, not transcribed.
