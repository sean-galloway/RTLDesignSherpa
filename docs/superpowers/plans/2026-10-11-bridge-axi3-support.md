# Bridge AXI3 Port Support — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The bridge generator accepts `protocol = "axi3"` on master and slave ports, emitting AXI3 external surfaces that convert to the internal AXI4 fabric at the boundary via the proven converter suite.

**Architecture:** Boundary conversion — AXI3 exists only on external pins; `axi3_to_axi4` (masters) / `axi4_to_axi3` (slaves) instantiate inside the generated adapters, exactly where `apb4_to_axi4` / `axi4_to_axil4` sit today. The crossbar core never sees AXI3.

**Tech Stack:** Python 3 generator (`bridge_pkg`), SystemVerilog emit, cocotb + RDS-DV BFMs, pytest, verible / decl-order gates.

**Spec:** `docs/superpowers/specs/2026-10-11-bridge-axi3-support-design.md` — this plan argues from it; read both. Tracking: GitHub `sean-galloway/RTLDesignSherpa#97`.

## Global Constraints

- Any cocotb run: `PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src` (shadows the installed framework; the AXI3 BFMs live there).
- Declaration-order gate on every generated `.sv`: `venv/bin/python bin/check_sv_decl_order.py <file>` from repo root.
- Verible lint on every generated/touched `.sv`, matching the invocation the converters flow uses.
- **Never modify converter RTL** (`projects/components/utility-ip/converters/rtl/*`) — spec non-goal. Bridge adapts to the converters as they are.
- Shared tree: commit by explicit pathspec only; never `checkout`/`stash`/`reset`; on HEAD-lock wait 5 s and retry. Pre-commit runs `check_task_ids` + broken-links — do **not** add vault task files; tracking is GitHub #97.
- Comment style in the generator cites the tracker: `bridge GitHub #97`.
- Reference fixtures/commands below use `projects/components/fabric-gen-ip/bridge/` as the working area; generator CLI: single-config mode is `--ports <toml> --connectivity <csv> --name <n>`, suite mode is `--bulk bridge_batch.csv --generate-tests`.

## Review Focus

1. **Interleaved W data from an AXI3 master** (input: W beats of two IDs alternating before WLAST). Converter contract requires one ID until WLAST, assertion-checked. A reasonable person expects the bridge docs to state this master obligation — pinned by the Task 6 ordered-multi-ID test (positive contract) and the Task 7 HAS restatement.
2. **AXI4 master issuing >16-beat bursts to an AXI3 slave** (input: AWLEN > 15 toward the AXI3 slave). `axi4_to_axi3` chops by address regeneration and must return one B with worst-response; data must round-trip. Generated smoke tests use short bursts — pinned by the Task 6 chunk test.
3. **Width-mismatched AXI3 master** (input: 64-bit-wide bursts from a 32-bit AXI3 master port on a 64-bit fabric). Converter is same-width; adaptation happens on the internal AXI4 side. Pinned by the Task 6 wide-burst test on `bridge_2x2_axi3_masters`.
4. **Same-ID ordering with multiple outstanding reads from an AXI3 master** (input: 4 outstanding ARs, one ID). AXI3 ordering guarantees must survive the fabric. Pinned by the Task 6 multi-outstanding test on `bridge_1x2_axi3`.
5. **Exclusive transfer from an AXI3 master** (input: AxLOCK = `10`). Converter maps to 1-bit exclusive; bridge passes through, response OKAY. Pinned by the Task 6 lock-mapping test (with directed-drive fallback if the AXI3 BFM lacks lock control).

---

### Task 1: Validator accepts `axi3` with AXI3 rules

**Files:**
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/config_validator.py` (`valid_protocols` at :71; add `validate_axi3`; dispatch next to `validate_axi5`)
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/config_loader.py` (:205 area — verify the `axi5_features` protocol gate rejects `axi3`; extend only if it whitelists protocols)
- Test: `projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py`
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_zero_id.toml` (+ its `_connectivity.csv`)
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_bad_width.toml` (+ csv)
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_cdc.toml` (+ csv)
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_axi5_features.toml` (+ csv)

**Interfaces:**
- Consumes: existing `validate_protocol`, `validate_axi5` (:124), the `PortSpec` attrs (`protocol`, `id_width`, `data_width`, `cdc`, `axi5_features`).
- Produces: `validate_axi3(masters: List[PortSpec], slaves: List[PortSpec]) -> None` raising `ValueError` with message prefix `"AXI3 port '..."`; called from the same dispatch point as `validate_axi5`. Later tasks rely on `'axi3'` passing validation.

- [ ] **Step 1: Write the failing tests**

In `bin/tests/test_generator_pkg.py`, mirror the existing `test_illegal_apb_write_config_rejected` (:53) four times: `_fixture("test_illegal_axi3_zero_id.toml")` etc., each asserting `ValueError` from the generator entry the existing tests call. Add two positive unit tests calling `validate_axi3` directly with a legal AXI3 master (id_width=4, data_width=64) + AXI3 slave, expecting no raise; and asserting `validate_axi5` still rejects `axi5_features` on an `axi3` port. Fixture shapes: copy `test_illegal_apb_wr.toml` and change the offending field — zero-id master omits `id_width`; bad-width uses `data_width = 16`; cdc sets `cdc = true` on the AXI3 slave; axi5-features adds `axi5_features = ["trace"]`.

- [ ] **Step 2: Run to verify failure**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && python3 -m pytest tests/test_generator_pkg.py -v`
Expected: the four negative tests FAIL — generator either rejects `axi3` outright ("Must be one of {...}") or accepts it without the new rules (zero-id/bad-width/cdc) — and the axi5-features test fails if `config_loader` needs the extension.

- [ ] **Step 3: Implement**

In `config_validator.py`: add `'axi3'` to `valid_protocols` (:71). Add `validate_axi3` enforcing: AXI3 master with `id_width` falsy → `ValueError("AXI3 master '<name>': id_width must be > 0")`; any AXI3 port with `data_width` not in `{32, 64, 128, 256}` → `ValueError` naming the port and the legal set; any AXI3 port with truthy `cdc` → `ValueError("AXI3 port '<name>': CDC is not supported (v1)")`. Wire it into the validation dispatch beside `validate_axi5`. In `config_loader.py`, extend the :205 `axi5_features` protocol check to also fire for `axi3` if it currently whitelists; otherwise leave (the validator test proves which).

- [ ] **Step 4: Run to verify pass**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && python3 -m pytest tests/test_generator_pkg.py -v`
Expected: all tests PASS, including the pre-existing ones (no regression).

- [ ] **Step 5: Commit**

```bash
git add projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/config_validator.py projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/config_loader.py projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_zero_id.toml projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_zero_id_connectivity.csv projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_bad_width.toml projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_bad_width_connectivity.csv projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_cdc.toml projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_cdc_connectivity.csv projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_axi5_features.toml projects/components/fabric-gen-ip/bridge/bin/test_configs/test_illegal_axi3_axi5_features_connectivity.csv
git commit -m "feat(bridge): validator accepts axi3 with AXI3-specific rules (GitHub #97)"
```

---

### Task 2: Master-side AXI3 front end (`axi3_to_axi4`)

**Files:**
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/generators/adapter_generator.py` (`FRONT_END_CONV` :437; `_generate_external_ports` :314 branch; front-end instantiation `_generate_apb_front_end` :549; audit `is_front_end_master` :445 / `is_apb_master` :449 / `front_end_prefix` :453 consumers)
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/components/bridge_module_generator.py` (`_generate_master_ports` — add the `axi3` branch)
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_1x2_axi3.toml`
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_1x2_axi3_connectivity.csv`
- Test: `projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py` (generation assertions)

**Interfaces:**
- Consumes: Task 1's validator (`axi3` passes). `FRONT_END_CONV` map :437; converter module name `axi3_to_axi4` with params `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `AXI_DATA_WIDTH`, `AXI_USER_WIDTH` (no width conversion — spec §3.5).
- Produces: emitted master adapter with external AXI3 surface (`{prefix}awlen[3:0]`, `{prefix}arlen[3:0]`, `{prefix}wid`, 2-bit `awlock`/`arlock`, **no** `qos`/`region`) and a `u_axi3_front_end : axi3_to_axi4` instance. `bridge_1x2_axi3.{toml,csv}` fixtures reused by Tasks 3–6.

- [ ] **Step 1: Write the fixture + failing test**

Create `bridge_1x2_axi3.toml`: one rw master `cpu` (`protocol = "axi3"`, id_width=4, data_width=64, addr_width=32) and two slaves — `s0` AXI3 (protocol = "axi3", id_width=5 per the existing master-index-bit comment convention) and `s1` AXI4, 64-bit, `base_addr`/`addr_range` non-overlapping. Connectivity CSV: master reaches both slaves (`master\slave,s0,s1` / `cpu,1,1`). In `test_generator_pkg.py`, add a test that generates this config into `tmp_path` (mirror the generation call the existing positive tests use) and asserts: `"axi3_to_axi4"` in the emitted master-adapter SV, `wid` in the top-level port list, and `awlen` declared 4-bit wide there.

- [ ] **Step 2: Run to verify failure**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && python3 -m pytest tests/test_generator_pkg.py -k axi3 -v`
Expected: FAIL — no AXI3 surface or instance emitted yet.

- [ ] **Step 3: Implement**

`adapter_generator.py`: `FRONT_END_CONV['axi3'] = 'axi3_to_axi4'`. In `_generate_external_ports` (:314), route `protocol == 'axi3'` to a new `_generate_axi3_external_ports()` that mirrors the wb4 full-bus pattern (:456) but emits the AXI3 signal set — 4-bit `awlen`/`arlen`, `wid` on W, 2-bit `awlock`/`arlock`, and qos/region omitted (the AXI4 signal-info list minus those). Grep every consumer of `is_front_end_master` / `is_apb_master` / `front_end_prefix` and make each treat `axi3` as a front-end master (the nets between converter and timing wrapper are the standard AXI4 list at port width — same as wb4's post-conversion side, so wb4's net-declaration shape is the model). Extend the front-end instantiation (:549) to emit `u_axi3_front_end` with the converter's four `AXI_*_WIDTH` params bound from the master config. `bridge_module_generator.py`: add the `axi3` branch to `_generate_master_ports` delegating to the same AXI3 external-port emitter.

- [ ] **Step 4: Run test + lint gates**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && python3 -m pytest tests/test_generator_pkg.py -k axi3 -v` — PASS.
Then generate for real: `python3 bridge_generator.py --ports test_configs/bridge_1x2_axi3.toml --connectivity test_configs/bridge_1x2_axi3_connectivity.csv --name bridge_1x2_axi3` and run the decl-order gate + verible on every emitted `.sv` (adapter, top, crossbar). Expected: clean. (Generation succeeds here because Task 1 made `axi3` legal; sim is Task 6, after filelists land in Task 4.)

- [ ] **Step 5: Commit**

```bash
git add projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/generators/adapter_generator.py projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/components/bridge_module_generator.py projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_1x2_axi3.toml projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_1x2_axi3_connectivity.csv projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_1x2_axi3 rtl/filelists
git commit -m "feat(bridge): AXI3 master front end via axi3_to_axi4 (GitHub #97)"
```

(Adjust the generated-path pathspec to what the generator actually writes; `rtl/filelists` picks up the new `.f`.)

---

### Task 3: Slave-side AXI3 converter path (`axi4_to_axi3`)

**Files:**
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/generators/slave_adapter_generator.py` (branches in `generate()` :103, `_generate_external_interface_ports()` :346, `_generate_internal_signals()` :583; new `_generate_axi3_external_ports()` + `_generate_axi3_converter()`)
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/components/bridge_module_generator.py` (`_generate_slave_ports` — `axi3` branch)
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/config_validator.py` (`validate_slave_id_widths` :341 — include `'axi3'`)
- Test: `projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py`

**Interfaces:**
- Consumes: `bridge_1x2_axi3` fixtures (Task 2) — its `s0` is AXI3. `_generate_axil_converter()` (:126 dispatch) as the structural model for a `_rd`/`_wr`-pair converter path.
- Produces: slave adapter emitting external AXI3 slave surface + `u_axi3_converter : axi4_to_axi3` between the `axi4_master_*` timing wrapper and the pins; id-width rule now enforced for AXI3 slaves (id_width ≥ master-index-prefixed width).

- [ ] **Step 1: Write the failing test**

Extend the Task 2 generation test: assert `"axi4_to_axi3"` in the emitted slave-adapter SV for the AXI3 slave, `wid` present on its W port, and a `ValueError` from `validate_slave_id_widths` when the AXI3 slave's `id_width` is under-width (set id_width=1 in a copied spec, expect the existing "Set id_width = ..." message).

- [ ] **Step 2: Run to verify failure**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && python3 -m pytest tests/test_generator_pkg.py -k axi3 -v`
Expected: FAIL on the new assertions (no converter emitted; under-width AXI3 slave currently skipped by the `:341` protocol filter).

- [ ] **Step 3: Implement**

`slave_adapter_generator.py`: add `'axi3'` to the three dispatch points (`generate()`, `_generate_external_interface_ports()`, `_generate_internal_signals()` :583 list). `_generate_axi3_external_ports()` emits the slave-direction AXI3 set (4-bit `awlen`/`arlen`, `wid`, 2-bit lock, no qos/region). `_generate_axi3_converter()` mirrors `_generate_axil_converter()` but instantiates the single top wrapper `axi4_to_axi3` with `.AXI_ID_WIDTH(s.id_width)`, `.AXI_ADDR_WIDTH`, `.AXI_DATA_WIDTH`, `.AXI_USER_WIDTH`; bridge-ID tracking pops on the crossbar-side AXI4 handshake exactly as the APB/AXIL paths do — no AXI3-specific change there. `bridge_module_generator.py`: slave `axi3` branch. `config_validator.py` :341: `('axi4', 'axi5')` → `('axi3', 'axi4', 'axi5')`.

- [ ] **Step 4: Run test + lint gates**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && python3 -m pytest tests/test_generator_pkg.py -v` — all PASS.
Regenerate `bridge_1x2_axi3` as in Task 2 Step 4; decl-order + verible on every emitted `.sv`. Expected: clean.

- [ ] **Step 5: Commit**

```bash
git add projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/generators/slave_adapter_generator.py projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/components/bridge_module_generator.py projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/config_validator.py projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_1x2_axi3 rtl/filelists
git commit -m "feat(bridge): AXI3 slave converter path via axi4_to_axi3 (GitHub #97)"
```

---

### Task 4: Conditional converter filelist includes

**Files:**
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py` (master block ~:1079, slave block ~:1197)
- Test: `projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py`

**Interfaces:**
- Consumes: `config.masters` / `config.slaves` protocols; emitted `<output>/filelists/<name>.f` (filelist assembly at :937).
- Produces: `bridge_1x2_axi3.f` containing both converter `-f` lines; AXI4-only bridges' `.f` files unchanged (no new lines).

- [ ] **Step 1: Write the failing test**

Generator test: generate `bridge_1x2_axi3` into `tmp_path`, read the emitted `.f`, assert it contains `-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4.f` AND `.../axi4_to_axi3.f`; then generate an existing pure-AXI4 fixture (e.g. `bridge_1x2_rd_matched.toml`) and assert its `.f` does NOT contain either line.

- [ ] **Step 2: Run to verify failure**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && python3 -m pytest tests/test_generator_pkg.py -k filelist -v`
Expected: FAIL — no converter lines emitted yet.

- [ ] **Step 3: Implement**

In `bridge_generator.py`, mirror the exact `if any(m.protocol.lower() == 'apb' ...)` pattern (:1079): masters — `if any(m.protocol.lower() == 'axi3' for m in config.masters):` append the comment header + `-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4.f`; slaves — same for `axi3_to_axi3`→`axi4_to_axi3` with `-f .../axi4_to_axi3.f`, placed with the slave converter block (:1197–1231). Verify the referenced `.f` filenames exist in `projects/components/utility-ip/converters/rtl/filelists/`.

- [ ] **Step 4: Run to verify pass**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && python3 -m pytest tests/test_generator_pkg.py -v` — PASS.

- [ ] **Step 5: Commit**

```bash
git add projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py projects/components/fabric-gen-ip/bridge/rtl/filelists
git commit -m "feat(bridge): conditional axi3 converter filelist includes (GitHub #97)"
```

---

### Task 5: Batch fixtures + suite generation

**Files:**
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_2x2_axi3_masters.{toml,csv}` — 2 AXI3 masters (one 32-bit port, one 64-bit, both on a 64-bit fabric) × 2 AXI4 slaves
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_2x2_axi3_slaves.{toml,csv}` — AXI4 master + AXIL master × 2 AXI3 slaves
- Create: `projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_mix_e.{toml,csv}` — AXI3 + AXI4 + APB masters × AXI3 + AXI4 + APB slaves (hetero, extends `bridge_mix_a`–`d`)
- Modify: `projects/components/fabric-gen-ip/bridge/bin/bridge_batch.csv` — 4 rows (the three above + `bridge_1x2_axi3` from Task 2)
- Generated: `rtl/generated/bridge_{1x2_axi3,2x2_axi3_masters,2x2_axi3_slaves,mix_e}/`, `dv/tbclasses/`, `dv/tests/test_bridge_*.py`, `rtl/filelists/*.f`

**Interfaces:**
- Consumes: Tasks 1–4. Note `bin/tests/test_generator_pkg.py:119` requires every `test_configs/*.toml` to appear in the batch or be named `test_illegal_*` — the four rows satisfy this.
- Produces: four generated bridges with TB classes + tests, ready for Task 6 sims.

- [ ] **Step 1: Write the fixtures**

Author the three new TOML/CSV pairs following `bridge_2x2_axi5.toml` / `bridge_2x2_axi5_connectivity.csv` shape. Widths/IDs per existing conventions: AXI3 masters id_width=4; slaves id_width = 4 + master-index bits (see the `bridge TASK-005` comment convention in existing fixtures); non-overlapping `base_addr`/`addr_range`; `channels = "rw"` unless a fixture deliberately exercises `rd`/`wr` (keep all rw for v1). Add the four batch rows to `bridge_batch.csv` in the same column order.

- [ ] **Step 2: Generate the suite**

Run: `cd projects/components/fabric-gen-ip/bridge/bin && make all`
Expected: four new `rtl/generated/bridge_*` dirs, four `dv/tests/test_bridge_*.py`, TB classes, no generator errors. `git status` shows only the four new generated trees + filelists.

- [ ] **Step 3: Collection + lint gates**

Run: `cd projects/components/fabric-gen-ip/bridge/dv/tests && PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src python3 -m pytest test_bridge_1x2_axi3.py test_bridge_2x2_axi3_masters.py test_bridge_2x2_axi3_slaves.py test_bridge_mix_e.py --collect-only -q` — collects without import errors.
Decl-order + verible on every emitted `.sv` in the four new trees: clean.

- [ ] **Step 4: Commit**

```bash
git add projects/components/fabric-gen-ip/bridge/bin/bridge_batch.csv projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_2x2_axi3_masters.toml projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_2x2_axi3_masters_connectivity.csv projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_2x2_axi3_slaves.toml projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_2x2_axi3_slaves_connectivity.csv projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_mix_e.toml projects/components/fabric-gen-ip/bridge/bin/test_configs/bridge_mix_e_connectivity.csv projects/components/fabric-gen-ip/bridge/rtl/generated projects/components/fabric-gen-ip/bridge/dv
git commit -m "feat(bridge): four AXI3 batch bridges — suite generated (GitHub #97)"
```

---

### Task 6: DV runs + Review-Focus supplements

**Files:**
- Create: `projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_chunk.py` (>16-beat bursts to the AXI3 slave — Review Focus 2)
- Create: `projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_multioutstanding.py` (same-ID 4-outstanding reads from the AXI3 master — Focus 4; ordered multi-ID W — Focus 1 positive contract)
- Create: `projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_2x2_axi3_masters_wideburst.py` (64-bit bursts from the 32-bit AXI3 master — Focus 3)
- Create: `projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_lock.py` (AxLOCK=`10` exclusive pass-through — Focus 5, with directed drive if the BFM lacks lock)
- Test: all of `dv/tests/`

**Interfaces:**
- Consumes: generated TB classes + tests (Task 5); AXI3 BFMs `AXI3MasterRead/Write`, `AXI3SlaveRead/Write` from RDS-DV.
- Produces: passing sim evidence for all four bridges + the four hand supplements.

- [ ] **Step 1: Run the four generated tests at GATE**

Run: `cd projects/components/fabric-gen-ip/bridge/dv/tests && PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src REG_LEVEL=GATE python3 -m pytest test_bridge_1x2_axi3.py test_bridge_2x2_axi3_masters.py test_bridge_2x2_axi3_slaves.py test_bridge_mix_e.py -v`
Expected: PASS. If a converter filelist dep is missing, fix the Task 4 includes (do NOT touch converter RTL).

- [ ] **Step 2: Write and run the four supplements**

Model them on the hand-written extras `test_bridge_2x2_axi5_sideband_arb.py` / `test_bridge_1x2_rd_axi5c_chunk.py` (same imports, same wrapper/level structure). Assertions: chunk test — 32-beat INCR write+read to the AXI3 slave round-trips byte-exact and returns exactly one B with OKAY; multi-outstanding — 4 same-ID ARs return in issue order; ordered multi-ID W completes both writes with correct data per ID; wide-burst — 64-bit fabric bursts from the 32-bit AXI3 master return correct data; lock — exclusive read+write pass with OKAY (response passthrough, no lock semantics fabricated). Run each at `REG_LEVEL=GATE`; then `REG_LEVEL=FUNC` on the generated tests.

- [ ] **Step 3: Regression — full existing suite at GATE**

Run: `cd projects/components/fabric-gen-ip/bridge/dv/tests && PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src REG_LEVEL=GATE python3 -m pytest -v` (whole dir).
Expected: every pre-existing bridge test still PASSes — the validator/generator changes touched shared code paths.

- [ ] **Step 4: Commit**

```bash
git add projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_chunk.py projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_multioutstanding.py projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_2x2_axi3_masters_wideburst.py projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_lock.py
git commit -m "test(bridge): AXI3 Review-Focus supplements — chunk, ordering, wideburst, lock (GitHub #97)"
```

---

### Task 7: Docs

**Files:**
- Modify: `projects/components/fabric-gen-ip/bridge/PRD.md` (protocol support table/rows)
- Modify: `projects/components/fabric-gen-ip/bridge/references/README.md` (AXI3 citation next to ARM IHI 0022E)
- Modify: `projects/components/fabric-gen-ip/bridge/docs/bridge_has/` + `docs/bridge_mas/` md sources (protocol tables + integration chapter restating converter constraints **by reference** — no W interleaving, WRAP chop deferral, lock mapping)
- Generated: rev-bumped HAS/MAS PDFs via `docs/generate_has_pdf.sh` / `docs/generate_mas_pdf.sh` (build-time `--rev`; never hand-edit version tables)

- [ ] **Step 1: Update md sources**

PRD: add `axi3` rows/column wherever `axi5`/`apb` protocols are enumerated. References: add the AMBA AXI3 row (ARM IHI 0022 family) with the same WorldCat/catalogue-link style as existing entries. HAS/MAS: protocol-support tables gain `axi3`; a short integration chapter (or section) states: boundary-conversion architecture; converter constraints by reference to the converter docs (master W-no-interleave obligation, burst-chop on >16-beat egress, lock mapping, same-width converters + internal width adaptation); the four new batch bridges listed as validation evidence.

- [ ] **Step 2: Regenerate PDFs + gates**

Run: `cd projects/components/fabric-gen-ip/bridge/docs && ./generate_has_pdf.sh && ./generate_mas_pdf.sh`
Expected: new revs emitted; pre-commit's link/emoji gates pass on commit.

- [ ] **Step 3: Commit**

```bash
git add projects/components/fabric-gen-ip/bridge/PRD.md projects/components/fabric-gen-ip/bridge/references/README.md projects/components/fabric-gen-ip/bridge/docs
git commit -m "docs(bridge): AXI3 protocol rows, integration chapter, references citation (GitHub #97)"
```

---

### Task 8: Wrap-up — issue, notify, final review prep

**Files:**
- None (GitHub + process)

- [ ] **Step 1: Update GitHub #97** — comment with the commit list and test evidence (four bridges passing at GATE/FUNC, supplements, regression sweep).
- [ ] **Step 2: Fire `kimi-notify`** completion message.
- [ ] **Step 3: Hand to whole-branch review** (subagent-driven flow runs its own final review; on native flow, request the fresh reviewer per superpowers:requesting-code-review).
