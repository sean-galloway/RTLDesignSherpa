# DE10-Standard Fabric Benchmark Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build and measure the two-leg fabric benchmark on the DE10-Standard (bridge crossbar vs Intel Platform Designer interconnect) with the mirrored W1/W2/W3 workloads, delivering size and performance deltas.

**Architecture:** One DE10 harness top holds the constant cast (stream mover, CRC checker + SRAM, write injector, PRBS slave, obs blocks) and swaps only the fabric: Leg A = bridge-generated AXI3 crossbar, Leg B = qsys-generated PD AXI interconnect. The host driver is System Console over a JTAG-to-Avalon master + AXI translator, replacing stream's UART bridge. Harness structure merges the stream Genesys2 cast/register-map conventions with the pumice NexysA7 board-lifecycle/sequence/csv conventions, on a new Quartus flow layer.

**Tech Stack:** Quartus Prime 24.1 Standard (`/home/seang/intelFPGA_lite/24.1std`, `quartus_sh`, `qsys-script`/`qsys-generate` in `quartus/sopc_builder/bin/`), Platform Designer (altera_hps, merlin AXI fabric, altera_jtag_avalon_master, altera_merlin_axi_translator), System Console TCL, Python 3.12 host layer, bridge generator (`projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py`).

**Spec:** `projects/fpga-systems/DE10-Standard/fabric-benchmark/PRD.md` (v0.3)

## Global Constraints

- Board / device: Terasic DE10-Standard, Cyclone V 5CSXFC6D6F31C8 (PRD §3).
- Toolchain: Quartus Prime 24.1 Standard, identical options/seeds/SDC both legs (PRD §4.4).
- HPS DDR3: 1 GB, 2×256Mx16 (32-bit data bus) — hard Intel MC, identical HPS config both legs (manual §3.1, PRD §3).
- HPS-FPGA bridges (Cyclone V fixed): h2f_axi_master 64-bit, f2h_axi_slave 128-bit, lightweight h2f 32-bit — verify against GHRD at M1 before fixing the bridge TOML widths (manual §7.3 figure; PRD §11).
- Clock plan: one fabric clock domain, same frequency both legs (PRD §3); target 100 MHz nominal, achieved fmax reported per leg (PRD §4.3).
- Matching rule: Leg A bridge TOML mirrors the PD topology exactly — same master/slave count, widths, ID widths, address map; Leg A never exceeds Leg B's configured capability (PRD §3).
- obs blocks: identical RTL and probe points both legs, same register addresses both legs (PRD §3/§4.2).
- Driver: same System Console TCL scripts, transaction counts, PRBS seeds, both legs and both flavors (PRD §4.4).
- Host transport: JTAG (altera_jtag_avalon_master + merlin AXI translator); no native jtag_axi_master exists in 24.1 std — confirmed by IP inventory 2026-10-11.
- No Linux userspace benchmarking (PRD §9); HPS boots only far enough to initialize the DDR3 MC (preloader from GHRD collateral).
- Pre-commit gates before every commit: filelist registry (--check/--audit/--blindspots --ratchet/--placement), check_doc_examples.py, check_test_dut_family.py, decl-order on hand-written SV, broken-links ratchet.
- Shared tree: commit by explicit pathspec only; never checkout/stash/reset; on index.lock wait ~8 s and retry.

## Review Focus

1. **HPS never boots / DDR3 never initialized** — every workload then hangs with no R/B responses. A reasonable person expects the harness to *say* "DDR3 not ready" instead of timing out: the bring-up sequence must read an HPS-DDR3-ready flag (System Console HPS service or a CSR written by the preloader) before any traffic task, and fail fast with that message.
2. **JTAG driver saturation** — the JTAG-AXI master tops out well below DRAM bandwidth, capping the performance axis. Pinned by PRD §10 risk table: report "at-driver-saturation" figures plainly; the W2 (SRAM↔SRAM) control partially isolates this since SRAM exceeds JTAG ceiling by less... if W2 also saturates at the same number, the driver — not either fabric — is the ceiling.
3. **Mirror-flavor asymmetry (W1-F1 vs W1-F2)** — PRD §4.1 says asymmetry is itself a result; the plan must attribute it with W2 (fabric-only) vs W1 (with MC) before declaring either fabric biased.
4. **PD-only features with no bridge equivalent** (default slave behavior, interconnect pipeline knobs) — matching rule says match functionally or document as a difference; silently diverging configs invalidate the size comparison.
5. **Leg A fmax below Leg B on Cyclone V** (different RAM/adder inference) — the comparison stays at-equal-clock per PRD §4.3, but a leg that misses 100 MHz must still close timing at the shared achieved frequency or the performance comparison is not at the same clock.

---

### Task 1: Board registry entry + DE10 facts file

**Files:**
- Create: `projects/fpga-systems/bin/boards/de10_standard.py`
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/docs/de10_facts.md`
- Modify: `projects/fpga-systems/bin/fpga_board.py` (board registry table — add the de10_standard entry alongside nexys_a7_100t)

**Interfaces:**
- Produces: `de10_standard.py` exposing the same attributes `fpga_board.py` expects of a board module (part `5CSXFC6D6F31C8`, cable id for the on-board USB-Blaster II, `find_uart_ports()` returning `[]` — host transport is JTAG, no UART needed); `de10_facts.md` is the human-readable fact sheet (DDR3 part, bridge widths, clock plan, programming method), cited to the Terasic manual §3.1/§7.3.

- [ ] **Step 1: Write the board file.** Copy the shape of `projects/fpga-systems/bin/boards/nexys_a7_100t.py`; set part string, JTAG cable match rule (USB-Blaster II, usb_device_id), empty UART list, program flow = `quartus_pgm` (tooling lands in Task 3; here just the registry metadata + a NotImplementedError path guard).
- [ ] **Step 2: Write `de10_facts.md`** with the facts from the M0 inventory: HPS DDR3 2×256Mx16 (32-bit); FPGA-side 64 MB SDRAM (not used in v1); bridge widths (h2f 64b / f2h 128b / lw 32b — marked VERIFY-at-M1 against GHRD); config methods (JTAG + AS/EPCS128); System Console as host.
- [ ] **Step 3: Verify import + registry resolution.** Run: `python3 -c "import sys; sys.path.insert(0,'projects/fpga-systems/bin'); import fpga_board; b=fpga_board.Board('de10_standard'); print(b.part)"` → Expected: prints `5CSXFC6D6F31C8`.
- [ ] **Step 4: Commit** (pathspec: the three files above).

### Task 2: GHRD collateral intake (HPS DDR3 preset + preloader)

**Files:**
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/quartus/ghrd/README.md` (provenance: URL/date/license note for the vendor collateral; **no vendor files committed** — they stay outside the repo like the books policy; only our generated-from facts enter git)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/data/ghdr_facts.json` (machine-readable extraction)

**Interfaces:**
- Produces: `ghdr_facts.json` keys consumed by Task 4 (qsys TCL) and Task 7 (bridge TOML): `hps_ddr3` {part, width, freq}, `h2f_width`, `f2h_width`, `lw_width`, `h2f_clock_hz`, `preloader_image` (path outside repo), `ghrd_qsys` (path outside repo).

- [ ] **Step 1: Acquire the DE10-Standard GHRD** (Terasic download page → DE10-Standard System CD or standalone GHRD archive; expected contents: `soc_system.qsys`, `hps.xml`-era handoff, prebuilt preloader/u-boot images). Unpack under `/mnt/data/de10-collateral/` (outside repo).
- [ ] **Step 2: Extract the HPS DDR3 configuration** — open `soc_system.qsys` with `qsys-script --system=...` TCL `get_component_properties`/`get_interface_properties` on the hps component; write `ghdr_facts.json`. Expected: DDR3 32-bit, h2f 64, f2h 128, lw 32 (VERIFY against extracted values; if the figure-only manual widths disagree, extracted wins and `de10_facts.md` gets corrected).
- [ ] **Step 3: Verify preloader image exists** in the collateral and record its path in `ghdr_facts.json`. Expected: a `preloader*.bin`/`u-boot*.img` pair or mkpimage output present.
- [ ] **Step 4: Fallback documented.** If the GHRD cannot be obtained, stop and report — do NOT hand-roll the HPS DDR3 timing config; the preloader is on the critical path for every workload.
- [ ] **Step 5: Commit** (pathspec: `quartus/ghrd/README.md`, `data/ghdr_facts.json`, plus the `de10_facts.md` correction if widths changed).

### Task 3: Quartus flow layer + toolchain smoke (hello LED)

**Files:**
- Create: `make/fpga_flow_quartus.mk`
- Create: `projects/fpga-systems/bin/program_fpga_quartus.tcl`
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/build-smoke/Makefile`
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/build-smoke/rtl/blink_top.sv`
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/build-smoke/fpga/de10_standard.sdc`

**Interfaces:**
- Produces: make targets `project`, `synth`, `bitstream`, `program`, `clean` for any build dir whose Makefile sets `FLOW := quartus`, `TOP`, `QSYS_SYSTEM` (optional), `FILELIST`; `fpga_board.py program --board de10_standard` dispatches to `program_fpga_quartus.tcl` via `quartus_pgm`. Target names mirror `make/fpga_flow.mk` so the dispatcher pattern from stream/pumice works unchanged.
- Consumes: board registry from Task 1.

- [ ] **Step 1: Write `fpga_flow_quartus.mk`.** `project`: `quartus_sh -t create_project.tcl` (TCL creates .qpf/.qsf from `TOP`, part from `BOARD.part`, reads `FILELIST`, adds SDC); if `QSYS_SYSTEM` set, first `qsys-generate --synthesis=VERILOG` then add the generated `.qip`; `bitstream`: `quartus_sh -t build_all.tcl` (shutil flow: `execute_flow -compile`); `program`: `quartus_pgm -c <cable> -m jtag -o p\;$(bitstream).sof`. Include the same build-lock (`flock`) convention as `fpga_flow.mk`.
- [ ] **Step 2: Write `program_fpga_quartus.tcl`** (JTAG identity pre-read like `jtag_readback.tcl`, then program; reuse the board_lock.sh wrapper — no changes needed there).
- [ ] **Step 3: Write the smoke build.** `blink_top.sv`: 27-bit counter from the on-board 50 MHz oscillator (`PIN_AF14`... — exact pin from the Terasic manual pin list §4; verify before writing) driving LEDR[0]. SDC: `create_clock -period 20 [get_ports clk]`.
- [ ] **Step 4: Build.** Run: `make -C projects/fpga-systems/DE10-Standard/fabric-benchmark/build-smoke bitstream` → Expected: fitter reports 0 errors; a `.sof` exists. This proves Quartus 24.1 std → 5CSX device → timing closure end-to-end before any fabric work (PRD §10: "M0 verifies before any build work").
- [ ] **Step 5: Commit** (pathspec: the five files above + `fpga_board.py` program dispatch edit).

### Task 4: Leg B qsys system (PD fabric skeleton)

**Files:**
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/quartus/legb/de10_legb.qsys.tcl` (qsys-script source that builds the whole system programmatically)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/build-legb/Makefile`
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/rtl/de10_legb_top.sv`

**Interfaces:**
- Consumes: `ghdr_facts.json` (Task 2).
- Produces: generated `de10_legb.qsys` (git-ignored, generated) instantiating: hps (DDR3 config from facts), **master side**: `altera_jtag_avalon_master` → `altera_merlin_axi_translator` (Avalon→AXI3) → PD AXI interconnect; **HPS side**: interconnect masters → `f2h_axi_slave` (128b) and slaves ← `h2f_axi_master` (64b); placeholder on-chip RAM slaves for M1 loopback. This TCL is the single source of truth for Leg B topology — Task 7 reads its component list to write the matching bridge TOML.

- [ ] **Step 1: Write `de10_legb.qsys.tcl`** per the Interfaces block. Export the interconnect's AXI3-facing master/slave ports as conduit exports named `fpga_axi_*` so `de10_legb_top.sv` can hang the constant cast on them.
- [ ] **Step 2: Generate + compile.** Run: `make -C build-legb bitstream` → Expected: qsys-generate exit 0, quartus fit 0 errors. (Timing closure at this skeleton stage is informational.)
- [ ] **Step 3: Verify topology extraction.** Run a qsys-script TCL that prints the master/slace connection list and widths; compare against `ghdr_facts.json`; save the printout as `data/legb_topology.txt` (committed — it is what Task 7 mirrors).
- [ ] **Step 4: Commit** (pathspec: the three files + `data/legb_topology.txt`).

### Task 5: System Console driver + JTAG loopback test

**Files:**
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/scripts/sc_master.tcl` (System Console TCL library: `open_jtag_master`, `csr_read addr`, `csr_write addr data`, `check_ddr3_ready`)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/bin/de10_env.py` (sys.path setup, mirrors `stream/bin/stream_env.py` + `pumice/bin/pumice_env.py`)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/bin/de10_addrs.py` (by-name CSR map, mirrors `stream/bin/harness_addrs.py` shape; map contents come from the Task 6 address map)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/bin/run_seq.py` (sequence runner, mirrors `pumice/bin/run_smoke.py`: `--list`, dependency-ordered sequences)

**Interfaces:**
- Produces: `sc_master.tcl` procs called by every later measurement script; `de10_addrs.py: Csr(accessor, name→addr)` used by host scripts; `run_seq.py` auto-discovers `seq_*.py` in `bin/` with `requires=` tuples (same contract as pumice's SequenceRunner).
- Consumes: JTAG master present in Leg B (Task 4).

- [ ] **Step 1: Write `sc_master.tcl`** with the System Console API: `get_service_paths master`, `claim_service`, `master_read_32`/`master_write_32`, `close_service`. `check_ddr3_ready`: reads the HPS reset manager/ddr status through the lightweight h2f bridge... simplest reliable M1 form: poll a scratch register the preloader writes (Task 6 defines it); if it never appears, fail with "HPS DDR3 not ready — check preloader".
- [ ] **Step 2: Loopback test.** Add `bin/seq_loopback.py`: writes/reads a walking-ones pattern to the Leg B on-chip RAM slave via `sc_master.tcl` through the full JTAG→translator→interconnect path. Run on the board: `python3 bin/run_seq.py --board de10_standard loopback` → Expected: PASS, and a measured round-trip latency (first JTAG ceiling datapoint, logged to `data/`).
- [ ] **Step 3: Commit** (pathspec: the four files + `bin/seq_loopback.py`).

### Task 6: Constant cast port — DE10 harness top (Leg B first)

**Files:**
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/rtl/de10_harness.sv` (constant cast: movers, injector, PRBS slave, CRC+SRAM, obs, CSR file)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/rtl/filelists/de10_harness.f`
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/rtl/de10_harness_addrmap.md` (slave map, mirrors stream's address-map table style)
- Modify: `projects/fpga-systems/DE10-Standard/fabric-benchmark/build-legb/Makefile` (TOP → legb top with harness)
- Modify: `de10_legb_top.sv` (instantiate harness, wire `fpga_axi_*` exports)

**Interfaces:**
- Consumes: stream block filelists — `projects/components/dma-ip/stream/rtl/filelists/top/stream_top_ch8.f` (mover); the master injector pair that owns all DDR3 interactions (owner directive 2026-10-11: **the wr/rd injectors do the DDR3 interactions**): `rtl/amba/filelists/axi4_master_wr_injector.f` (PRBS fill master — F1 setup fill, W3 contention fill) and `rtl/amba/filelists/axi4_master_rd_crc_check.f` (master read-back + CRC verdict — C1 readback for F2, integrity check for fills); the slave-side CRC-SRAM pair stream's agents target: `rtl/amba/filelists/axi4_slave_wr_crc_check.f` (write sink + CRC checker + SRAM backing — F1's drain target) and `rtl/amba/filelists/axi4_slave_rd_injector.f` (read source — F2's mirror source); obs: `rtl/amba/filelists/axi4_intf_master_observer.f`/`axi4_intf_slave_observer.f` + `monbus_tally_axil.f`.
- Produces: `de10_harness_addrmap.md` — the fixed slave address map (CSR file, desc/tally SRAMs, CRC SRAM window, PRBS slave, obs registers, injector CSR windows for both master injectors) used identically in both legs; `de10_addrs.py` map filled from it.
- Key decision locked here: the HPS-facing side of the harness is AXI3 (f2h/h2f) with AXI4 inside; obs blocks tap the internal AXI4 nets — identical probe points both legs (PRD §3).
- Workload wiring locked here: W1-F1 = wr_injector fills DRAM, stream drains DRAM→slave-side CRC SRAM; W1-F2 = stream reads slave_rd_injector→writes DRAM, master_rd_crc_check reads DRAM back (C1 verdict); W3 = stream drain concurrent with wr_injector fill, mirror swaps; W2 = SRAM↔SRAM between the slave pair (no DRAM, fabric-only control).

- [ ] **Step 1: Confirm the PRBS responder** — the Flavor-2 source is `axi4_slave_rd_injector` (LFSR-generated read data per its filelist's `shifter_lfsr_fibonacci` dependency); record the module + its PRBS seed programming in the addrmap doc (resolves the PRD §11 M2 question; no `rtl/fub` selection needed).
- [ ] **Step 2: Write `de10_harness.sv`** replicating stream_harness's structure minus `uart_axil_bridge` (JTAG-AXI master takes its place) and minus the stream DUT's channel generics pinned to the DE10 cast. Instantiate the four injector/CRC blocks per the workload wiring above: master pair on the DRAM side (f2h/h2f AXI3 ports), slave-side CRC-SRAM pair on stream's ports, obs taps on the internal AXI4 nets.
- [ ] **Step 3: Compile Leg B full system.** Run: `make -C build-legb bitstream` → Expected: fit passes; capture `data/legb_size_baseline.json` (ALM/FF/M10K from fitter report parse — the parser is Task 8, here just archive the .rpt).
- [ ] **Step 4: W1 smoke on board.** Script `bin/seq_w1_smoke.py` (F1 fill→drain with a small 64 KB region, CRC verdict). Run: `python3 bin/run_seq.py w1_smoke` → Expected: CRC OK, first real DRAM datapoint lands in `data/`.
- [ ] **Step 5: Commit** (pathspec: rtl/, build-legb Makefile, addrmap doc, seq script).

### Task 7: Leg A — bridge fabric, matched topology

**Files:**
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/rtl/bridges/configs/de10_fabric.toml` (+ connectivity CSV)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/build-lega/Makefile`
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/rtl/de10_lega_top.sv`
- Modify: `de10_addrs.py` — none (same map; listed to assert it).

**Interfaces:**
- Consumes: `data/legb_topology.txt` (Task 4) — the TOML mirrors it exactly (PRD §3 matching rule); bridge generator with `protocol = "axi3"` ports (verified under #97/#98/#99).
- Produces: generated crossbar wired into `de10_lega_top.sv` with the identical `de10_harness.sv` instance and identical obs hookups.

- [ ] **Step 1: Write `de10_fabric.toml`** mirroring `legb_topology.txt` (masters: JTAG-AXI + stream + injector; slaves: HPS f2h... i.e., the same endpoints PD exposes, same widths/IDs/addresses).
- [ ] **Step 2: Generate + compile.** `make -C build-lega bitstream` → Expected: fit passes at the shared clock target; if Leg A misses where Leg B closed, apply PRD §4.3 (report achieved; close both legs at the shared achieved frequency).
- [ ] **Step 3: Same-driver parity.** Run the Task 6 W1 smoke unmodified against Leg A → Expected: PASS with CRC OK. This is the PRD §8 "identical driver" success criterion in miniature.
- [ ] **Step 4: Commit** (pathspec: the new files; generated bridge dir per bridge Rule #0 conventions — generated RTL committed, regen via `make regen` pattern if the generator changes).

### Task 8: Measurement campaign + parsers

**Files:**
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/scripts/reports_to_csv.py` (Fitter/TimeQuest report → CSV parse: ALM/FF/M10K/fmax, per PRD §4.3)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/bin/seq_w1_sweep.py`, `bin/seq_w2_loopback.py`, `bin/seq_w3_contention.py` (+ scenario-library runners as appetite allows: B1/B2/B4, C1/C2 per PRD §4.1)
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/data/README.md` (CSV column conventions, mirrors pumice csv format)

**Interfaces:**
- Consumes: all prior tasks; obs/tally readout procs from `sc_master.tcl`.
- Produces: `data/<leg>/<scenario>_<date>.csv` files; `data/size_<leg>.csv`; the inputs to the analysis doc (Task 9).

- [ ] **Step 1: Write `reports_to_csv.py`;** run on both legs' build reports → `data/size_{a,b}.csv`. Verify: columns per PRD §4.3 (ALM, FF, M10K blocks/bits, DSP, fmax, wall-clock).
- [ ] **Step 2: Write the three workload sweep sequences** with N=5 runs/point, median+spread (PRD §4.4), identical seeds both legs.
- [ ] **Step 3: Run v1 sweep** on both legs (W1-F1/F2, W2, W3) → Expected: every flavor run ends in a CRC verdict (C1 for F2); mirror-agreement columns filled.
- [ ] **Step 4: Commit** (pathspec: scripts/, bin/ seq files, data/README.md; CSV data files committed per PRD §6.4).

### Task 9: Analysis document

**Files:**
- Create: `projects/fpga-systems/DE10-Standard/fabric-benchmark/docs/fabric_benchmark_analysis.md` (standard doc flow → PDF per repo doc methodology; graphs from plot scripts in the stream/pumice style)

**Interfaces:**
- Consumes: `data/` CSVs from Task 8.
- Produces: the published comparison: headline size table, performance tables both flavors, mirror-agreement verdicts, honest caveats (PRD §6.5/§8).

- [ ] **Step 1: Write the analysis doc** with the normalized delta table (% A vs B) and the mirror-agreement section; every divergence attributed via W2 per Review Focus 3.
- [ ] **Step 2: Render to PDF** via the repo's standard doc flow; place final PDF in `projects/fpga-systems/DE10-Standard/fabric-benchmark/docs/` (repo convention).
- [ ] **Step 3: Commit + close out** (pathspec: docs/; then verify PRD success criteria §8 one final time and report).

---

## Self-review notes

- **Spec coverage:** PRD §4.1 workloads → Task 8 (W1/W2/W3) + scenario library listed as appetite-allowing steps inside Task 8; §4.2 metrics → obs readout procs (Task 5) + sweep sequences (Task 8); §4.3 size → Task 8 Step 1; §4.4 methodology → identical-driver steps pinned in Tasks 6/7; §6 deliverables → quartus/ (Tasks 3/4/7), rtl/ (6/7), scripts/ (5/8), data/ (8), docs/ (9). M0 §11 open questions → Task 2 (facts), Task 4 Step 3 (topology), Task 5 (JTAG availability/bandwidth, license-free System Console confirmed by local run in Task 5 Step 2), Task 6 Step 1 (PRBS block selection). A2 backpressure stays deferred per PRD.
- **Step scan:** every step names a file or a run command plus expected output; no "handle edge cases" lines.
- **Type consistency:** `ghdr_facts.json` keys are the only cross-task contract and are spelled out in Task 2's Produces; `de10_addrs.py`, `sc_master.tcl` procs, and the `seq_*.py requires=` convention are named identically wherever consumed.
- **Review Focus:** (1) covered by `check_ddr3_ready` in Task 5 Step 1 + fail-fast in every seq; (2) covered by W2-vs-W1 attribution note in Task 9 Step 1 and the loopback latency datapoint in Task 5 Step 2; (3) Task 9 Step 1; (4) Task 7 Step 1 mirrors `legb_topology.txt` exactly; (5) Task 7 Step 2.
- **Proportion:** PRD is ~300 lines; this plan is ~250 — within proportion. The heavy lifting (qsys TCL bodies, harness RTL) is deliberately left to the implementer with only interfaces fixed.

## Merge interpretation (owner-confirmed 2026-10-11)

The owner's "combine the stream and the pumice builds" note is resolved as **harness-structure merge**: stream contributes the block cast, register-map, and obs conventions; pumice contributes board lifecycle (registry/lock/sequences/CSV). Both source flows are Vivado; the Quartus flow layer is new (Task 3).
