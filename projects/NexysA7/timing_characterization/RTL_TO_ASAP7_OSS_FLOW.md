# RTL → ASAP7 (7 nm) Gate-Level Netlist — Fully Open-Source Flow

**Goal:** take SystemVerilog RTL and produce a technology-mapped gate-level
netlist (and, optionally, a placed-and-routed GDS) against the ASAP7 7 nm
predictive PDK, using **only open-source tools**.

**Target host:** Ubuntu workstation (e.g. `amdtrp`). Everything below builds and
runs natively; no commercial licenses required.

> **Reality check on ASAP7.** ASAP7 is a *predictive* academic PDK, not a real
> foundry kit. Its timing/area/power numbers are meaningful **relative to one
> another** for tool benchmarking and methodology work — they are **not**
> predictions of real 7 nm silicon, and there is no path to tape-out. That is
> exactly why the `.lib` characterization (clock-to-out, cell delays, setup/hold)
> is openly inspectable: there's no foundry NDA. Treat it as a teaching /
> research substrate (ideal for RTLDesignSherpa), not sign-off.

---

## 1. Toolchain overview

```
  SystemVerilog RTL
        │
        ▼
  ┌─────────────┐   SV frontend: yosys-slang (preferred) OR sv2v fallback
  │   Yosys     │ ─ logic synthesis, generic opt
  │   + ABC     │ ─ technology mapping to ASAP7 std cells
  └─────────────┘
        │  write_verilog
        ▼
  Gate-level netlist (.v)  ◄── ASAP7 Liberty (.lib) provides the cells
        │
        ├──► OpenSTA              (standalone static timing on the netlist)
        ├──► Verilator + cocotb   (gate-level functional sim w/ ASAP7 models)
        └──► OpenROAD (ORFS)      (optional: floorplan → place → CTS → route → GDS)
                                   FakeRAM2.0 supplies SRAM macros
                                   KLayout views the GDS
```

Two paths are documented:

- **Path A — ORFS turnkey (recommended).** OpenROAD-Flow-Scripts drives the whole
  thing, handles Liberty merging, `dont_use` cells, the 4× layout scaling, SDC,
  and SRAM macros automatically. Fastest way to a correct mapped netlist
  (`1_synth.v`) and, if you want it, a full GDS.
- **Path B — standalone Yosys.** Transparent, minimal, no OpenROAD. Best for
  understanding each step and for dropping into RTLDesignSherpa. Produces the
  mapped netlist only (no place & route).

---

## 2. Tools and where to get them

| Tool | Purpose | Repo / download |
|------|---------|-----------------|
| **Yosys** | RTL synthesis + ABC tech mapping | https://github.com/YosysHQ/yosys |
| **OSS CAD Suite** | Prebuilt bundle of Yosys, ABC, and friends (easiest install for Path B) | https://github.com/YosysHQ/oss-cad-suite-build |
| **ABC** | Technology mapping engine (bundled inside Yosys) | https://github.com/berkeley-abc/abc |
| **yosys-slang** | Modern SystemVerilog frontend plugin for Yosys (slang-based) | https://github.com/povik/yosys-slang |
| **slang** | SV parser/elaborator that yosys-slang builds on (auto-fetched by its CMake) | https://github.com/MikePopoloski/slang |
| **sv2v** | SV→Verilog-2005 converter (fallback frontend; you already use this) | https://github.com/zachjs/sv2v |
| **ASAP7 PDK** | 7 nm predictive PDK: std cells, Liberty, LEF, GDS, SPICE | https://github.com/The-OpenROAD-Project/asap7 |
| **OpenROAD-Flow-Scripts (ORFS)** | Turnkey RTL→GDS orchestration (Path A) | https://github.com/The-OpenROAD-Project/OpenROAD-flow-scripts |
| **OpenROAD** | The APR engine (bundled in ORFS) | https://github.com/The-OpenROAD-Project/OpenROAD |
| **OpenSTA** | Standalone static timing analysis (also bundled in OpenROAD) | https://github.com/parallaxsw/OpenSTA |
| **FakeRAM2.0** | "Fake" memory compiler → Liberty/LEF/Verilog macros (ASAP7 has no SRAM compiler) | https://github.com/The-OpenROAD-Project/FakeRAM2.0 |
| **KLayout** | GDS / layout viewer (Path A only) | https://github.com/KLayout/klayout |
| **GTKWave** or **Surfer** | Waveform viewing for gate-level sim | https://gtkwave.sourceforge.net / https://gitlab.com/surfer-project/surfer |

You already have Verilator, cocotb, sv2v, SymbiYosys, and an OSS CAD Suite
install from the RTLDesignSherpa work — those carry straight over.

---

## 3. Install (Ubuntu)

### 3.1 System dependencies

```bash
sudo apt-get update
sudo apt-get install -y \
  build-essential clang cmake git \
  python3 python3-pip python3-venv \
  tcl-dev tcl tk libreadline-dev \
  bison flex libffi-dev \
  zlib1g-dev gawk
```

### 3.2 ASAP7 PDK (needed by both paths)

```bash
cd ~/eda
git clone --recurse-submodules https://github.com/The-OpenROAD-Project/asap7.git
```

The tree (submodules hold the actual IP):

```
asap7/
├── asap7_pdk_r1p7/     # tech files, HSPICE models, Calibre decks
├── asap7_sram_0p0/     # minimal SRAM macros (usually replaced by FakeRAM2.0)
├── asap7sc6t_26/       # 6-track cells (area studies)
├── asap7sc7p5t_27/     # 7.5-track cells (older, v27)
└── asap7sc7p5t_28/     # 7.5-track cells (CURRENT — use this for digital)
```

> For digital flows use **`asap7sc7p5t_28`**. Liberty files live under
> `asap7sc7p5t_28/LIB/NLDM/` (NLDM is fine and lighter for synthesis; CCS also
> ships). They may be gzipped (`*.lib.gz`) — `gunzip` what you need.

ASAP7 ships **three STA corners only** — TT, FF, SS — as both HSPICE and
per-group Liberty, across **four V_T flavors** (RVT, LVT, SLVT, SRAM) and **five
cell groups** (SIMPLE, INVBUF, AO, OA, SEQ). There are no SF/FS or temperature
corners; generate those yourself if you need them.

### 3.3 Path A tools — ORFS (builds Yosys, OpenROAD, yosys-slang for you)

```bash
cd ~/eda
git clone --recurse-submodules https://github.com/The-OpenROAD-Project/OpenROAD-flow-scripts.git
cd OpenROAD-flow-scripts
sudo ./etc/DependencyInstaller.sh          # one-time system deps
./build_openroad.sh --local                # builds yosys + openroad + yosys-slang
source ./env.sh                            # puts tools on PATH
yosys -version && openroad -version
```

ORFS vendors ASAP7 itself, so for Path A you don't strictly need the clone in
3.2 — but it's handy to have the full PDK around for reference.

### 3.4 Path B tools — standalone Yosys + slang

If you'd rather not build OpenROAD, use OSS CAD Suite for Yosys/ABC:

```bash
cd ~/eda
# grab the latest linux-x64 tarball from the releases page:
#   https://github.com/YosysHQ/oss-cad-suite-build/releases
tar -xzf oss-cad-suite-*.tgz
source ~/eda/oss-cad-suite/environment        # sets PATH for yosys, abc, etc.
```

Build the SystemVerilog frontend plugin (its CMake auto-fetches slang):

```bash
cd ~/eda
git clone --recurse-submodules https://github.com/povik/yosys-slang.git
cd yosys-slang
make                      # uses `yosys-config` from the active Yosys on PATH
make install              # installs the plugin where Yosys can -m it
```

sv2v fallback (prebuilt binary is simplest):

```bash
# from https://github.com/zachjs/sv2v/releases  (linux x86_64 zip)
unzip sv2v-Linux.zip && sudo cp sv2v-Linux/sv2v /usr/local/bin/
sv2v --version
```

---

## 4. Path A — ORFS turnkey (recommended)

ORFS uses a per-design `config.mk`. Minimal example for a pure-logic block
(no SRAM) on ASAP7:

```makefile
# flow/designs/asap7/myblock/config.mk
export DESIGN_NAME     = myblock
export PLATFORM        = asap7
export VERILOG_FILES   = $(sort $(wildcard ./designs/src/myblock/*.sv))
export SDC_FILE        = ./designs/asap7/myblock/constraint.sdc

# Use the slang SV frontend (avoids sv2v lossiness, much better QoR):
export USE_SLANG       = 1

# Reasonable starting floorplan; tune to your design:
export CORE_UTILIZATION = 40
export PLACE_DENSITY    = 0.60
```

A minimal SDC:

```tcl
# constraint.sdc
create_clock -name clk -period 700 [get_ports clk]   ;# ps — ASAP7 lib units
set_input_delay  100 -clock clk [all_inputs]
set_output_delay 100 -clock clk [all_outputs]
```

Run **synthesis only** to get the mapped netlist:

```bash
cd ~/eda/OpenROAD-flow-scripts/flow
source ../env.sh
make DESIGN_CONFIG=./designs/asap7/myblock/config.mk synth
```

The mapped gate-level netlist lands at:

```
flow/results/asap7/myblock/base/1_synth.v        # technology-mapped netlist
flow/reports/asap7/myblock/base/synth_stat.txt   # cell/area report
```

Run the **full RTL→GDS** flow instead:

```bash
make DESIGN_CONFIG=./designs/asap7/myblock/config.mk
make DESIGN_CONFIG=./designs/asap7/myblock/config.mk gui_final   # view in OpenROAD GUI
```

ORFS transparently handles the things that bite you in a hand-rolled flow:
Liberty merging across the five cell groups, the ASAP7 `DONT_USE_CELLS` set, the
**4× drawn-scale → 0.25 APR scaling**, multi-corner setup, and SRAM macro
insertion.

### 4.1 Adding SRAM (FakeRAM2.0)

ASAP7 has no real memory compiler, so generate blackbox macros:

```bash
cd ~/eda
git clone https://github.com/The-OpenROAD-Project/FakeRAM2.0.git
cd FakeRAM2.0
# edit a config JSON describing the PDK + the memory geometry you want,
# e.g. 256x32, 512x64, ...  (see repo README for the schema)
python3 run.py configs/asap7.json
```

It emits `.lib`, `.lef`, and `.v` for each `width × depth` you request. Wire them
into the design via `ADDITIONAL_LIBS` / `ADDITIONAL_LEFS`, and instantiate the
matching blackbox module in RTL. ORFS already ships a couple of pre-baked
`fakeram7_*` macros under `platforms/asap7/{lib,lef}/` you can copy from.

---

## 5. Path B — standalone Yosys (netlist only, no APR)

This is the transparent version. It maps RTL to ASAP7 cells and writes a netlist,
nothing more — good for RTLDesignSherpa demos.

### 5.1 The Liberty-merge gotcha

ABC's `-liberty` takes **one** Liberty file, but ASAP7 splits cells across five
group libraries per V_T/corner. You must map against a **single merged** Liberty.
Two clean options:

1. **Borrow the merged lib ORFS already builds** after any Path-A run:
   `flow/objects/asap7/.../lib/` contains a concatenated `.lib`. Point ABC at it.
2. **Merge yourself** — concatenate the five RVT/TT group libs into one
   `library(){...}` block. Don't naively `cat` five separate `library()` headers;
   use a small merge (strip the trailing `}` of all but the last and the
   `library(...) {` of all but the first), or use ORFS's merge helper. Verify with
   `read_liberty` reporting the expected cell count.

Set `ASAP7_LIB` below to that single merged RVT/TT NLDM file.

### 5.2 Synthesis script (slang frontend)

```tcl
# synth_asap7.ys   →  run with:  yosys -c synth_asap7.ys
yosys -import

set ASAP7_LIB $::env(ASAP7_LIB)     ;# merged RVT/TT NLDM liberty
set TOP       myblock

# --- SystemVerilog frontend via slang plugin ---
plugin -i slang
read_slang --top $TOP rtl/*.sv

# --- read cells for area/sequential mapping ---
read_liberty -lib $ASAP7_LIB

# --- generic synthesis + flatten (flatten avoids the known ASAP7
#     hierarchical-synth segfault on some RISC-V-style cores) ---
synth -top $TOP -flatten

# --- map flops, then combinational logic, to ASAP7 cells ---
dfflibmap -liberty $ASAP7_LIB
abc -liberty $ASAP7_LIB -constr constr.sdc     ;# or:  abc -liberty $ASAP7_LIB -D 700

# --- tidy up ---
setundef -zero
splitnets
opt_clean -purge

# --- reports + output ---
tee -o reports/synth_stat.txt stat -liberty $ASAP7_LIB
write_verilog -noattr results/myblock_asap7.v
```

If slang chokes on a construct, fall back to your existing sv2v step:

```bash
sv2v rtl/*.sv > build/myblock.v
# then in the .ys, replace the slang lines with:
#   read_verilog -sv build/myblock.v
#   hierarchy -check -top myblock
```

Run it:

```bash
export ASAP7_LIB=~/eda/asap7_merged/asap7sc7p5t_RVT_TT_nldm.lib
yosys -c synth_asap7.ys
```

`results/myblock_asap7.v` is your technology-mapped 7 nm netlist.

### 5.3 `dont_use` cells

ASAP7 has cells you generally want to exclude from mapping (certain
hold/area-pathological cells). Pull the current list from ORFS
(`platforms/asap7/config.mk`, `DONT_USE_CELLS`) and pass them to ABC/Yosys, e.g.
remove them from the merged lib or use `set_dont_use` in the SDC for STA. Skipping
this still synthesizes, but QoR and downstream APR can suffer.

---

## 6. Static timing on the netlist (OpenSTA)

Confirm clock-to-out / setup paths against the same Liberty:

```bash
# OpenSTA is bundled in OpenROAD; or build standalone from parallaxsw/OpenSTA
sta
```

```tcl
read_liberty $env(ASAP7_LIB)
read_verilog results/myblock_asap7.v
link_design myblock
read_sdc constraint.sdc
report_checks -path_delay max -fields {slew cap input nets} -format full_clock
report_checks -path_delay min      ;# hold
report_wns
report_tns
```

---

## 7. Gate-level functional sim (optional)

The mapped netlist references ASAP7 cells, so simulate with the PDK's Verilog
cell models (`asap7sc7p5t_28/Verilog/`) plus a UDP/primitives file:

```bash
verilator --binary --timing \
  results/myblock_asap7.v \
  ~/eda/asap7/asap7sc7p5t_28/Verilog/*.v \
  tb/myblock_tb.sv
```

cocotb drives this the same way as your RTL testbenches — just point the sim at
the netlist + cell models instead of the source RTL.

---

## 8. Known gotchas (ASAP7-specific)

- **4× drawn scale.** ASAP7 GDS/LEF is drawn at 4× and must be scaled by 0.25
  during APR. ORFS does this automatically; it only matters for Path A / physical
  steps. Synthesis timing in `.lib` is already in real units — netlist-only flows
  are unaffected.
- **Hierarchical synth segfaults.** Older Yosys + ASAP7 has reports of segfaults
  on hierarchical RISC-V-style cores. Mitigate with `-flatten` or the slang
  frontend (Path B already does both).
- **Single Liberty for ABC.** See §5.1 — the five-group split is the most common
  thing people trip on in a hand-rolled flow.
- **Relative, not absolute.** Worth repeating: don't quote ASAP7 ps/µm² numbers
  as "7 nm silicon." They're for methodology and cross-design comparison.
- **Routing layers.** Default ASAP7 APR routes signals on M2–M7, reserves M1 for
  intra-cell, and uses M8/M9 for power straps and clock trunks.

---

## 9. Minimal end-to-end checklist

1. `git clone --recurse-submodules` the ASAP7 PDK (§3.2).
2. Install tools — ORFS build (§3.3) **or** OSS CAD Suite + yosys-slang + sv2v (§3.4).
3. Drop RTL + SDC into a design dir.
4. **Path A:** `make ... synth` → `1_synth.v`; or full `make` → GDS.
   **Path B:** prepare merged RVT/TT Liberty → `yosys -c synth_asap7.ys` → netlist.
5. Verify timing with OpenSTA (§6); optionally gate-level sim (§7).
6. Add SRAM via FakeRAM2.0 if your design needs memory (§4.1).
