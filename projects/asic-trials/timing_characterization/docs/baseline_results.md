# Baseline Results -- Cross-Technology Comparison

Generated 2026-09-29 by `fpga/tools/baseline_report.py` from the sweep CSVs under `fpga/reports/`. Do not edit the numbers here; rerun the sweep and this script.

The constraint is the same on every target -- `rtl/syn/char_top.sdc`: a single clock at the target frequency, 80 % of the period as input delay, 20 % as output delay, 100 ps uncertainty. The point of the design is NOT to close timing; it is to read how far each FUB's combinational path falls short as the target tightens (README.md section 1). Two FPGA technologies are compared here: Artix-7 (Xilinx, 28 nm, Vivado, the Nexys A7 part) and Cyclone V GX (Intel, 28 nm, Quartus Prime Lite). The ASAP7 numbers live in `work/timing_char_data.csv` and the ASIC paper.

## 1. Frequency sweep, Artix-7 (Vivado, `make bitstream-sweep`)

Full place-and-route of the board wrapper `char_top_fpga` on xc7a100tcsg324-1, all nine FUBs enabled. WNS is post-route, per clock group; `met` is WNS >= 0.

| target MHz | period ns | clock group | WNS ns | met | LUTs | FFs | BRAM | DSP |
|---:|---:|---|---:|---|---:|---:|---:|---:|
| 100 | 10.0 | sys_clk_pin | 1.132 | yes | 449 | 319 | 0 | 1 |
| 200 | 5.0 | sys_clk_pin | -0.722 | no | 580 | 346 | 0 | 1 |
| 300 | 3.3333 | sys_clk_pin | -2.017 | no | 644 | 362 | 0 | 1 |

Vivado reports one number per clock group, not per FUB; the per-FUB view on this target is the `timing_worst.txt` in each `fpga/reports/sweep_<F>MHz/` archive.

## 2. Frequency sweep, Cyclone V GX (Quartus, `make quartus-sweep`)

`char_top` itself (no board wrapper) on 5CGXFC5C6F27C7, all nine FUBs, map + fit + STA per point. Slack is setup slack at the slow 85C corner from `fub_slack.csv` (`fpga/quartus/sta_reports.tcl`): the worst register-to-register path launched from each FUB's flops, then the worst path from those flops to ANY endpoint (`.io`, which carries the 20 % output-delay budget). The `design` row is the worst path anywhere.

| path | 100 MHz | 150 MHz | 200 MHz | 250 MHz | 300 MHz |
|---|---:|---:|---:|---:|---:|
| clock `clk`, slow 85C corner, worst setup slack | -2.384 | -5.049 | -6.642 | -7.462 | -9.343 |
| `design` worst path anywhere (ports included) | -2.384 | -5.049 | -6.642 | -7.462 | -9.343 |
| `nand` reg-to-reg worst slack | 4.836 | 1.464 | -0.560 | -1.277 | -3.736 |
| `inv` reg-to-reg worst slack | 7.241 | 5.489 | -0.196 | 2.850 | -0.898 |
| `xor` reg-to-reg worst slack | 2.935 | -1.226 | -0.955 | -0.602 | -2.238 |
| `carry` reg-to-reg worst slack | 3.129 | -0.529 | -2.504 | -3.743 | -4.232 |
| `mult` reg-to-reg worst slack | 1.362 | 0.058 | -2.450 | -4.700 | -4.303 |
| `mux` reg-to-reg worst slack | 3.554 | -1.414 | -2.496 | -1.991 | -2.917 |
| `queue` reg-to-reg worst slack | 2.400 | 0.161 | -2.452 | -3.823 | -4.352 |
| `clkdiv` reg-to-reg worst slack | 7.449 | 4.116 | 2.474 | 1.568 | 0.710 |
| `gray` reg-to-reg worst slack | 2.712 | 2.242 | -0.729 | -1.298 | -1.444 |
| `nand.io` worst slack incl. output ports | -0.067 | -2.578 | -4.202 | -4.956 | -5.143 |
| `inv.io` worst slack incl. output ports | 0.323 | -2.536 | -3.711 | -4.832 | -5.312 |
| `xor.io` worst slack incl. output ports | -0.211 | -2.349 | -3.866 | -4.800 | -5.386 |
| `carry.io` worst slack incl. output ports | -0.226 | -2.607 | -4.267 | -5.011 | -5.610 |
| `mult.io` worst slack incl. output ports | -0.206 | -2.909 | -4.226 | -5.204 | -5.515 |
| `mux.io` worst slack incl. output ports | -0.161 | -2.223 | -3.777 | -5.000 | -5.417 |
| `queue.io` worst slack incl. output ports | -2.384 | -5.049 | -6.642 | -7.462 | -9.343 |
| `clkdiv.io` worst slack incl. output ports | -1.913 | -4.661 | -6.061 | -6.998 | -7.400 |
| `gray.io` worst slack incl. output ports | -0.301 | -3.083 | -3.951 | -5.222 | -5.749 |

### 2.1 Per-FUB data-path delay and logic levels

Delay is what the fitter achieved for that FUB's worst reg-to-reg path at each target; it moves with placement effort, so read the trend across FUBs, not the third decimal.

| FUB | data-path delay ns (worst reg-to-reg path, per target) | logic levels |
|---|---|---:|
| `nand` | 100: 5.886, 150: 6.018, 200: 6.218, 250: 5.956, 300: 7.365 | 3/4/5 |
| `inv` | 100: 3.398, 150: 1.647, 200: 5.578, 250: 1.627, 300: 4.842 | 0 |
| `xor` | 100: 7.746, 150: 8.106, 200: 6.252, 250: 5.267, 300: 6.286 | 3/4/5 |
| `carry` | 100: 7.481, 150: 7.638, 200: 7.659, 250: 7.709, 300: 7.529 | 1 |
| `mult` | 100: 8.617, 150: 6.890, 200: 7.537, 250: 8.942, 300: 8.177 | 0 |
| `mux` | 100: 7.101, 150: 8.759, 200: 7.861, 250: 6.661, 300: 6.932 | 4/5 |
| `queue` | 100: 8.202, 150: 5.300, 200: 7.624, 250: 6.222, 300: 6.190 | 1/3 |
| `clkdiv` | 100: 1.706, 150: 1.749, 200: 1.683, 250: 1.654, 300: 1.785 | 1 |
| `gray` | 100: 8.531, 150: 5.041, 200: 5.807, 250: 5.910, 300: 5.622 | 0/1 |

Resources at every point (full char_top, all FUBs): 746 ALMs, 1559 registers, 1 RAM block(s), 1 DSP block(s).

## 3. Parameter sweeps, Cyclone V GX (Quartus)

One FUB enabled at a time, `VIRTUAL_PINS 1`, target 150 MHz (`fpga/quartus/sweeps/<name>.tcl`; `make quartus-sweep QUARTUS_CFG=quartus/sweeps/<name>.tcl QUARTUS_REPORTS_SUB=<name>`). The row is that FUB's worst reg-to-reg path.

### 3.1 carry-chain adder width

Target 150 MHz.

| `CARRY_WIDTH` | reg-to-reg slack ns | data-path delay ns | logic levels | ALMs | registers | DSP |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | 4.334 | 2.154 | 1 | 121 | 61 | 0 |
| 16 | 3.887 | 2.594 | 1 | 135 | 83 | 0 |
| 32 | 3.618 | 2.832 | 1 | 163 | 137 | 0 |
| 64 | 3.131 | 3.333 | 1 | 219 | 231 | 0 |
| 128 | 2.450 | 4.029 | 1 | 331 | 429 | 0 |
| 256 | 0.912 | 5.086 | 1 | 555 | 808 | 0 |

- `logic levels` stays 1 at every width: the adder rides the ALM carry chain, so what grows is the chain's propagation, not a LUT count -- the data-path delay column is the measurement.

### 3.2 NAND tree depth

Target 150 MHz.

| `NAND_LEVELS` | reg-to-reg slack ns | data-path delay ns | logic levels | ALMs | registers | DSP |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 4.120 | 2.356 | 2 | 148 | 52 | 0 |
| 6 | 3.028 | 3.423 | 3 | 173 | 105 | 0 |
| 8 | 2.041 | 4.406 | 4 | 278 | 302 | 0 |
| 10 | 1.730 | 4.722 | 4 | 491 | 699 | 0 |
| 12 | 0.707 | 5.269 | 5 | 927 | 1051 | 0 |

- `NUM_FLOPS` is raised to 4096 for this sweep. char_top clamps the leaf count to NUM_FLOPS (`NAND_ACTUAL_FLOPS`) and wraps the leaves; with the default 256 the 8/10/12-level points folded to one identical netlist (278 ALMs, 4 LUT levels) on the first run, which measured the clamp, not the tree.
- Quartus counts LUT levels, not NAND gates; an ALM absorbs about two tree levels.

### 3.3 multiplier architecture (0 inferred/DSP, 1 dadda, 2 wallace, 3 wallace_csa, 4 dadda_4to2)

Target 150 MHz.

| `MULT_TYPE` | reg-to-reg slack ns | data-path delay ns | logic levels | ALMs | registers | DSP |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 3.724 | 2.731 | 0 | 139 | 47 | 1 |
| 1 | -1.981 | 8.446 | 8 | 471 | 280 | 0 |
| 2 | -3.002 | 9.463 | 10 | 464 | 267 | 0 |
| 3 | -1.981 | 8.446 | 8 | 471 | 280 | 0 |
| 4 | 3.724 | 2.731 | 0 | 139 | 47 | 1 |

- Type 4 (Dadda with 4:2 compressors) is implemented for widths 8, 11 and 24 only; at the default `MULT_WIDTH = 16` `multiplier_tree.sv` falls back to the inferred multiplier, so its row equals type 0 by construction (the RTL header says so). Sweep it with `MULT_WIDTH 8` or `24` to see it.
- Types 1 and 3 synthesized to the same ALM count, register count and delay although their sources differ (`math_multiplier_dadda_tree_016.sv` vs `math_multiplier_wallace_tree_csa_016.sv`): read that as the fitter reducing both trees to the same structure, not as two measured architectures.
- Type 0 lands in one DSP block and shows 0 LUT levels; that is the DSP-vs-LUT comparison the task asked for: one DSP delay against an 8-10 level LUT tree at 3x the ALMs.

## 4. Reading across technologies

- The two 28 nm FPGA fabrics are compared on the same RTL and the same SDC, but not the same top: the Artix-7 numbers include the Nexys A7 board wrapper and real pins, the Cyclone V numbers are the bare `char_top` with real pins (frequency sweep) or virtual pins (parameter sweeps). Compare slopes, not absolute slack.
- Vivado's per-clock WNS and Quartus' per-FUB slack are different cuts of the same question; the Quartus `design` row is the like-for-like number against Vivado's WNS.
- `mult` shows 0 logic levels on Cyclone V: the inferred multiplier lands in a DSP block, so its path is one DSP delay, not a LUT count. The `MULT_TYPE` sweep is where DSP and LUT trees meet.
- Resource columns are not comparable across vendors (an ALM is not a LUT); use them within a target.

