<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->
# Synthesis and Implementation

## Overview

Everything before this page is about what a generated bridge does. This page
is about what it costs and how fast it closes, measured rather than
estimated: a worked Vivado flow that takes any generated bridge through
synthesis, placement and routing as a stand-alone block, the numbers it
produced for a reference set of configurations on the two parts this
repository's boards carry, and how to read and repeat them. Chapter 5.3
carries the resource tables; this chapter is the flow behind them.

## The Flow

### Where it lives

`projects/components/fabric-gen-ip/bridge/fpga/` is an FPGA build directory in the
repository's standard shape (handbook `fpga/cmn-infra/build-flows`): a
Makefile of variables that includes `make/fpga_flow.mk`, a `tcl/` directory
the flow discovers, and `reports/`. It builds no bitstream. Its one script,
`synth_only.tcl`, is a non-project batch run: read the bridge's filelist
closure, synthesize the bridge as the top with no pins (Vivado's
out-of-context mode), constrain its clocks, place and route, and write
reports.

| Knob | Default | Meaning |
|---|---|---|
| `BRIDGE` | `bridge_2x2_rw` | any generated fixture; the top module and the filelist follow from the name |
| `PART` | `xc7a100tcsg324-1` | the Artix-7 on the Nexys A7; `xc7k325tffg900-2` is the Kintex-7 on the Genesys 2 |
| `CLK_NS` | `10.0` | the period every clock is constrained to |

: Synthesis flow knobs

```bash
cd projects/components/fabric-gen-ip/bridge/fpga
make lint  BRIDGE=bridge_2x2_rw_cdc                 # verilator on the same closure, seconds
make synth BRIDGE=bridge_2x2_rw                     # one run, a few minutes
make synth BRIDGE=bridge_4x4_rw PART=xc7k325tffg900-2 CLK_NS=6.667
bin/synth_sweep.sh                                  # the reference set, both parts
bin/summary_table.py                                # reports/summary.csv as the tables below
```

Each run leaves `reports/<bridge>__<part>/` (utilization after synthesis and
after routing, a per-instance utilization breakdown, the timing summary, the
twenty worst paths overall and register-to-register, the clock-interaction
and CDC reports, and a `summary.txt`) and appends one line to
`reports/summary.csv`. Two bridges, or one bridge on two parts, never
overwrite each other. The flow's build lock serializes Vivado runs in the
directory, so the sweep is deliberately one run at a time.

### How the bridge is constrained

The flow reads the constraints off the bridge's port list, so a new fixture
needs nothing written by hand:

- **Clocks.** Every port whose name ends in `aclk` gets a clock of `CLK_NS`.
  A single-domain bridge gets one; a bridge with CDC slave ports (HAS 4.5a)
  gets one per domain, and the domains are declared asynchronous to each
  other, which is exactly how a system would constrain it. The crossing
  itself is then checked by the CDC report, not by setup analysis across it.
- **Resets.** Every `*aresetn` input is a false path. Reset is asynchronous
  on assertion in every generated build (MAS 6.1) and deassertion is
  synchronized outside the bridge.
- **Data I/O.** Inputs arrive, and outputs must be valid, 30% of the period
  into the cycle, against the clock of the port they belong to. This is the
  ordinary out-of-context convention for a block whose neighbours are
  registered; it is not a property of the bridge, which is why the
  register-to-register slack is reported on its own and is the figure the
  tables below quote.
- **Defines.** `XILINX` is set so `bridge_cam` takes its distributed-RAM
  attributes; Vivado sets `SYNTHESIS` itself, which removes the
  simulation-only checkers in the crossbar and subtractive adapter.

### Reading the summary line

| Column | What it is |
|---|---|
| `luts`, `ffs`, `bram_tiles`, `dsps` | post-route utilization of the whole bridge |
| `wns_ns` | worst setup slack over every path, I/O budget included |
| `wns_reg2reg_ns` | worst setup slack between registers inside the bridge |
| `fmax_reg2reg_mhz` | `1000 / (CLK_NS - wns_reg2reg_ns)`: the clock the internal paths would close at, estimated at this constraint |
| `worst_logic_levels` | LUT depth of the worst internal path |
| `unrouted_nets` | must be 0; anything else is a failed run, not a slow one |

: `summary.csv` columns

The Fmax column is an estimate at the period you constrained. Vivado stops
optimizing a path once it has margin, so a bridge that shows +2 ns of slack
at 10 ns is not guaranteed to close at 8 ns until you run it at 8 ns. The
handbook's rule applies (`fpga/cmn-infra/timing-closure`): when a run does
fail, look at the magnitude, the clock interaction and the logic levels, in
that order, before touching the RTL.

## Measured Results

### What the first run found

The first bridge through this flow, `bridge_2x2_rw` on the Artix-7 at
10 ns, failed timing by 22 ns with every functional test green. The worst
path ran from a master adapter's tracking pointer, through the crossbar's
AR arbitration and mux, into the slave adapter's CAM: 40 LUT levels, a 32 ns
data path, 83% of it routing. The CAM's Mode-2 allocate computed a
newcomer's ordering count as the largest count among the entries with the
same ID, written as a loop over the 16 entries, and that loop synthesized to
sixteen chained comparators hanging off the arbitrated ARID (MAS 4.1). The
counts of one ID are always `0..k-1`, so the value is the number of matching
entries, a popcount; the entry to retire, the one match with count 0, is
one-hot, so its index and stored master are OR reductions. With that change
the same bridge meets 10 ns.

| `bridge_2x2_rw`, Artix-7 100T -1, 10 ns | Before | After |
|---|---:|---:|
| LUTs | 5,824 | 4,615 |
| FFs | 3,253 | 3,253 |
| WNS register-to-register (ns) | -22.27 | +0.12 |
| Worst logic levels | 40 | 9 |
| Fmax estimate (MHz) | 31 | 101 |

: The CAM ordering-count scan, before and after (2026-09-11)

No simulation, formal proof or lint had a view of this: the block was
correct and its depth was invisible until synthesis. It is why the flow
exists and why it runs in minutes.

### The reference set

Ten generated fixtures cover the shapes the generator produces: the
baseline 2x2, its registered-crossbar, QoS, QoS-plus-registered and CDC
variants, a 4x4 with mixed widths, a shim-heavy mix, a 32-bit AXI5 pair, the
128-bit native-AXI5 2x2 with Memory Tagging and chunking on every port, and
a 5x3 with channel-specific masters. Each is constrained at 100 MHz on the Artix-7 and 150 MHz on the
Kintex-7, the clocks the Nexys A7 and Genesys 2 harnesses in this
repository run their fabrics at. Every row has zero unrouted nets, zero
block RAM and zero DSPs.

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 5,120 | 4,013 | 0 | -0.11 | 98.9 | 10 |
| `bridge_2x2_axi5_native` | 8,252 | 6,773 | 0 | -1.20 | 89.3 | 11 |
| `bridge_2x2_rw` | 5,832 | 4,605 | 0 | -0.04 | 99.6 | 11 |
| `bridge_2x2_rw_cdc` | 5,184 | 4,021 | 0 | +0.07 | 100.7 | 11 |
| `bridge_2x2_rw_pipe` | 5,569 | 4,869 | 0 | +0.57 | 106.1 | 8 |
| `bridge_2x2_rw_qos` | 5,344 | 3,925 | 0 | -0.28 | 97.3 | 11 |
| `bridge_2x2_rw_qos_pipe` | 5,932 | 4,933 | 0 | -0.02 | 99.8 | 12 |
| `bridge_4x4_rw` | 40,239 | 38,241 | 0 | -3.01 | 76.9 | 15 |
| `bridge_5x3_channels` | 30,835 | 28,051 | 0 | -3.21 | 75.7 | 15 |
| `bridge_mix_a` | 7,994 | 6,623 | 0 | -2.10 | 82.6 | 13 |

: Reference set on the Artix-7 100T -1 (Nexys A7), constrained at 10 ns

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 4,949 | 4,013 | 0 | +0.59 | 164.6 | 11 |
| `bridge_2x2_axi5_native` | 8,119 | 6,773 | 0 | +0.47 | 161.3 | 12 |
| `bridge_2x2_rw` | 5,682 | 4,605 | 0 | +0.56 | 163.8 | 10 |
| `bridge_2x2_rw_cdc` | 5,030 | 4,021 | 0 | +0.26 | 156.0 | 10 |
| `bridge_2x2_rw_pipe` | 5,564 | 4,869 | 0 | +1.14 | 180.8 | 9 |
| `bridge_2x2_rw_qos` | 5,176 | 3,925 | 0 | +0.48 | 161.6 | 11 |
| `bridge_2x2_rw_qos_pipe` | 5,886 | 4,933 | 0 | +0.53 | 163.0 | 11 |
| `bridge_4x4_rw` | 40,042 | 38,241 | 0 | -0.14 | 146.8 | 13 |
| `bridge_5x3_channels` | 30,712 | 28,051 | 0 | -0.68 | 136.1 | 15 |
| `bridge_mix_a` | 7,844 | 6,623 | 0 | +0.30 | 157.1 | 13 |

: Reference set on the Kintex-7 325T -2 (Genesys 2), constrained at 6.667 ns

### Reading the rows

Re-measured 2026-10-16 (rev 1.3) on the generator of that date: per-ID
target tracking (GitHub #119 L1), trackers sized by `max_outstanding` (L5),
latency modes (L7), the registered CAM insert and free, the per-ID gate
built from registered flags, and width converters without the read
reassembly pool and with a registered B input. The 2026-09-11 rows these
replace predate all of it. Rows within about 0.3 ns of zero move by that
much from run to run with placement; read them as "at the target".

- **The 2x2s are at 100 MHz on the Artix-7 and 150 MHz on the Kintex-7.**
  On the Artix-7 every 2x2 except the native-AXI5 one is within 0.3 ns of
  10 ns, and `bridge_2x2_rw_pipe` closes with +0.57 ns. Every 2x2 meets
  6.667 ns on the Kintex-7. `bridge_2x2_rw` grew from 4,615 LUTs and 3,253
  FFs to about 5,800 and 4,600: the per-ID target tables, the CAM's
  pending-insert and pending-free registers, and the gate's registered
  flags.
- **The September CAM-allocate path is gone,** taken out by the registered
  CAM insert; no row's worst path ends at a CAM allocate.
- **QoS is back at 100 MHz.** In September it missed by 2.91 ns
  (`bridge_2x2_rw_qos`). The per-ID gate the arbitration sees in series is
  now a 1-bit lookup and a one-hot AND (registered busy and full flags), so
  QoS and QoS behind the registered crossbar are at the target on the
  Artix-7 and close on the Kintex-7.
- **The native-AXI5 2x2 misses the Artix-7 by 1.2 ns:** 128-bit beats with
  every AMBA5 feature on every port, route-dominated. It meets the Kintex-7.
- **Converter fixtures are measurable again and much closer.** Until
  2026-10-16, every read width converter carried a 16 x 272-beat
  reassembly pool (about 128k LUTs each). `bridge_mix_a` did not fit the
  Artix-7 and `bridge_4x4_rw` did not finish synthesis. With the pool gone
  (`R_INTERLEAVE = 0`, legal because slaves may not interleave R), the
  write converter's B input registered and its CAM match one-hot:
  - `bridge_4x4_rw` went from -7.5 to -3.0 ns on the Artix-7 and is at the
    target on the Kintex-7 (-0.14 ns);
  - `bridge_5x3_channels` is -3.2 / -0.7 ns;
  - `bridge_mix_a` is -2.1 ns / met.
- **What those three still miss on is wide-path routing.** Their worst paths
  are route-dominated (78-83% route): the 256-bit R data return through a
  crossbar response mux into a master's R skid (5x3), and a slave CAM's
  pending free into its count array (mix_a). `xbar_pipeline` registers the
  response path, and none of these three fixtures uses it.
- **Width steps set the size.** The 4x4 with 32/64/128/256-bit ports is
  about seven times the 2x2: every converter carries a full wide beat each
  way, per path.
- **No block RAM, no DSPs, anywhere.** The CAMs, trackers and FIFOs are
  LUT arrays; there is no arithmetic.

## Design Notes

### What moves the numbers

- **Data width** sets the register count almost linearly: every skid buffer
  and every crossbar stage holds a full beat.
- **Masters x slaves** sets the crossbar's mux width and the arbiter count;
  the master adapters and slave adapters scale with their own counts.
- **`xbar_pipeline`** adds one 2-deep skid per slave-side channel (MAS 2.3),
  paid in registers, and returns it as the shorter worst path.
- **Protocol shims and width converters** are the expensive ports: an APB or
  AXI-Lite slave carries a converter plus its own monitor sandwich, a width
  step carries a converter each way.
- **CDC slave ports** add one async FIFO per channel (HAS 4.5a); the cost is
  the FIFO storage, and the crossing does not enter the fabric's critical
  path.

### Before a board build

Run this flow first. It takes minutes, it needs no constraints file, and it
answers "does this configuration fit and close on this part" before a
harness, a clock wizard and a pinout are wrapped around it.
