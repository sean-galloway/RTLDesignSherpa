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

`projects/components/bridge/fpga/` is an FPGA build directory in the
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

: Table 6.24: Synthesis flow knobs

```bash
cd projects/components/bridge/fpga
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

: Table 6.25: `summary.csv` columns

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

: Table 6.26: The CAM ordering-count scan, before and after (2026-09-11)

No simulation, formal proof or lint had a view of this: the block was
correct and its depth was invisible until synthesis. It is why the flow
exists and why it runs in minutes.

### The reference set

Nine generated fixtures cover the shapes the generator produces: the
baseline 2x2, its registered-crossbar, QoS, QoS-plus-registered and CDC
variants, a 4x4 with mixed widths, a shim-heavy mix, an AXI5 pair and a 5x3
with channel-specific masters. Each is constrained at 100 MHz on the Artix-7 and 150 MHz on the
Kintex-7, the clocks the Nexys A7 and Genesys 2 harnesses in this
repository run their fabrics at. Every row has zero unrouted nets, zero
block RAM and zero DSPs.

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 4,441 | 3,325 | 0 | +0.40 | 104.2 | 8 |
| `bridge_2x2_rw` | 4,615 | 3,253 | 0 | +0.12 | 101.2 | 9 |
| `bridge_2x2_rw_cdc` | 4,851 | 3,413 | 0 | +0.27 | 102.7 | 9 |
| `bridge_2x2_rw_pipe` | 5,646 | 4,227 | 0 | +1.27 | 114.6 | 6 |
| `bridge_2x2_rw_qos` | 5,136 | 3,317 | 0 | -2.91 | 77.4 | 14 |
| `bridge_2x2_rw_qos_pipe` | 5,494 | 4,291 | 0 | +0.17 | 101.7 | 9 |
| `bridge_4x4_rw` | 30,278 | 29,508 | 0 | -1.57 | 86.4 | 14 |
| `bridge_5x3_channels` | 19,243 | 16,932 | 0 | -2.66 | 79.0 | 16 |
| `bridge_mix_a` | 6,456 | 5,697 | 0 | -0.29 | 97.1 | 16 |

: Table 6.27: Reference set on the Artix-7 100T -1 (Nexys A7), constrained at 10 ns

| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |
|---|---:|---:|---:|---:|---:|---:|
| `bridge_2x2_axi5` | 4,430 | 3,325 | 0 | +0.69 | 167.4 | 9 |
| `bridge_2x2_rw` | 4,612 | 3,253 | 0 | +0.97 | 175.6 | 9 |
| `bridge_2x2_rw_cdc` | 4,842 | 3,413 | 0 | +0.55 | 163.4 | 9 |
| `bridge_2x2_rw_pipe` | 5,647 | 4,227 | 0 | +1.73 | 202.6 | 6 |
| `bridge_2x2_rw_qos` | 4,963 | 3,317 | 0 | -0.18 | 146.0 | 13 |
| `bridge_2x2_rw_qos_pipe` | 5,475 | 4,291 | 0 | +0.70 | 167.6 | 9 |
| `bridge_4x4_rw` | 29,719 | 29,508 | 0 | +0.28 | 156.5 | 13 |
| `bridge_5x3_channels` | 19,035 | 16,932 | 0 | -0.13 | 147.1 | 17 |
| `bridge_mix_a` | 6,375 | 5,697 | 0 | +0.53 | 162.9 | 8 |

: Table 6.28: Reference set on the Kintex-7 325T -2 (Genesys 2), constrained at 6.667 ns

### Reading the rows

- **Every 2x2 without QoS meets both targets**, AXI5 and CDC variants
  included. The CDC port adds one clock domain and about 240 LUTs and 160
  FFs for its five async FIFOs, and the crossing does not enter the fabric's
  critical path.
- **The registered crossbar is the timing option.** `xbar_pipeline` costs
  about 1,000 LUTs and 1,000 FFs on the 2x2 and cuts the worst path from
  9 levels to 6, the only row with more than a nanosecond of margin on the
  Artix-7.
- **Every Artix-7 miss is the same path**: a master adapter's request
  register, through the crossbar's arbitration and address/ID mux, into the
  slave adapter's CAM allocate (the ID compare against every entry, then
  the popcount), with routing at 75-80% of the delay. QoS adds its priority
  compare in series with the grant and misses 10 ns by 2.9 ns; the wide
  4x4 and the 5x3 miss by 1.6 and 2.7 ns on the same shape; the shim mix by
  0.3 ns. `bridge_2x2_rw_qos_pipe` is the demonstration: the same QoS
  arbiter behind the registered crossbar meets 10 ns with margin
  (-2.91 ns becomes +0.17 ns, 14 levels become 9). On the Artix-7 at
  100 MHz, a configuration with more than two masters, wide ports or QoS
  should be generated with `xbar_pipeline = true`; on the Kintex-7 at
  150 MHz only QoS-without-pipeline and the 5x3 fall short, by fractions of
  a nanosecond.
- **Width steps set the size.** The 4x4 with 32/64/128/256-bit ports is
  six times the 2x2 in both LUTs and FFs: every converter carries a full
  wide beat, in each direction, per path.
- **No block RAM, no DSPs, anywhere.** The CAM and the bridge-id FIFOs are
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
