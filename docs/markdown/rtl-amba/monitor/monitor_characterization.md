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

# Monitor Characterization

**What this is:** the measured cost of every monitor variant in `rtl/amba`,
on the two parts the repo's boards carry, from one repeatable flow. It
answers "what does adding a monitor to this port cost, in LUTs, flops,
timing and (estimated) power, and how do the variants compare". Written for
amba TASK-034 on 2026-09-28; re-run it rather than trusting it once the RTL
moves.

**How to reproduce:**

```
rtl/amba/fpga/bin/monitor_synth_sweep.sh                 # Kintex-7 325T -2 at 6.667 ns (Genesys 2)
TARGETS="xc7a100tcsg324-1:10.0" rtl/amba/fpga/bin/monitor_synth_sweep.sh <modules...>
rtl/amba/fpga/bin/summary_table.py                        # the tables below, from reports/summary.csv
```

Each module is synthesized, placed and routed **out of context** by
`rtl/amba/fpga/tcl/monitor_synth.tcl` -- the same recipe as the bridge
fixture (`projects/components/bridge/fpga`): Vivado 2025.1, one clock at the
stated period, 30 % input/output delays, reset false-pathed. Utilization is
post-route. Power is Vivado's vectorless estimate (`report_power`, confidence
"Medium"): it ranks variants against each other and says nothing absolute.

## What was measured

Every module at its **default parameters** (the wrapper's own defaults, not
the bridge's), so the numbers here are larger than the bridge fixture's
per-instance figures in [axi_monitor_lite.md](axi_monitor_lite.md): the
lite there has the bridge's parameters; here it has its own defaults.

| Family | Modules | Defaults that set the size |
|---|---|---|
| AXI4 read master | `axi4_master_rd` (plain), `_cg`, `_mon`, `_mon_cg`, `_monlite`, `_monlite_cg` | ID 8, addr 32, data 32; full monitor 16 slots; lite 8 slots; skids AR 2 / R 4 |
| AXI4 write master | `axi4_master_wr` (plain), `_mon`, `_monlite` | as above |
| AXI4 read slave | `axi4_slave_rd` (plain), `_mon`, `_monlite` | as above |
| AXI5 read master | `axi5_master_rd` (plain), `_mon`, `_monlite` | as above |
| AXI-Lite read/write master | `axil4_master_rd`, `axil4_master_wr` (plain), `_mon`, `_monlite`; `axil5_master_rd_monlite` | addr 32, data 32 |
| APB | `apb4_monitor`, `apb5_monitor` | 4 slots, FIFO 8 |
| AXIS | `axis4_master_monlite`, `_cg` | data 32, ID 8, skid 4 |
| Wishbone | `wb4_monitor` | 8 slots, FIFO 8 |
| Aggregation | `monbus_arbiter` (4 clients), `monbus_axil4_axil4_group`, `monbus_axi4_axi4_group` | group: error FIFO 64 records, write FIFO 96 beats, raw records |

The `_mon` wrappers embed the full monitor (`axi_monitor_base`), the
`_monlite` wrappers the lite (`axi_monitor_lite`); the plain block is the
same master or slave without a monitor, so **wrapper minus plain is the
monitor**. `_cg` adds the clock-gating controller.


### Kintex-7 325T -2 (Genesys 2), clock constrained at 6.667 ns, out of context

| Module | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | WNS incl. I/O (ns) | Worst logic levels | Dynamic power (est.) |
|---|---:|---:|---:|---:|---:|---:|---:|
| `apb4_monitor` | 572 | 653 | 0 | +0.939 | +0.939 | 12 | 18 mW |
| `apb5_monitor` | 594 | 676 | 0 | +0.596 | +0.596 | 15 | 19 mW |
| `axi4_master_rd` | 285 | 328 | 0 | +3.861 | +1.515 | 2 | 7 mW |
| `axi4_master_rd_cg` | 308 | 342 | 0 | +1.711 | +1.029 | 3 | 5 mW |
| `axi4_master_rd_mon` | 7,291 | 5,547 | 0 | +0.477 | -0.166 | 12 | 76 mW |
| `axi4_master_rd_mon_cg` | 7,372 | 5,561 | 0 | -0.608 | -0.608 | 10 | 83 mW |
| `axi4_master_rd_monlite` | 1,400 | 1,355 | 0 | +2.145 | +1.005 | 5 | 17 mW |
| `axi4_master_rd_monlite_cg` | 1,421 | 1,369 | 0 | +1.619 | +0.854 | 12 | 20 mW |
| `axi4_master_wr` | 297 | 332 | 0 | +4.306 | +1.515 | 2 | 7 mW |
| `axi4_master_wr_mon` | 8,492 | 6,160 | 0 | -1.053 | -1.546 | 13 | 77 mW |
| `axi4_master_wr_monlite` | 1,511 | 1,414 | 0 | +2.046 | +0.910 | 13 | 18 mW |
| `axi4_slave_rd` | 285 | 328 | 0 | +3.861 | +1.515 | 2 | 7 mW |
| `axi4_slave_rd_mon` | 7,269 | 5,552 | 0 | +0.566 | +0.067 | 9 | 72 mW |
| `axi4_slave_rd_monlite` | 1,400 | 1,355 | 0 | +2.139 | +1.179 | 6 | 16 mW |
| `axi5_master_rd` | 380 | 444 | 0 | +3.981 | +1.503 | 2 | 10 mW |
| `axi5_master_rd_mon` | 7,387 | 5,663 | 0 | +0.501 | +0.023 | 12 | 77 mW |
| `axi5_master_rd_monlite` | 1,495 | 1,471 | 0 | +1.948 | +0.876 | 6 | 18 mW |
| `axil4_master_rd` | 214 | 218 | 0 | +4.378 | +1.505 | 2 | 4 mW |
| `axil4_master_rd_mon` | 3,105 | 2,854 | 0 | +1.432 | +0.408 | 7 | 42 mW |
| `axil4_master_rd_monlite` | 1,143 | 1,156 | 0 | +1.889 | +1.011 | 9 | 14 mW |
| `axil4_master_wr` | 179 | 164 | 0 | +4.392 | +1.515 | 2 | 3 mW |
| `axil4_master_wr_mon` | 3,481 | 2,955 | 0 | +0.722 | +0.163 | 6 | 44 mW |
| `axil4_master_wr_monlite` | 1,209 | 1,156 | 0 | +2.055 | +1.515 | 9 | 15 mW |
| `axil5_master_rd_monlite` | 1,221 | 1,272 | 0 | +1.936 | +1.044 | 6 | 15 mW |
| `axis4_master_monlite` | 1,550 | 935 | 0 | +1.867 | +0.363 | 6 | 29 mW |
| `axis4_master_monlite_cg` | 1,570 | 949 | 0 | +1.695 | +0.308 | 3 | 22 mW |
| `monbus_arbiter` | 1,821 | 1,972 | 0 | +2.937 | +2.295 | 2 | 17 mW |
| `monbus_axi4_axi4_group` | 1,967 | 1,386 | 0 | +1.366 | -1.728 | 13 | 35 mW |
| `monbus_axil4_axil4_group` | 1,715 | 1,154 | 0 | +1.152 | -2.004 | 11 | 31 mW |
| `wb4_monitor` | 622 | 909 | 0 | +0.731 | +0.731 | 16 | 27 mW |

#### The monitor's own cost (Kintex-7 325T -2 (Genesys 2)): wrapper minus the plain block

| Monitored wrapper | Wraps | Monitor LUTs | Monitor FFs | Wrapper WNS reg-to-reg (ns) | Plain WNS reg-to-reg (ns) |
|---|---|---:|---:|---:|---:|
| `axi4_master_rd_mon` | `axi4_master_rd` | 7,006 | 5,219 | +0.477 | +3.861 |
| `axi4_master_rd_monlite` | `axi4_master_rd` | 1,115 | 1,027 | +2.145 | +3.861 |
| `axi4_master_rd_mon_cg` | `axi4_master_rd_cg` | 7,064 | 5,219 | -0.608 | +1.711 |
| `axi4_master_rd_monlite_cg` | `axi4_master_rd_cg` | 1,113 | 1,027 | +1.619 | +1.711 |
| `axi4_master_wr_mon` | `axi4_master_wr` | 8,195 | 5,828 | -1.053 | +4.306 |
| `axi4_master_wr_monlite` | `axi4_master_wr` | 1,214 | 1,082 | +2.046 | +4.306 |
| `axi4_slave_rd_mon` | `axi4_slave_rd` | 6,984 | 5,224 | +0.566 | +3.861 |
| `axi4_slave_rd_monlite` | `axi4_slave_rd` | 1,115 | 1,027 | +2.139 | +3.861 |
| `axi5_master_rd_mon` | `axi5_master_rd` | 7,007 | 5,219 | +0.501 | +3.981 |
| `axi5_master_rd_monlite` | `axi5_master_rd` | 1,115 | 1,027 | +1.948 | +3.981 |
| `axil4_master_rd_mon` | `axil4_master_rd` | 2,891 | 2,636 | +1.432 | +4.378 |
| `axil4_master_rd_monlite` | `axil4_master_rd` | 929 | 938 | +1.889 | +4.378 |
| `axil4_master_wr_mon` | `axil4_master_wr` | 3,302 | 2,791 | +0.722 | +4.392 |
| `axil4_master_wr_monlite` | `axil4_master_wr` | 1,030 | 992 | +2.055 | +4.392 |

### Artix-7 100T -1 (Nexys A7), clock constrained at 10.000 ns, out of context

| Module | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | WNS incl. I/O (ns) | Worst logic levels | Dynamic power (est.) |
|---|---:|---:|---:|---:|---:|---:|---:|
| `apb4_monitor` | 580 | 653 | 0 | +0.152 | +0.152 | 13 | 12 mW |
| `axi4_master_rd` | 285 | 328 | 0 | +5.969 | +1.895 | 2 | 5 mW |
| `axi4_master_rd_mon` | 7,636 | 5,547 | 0 | -0.868 | -1.451 | 12 | 49 mW |
| `axi4_master_rd_monlite` | 1,403 | 1,355 | 0 | +2.097 | +0.617 | 14 | 10 mW |
| `axi4_master_rd_monlite_cg` | 1,421 | 1,369 | 0 | +1.095 | +0.341 | 13 | 15 mW |
| `axil4_master_rd_monlite` | 1,144 | 1,156 | 0 | +1.478 | +0.393 | 11 | 9 mW |
| `axis4_master_monlite` | 1,550 | 935 | 0 | +1.646 | +0.599 | 6 | 20 mW |
| `axis4_master_monlite_cg` | 1,571 | 949 | 0 | +1.652 | +0.303 | 6 | 15 mW |
| `monbus_axil4_axil4_group` | 1,725 | 1,154 | 0 | +0.111 | -4.920 | 8 | 21 mW |
| `wb4_monitor` | 622 | 909 | 0 | +0.045 | +0.045 | 16 | 18 mW |

#### The monitor's own cost (Artix-7 100T -1 (Nexys A7)): wrapper minus the plain block

| Monitored wrapper | Wraps | Monitor LUTs | Monitor FFs | Wrapper WNS reg-to-reg (ns) | Plain WNS reg-to-reg (ns) |
|---|---|---:|---:|---:|---:|
| `axi4_master_rd_mon` | `axi4_master_rd` | 7,351 | 5,219 | -0.868 | +5.969 |
| `axi4_master_rd_monlite` | `axi4_master_rd` | 1,118 | 1,027 | +2.097 | +5.969 |

The "WNS incl. I/O" column carries the out-of-context I/O budget: every data
pin is given 30 % of the period, so a block whose configuration inputs feed
logic directly (the groups' `cfg_*_mask` pins, the AXIS lite's
`cfg_timeout_cycles`) shows a primary-input miss that a real design, where
those pins come from CSR flops nearby, does not have. The register-to-register
column is the block's own timing and is the one to read.

## What the numbers say

**Full monitor against lite.** At their defaults the full AXI monitor is
about 7,000 LUTs and 5,200 flops (16 slots, the CAM-based transaction
manager, six reporter cones); the lite is about 1,100 LUTs and 1,030 flops
(8 slots, linked lists, one event stage): 6.3x in LUTs, 5x in flops, on the
same read, write, slave and AXI5 wrappers alike, because the monitor is the
same core behind every one. On AXI-Lite the ratio is 3x (2,900 against 930):
the ID-less path removes most of the full monitor's matching logic and
leaves the lite's fixed costs. The lite in the bridge fixture measured 677
LUTs ([axi_monitor_lite.md](axi_monitor_lite.md)) because the bridge sets
narrower IDs and fewer slots; both figures are right for their parameters,
and the ratio to the full monitor is the number that carries.

**Timing.** Every lite variant meets 6.667 ns on the Kintex-7 with 0.8 to
1.5 ns to spare, register to register. The full AXI4 monitors at 16 slots do
not: the read master misses by 0.17 ns, the write master by 1.55 ns, and the
worst path in each is inside `monitor_trans_cam` (`g_slot[n]` compare and
select). The bridge fixture met on this part with the full monitor because
its `error_only` preset compiles fewer cones; at the wrapper's defaults the
CAM is the limit of the full monitor near 150 MHz. On the Artix-7 at 10 ns
the full read monitor misses by 1.45 ns and the lite meets by 0.6 ns.

**Clock gating.** `_cg` adds 20 to 80 LUTs and about 14 flops for the gating
controller and costs 0.15 to 0.45 ns of register-to-register slack (the
enable now sits on the clock enable of every register). Its purpose is
dynamic power in an idle design; the vectorless estimate cannot show that
(it assumes default toggle rates), so the power column reads a few
milliwatts higher for `_cg`, which is the controller's own activity, not a
measurement of savings. Measure clock gating on a board with real traffic
or not at all.

**Across protocols.** Per monitor, at defaults: AXI4/AXI5 lite about 1,100
LUTs; AXI-Lite lite about 930 to 1,030; AXIS lite about 1,550 (it is the
whole wrapper here, there is no plain `axis4_master` to subtract, and it
carries a skid of 4); APB4/APB5 monitors 570 to 600; Wishbone 620. The APB
and Wishbone monitors are older, table-based designs at 4 and 8 slots and
sit between the two AXI variants in cost per slot.

**Aggregation.** A four-client `monbus_arbiter` with skids is 1,800 LUTs and
2,000 flops (the flops are four 192-bit input skids and one output skid); a
group at its defaults (64-record error FIFO, 96-beat write FIFO) is 1,700 to
2,000 LUTs and about 1,200 flops, meeting 6.667 ns register to register with
1.2 to 1.4 ns to spare after the planner split of amba ISSUE-001.

**Power.** The estimates scale with LUT count as expected (full monitor 75
to 80 mW dynamic against the lite's 15 to 20 mW at default activity); treat
them only as a ratio between variants on the same part.

## Recommendations

1. **Default to the lite.** It is one sixth of the full monitor in LUTs, one
   fifth in flops, meets 150 MHz on the Kintex-7 with margin and 100 MHz on
   the Artix-7, and reports every event it cannot deliver. Reach for the
   full monitor only for a class it alone has (performance windows, debug
   trace, address filtering with the ID filter).
2. **If the full monitor is needed at 150 MHz, cut its slots.** The CAM is
   the critical path and scales with `MAX_TRANSACTIONS`; the bridge fixture
   met with fewer cones. Measure the chosen configuration with this sweep
   rather than the defaults.
3. **Budget the group once per subsystem, not per port.** Its 1,700 to 2,000
   LUTs are the fixed cost of the drain; three or thirty ports share it.
4. **Register configuration inputs next to the block.** Every out-of-context
   miss in the tables is a `cfg_*` pin driving arithmetic directly. In a real
   design those come from CSR flops; keep them adjacent (the group already
   re-registers its window config internally for this reason).
5. **Leave `_cg` off unless idle power is the goal**, and measure that on
   silicon. It buys nothing in area or timing.

## Open findings from this sweep

- `axis4_master_monlite` missed 10 ns on the Artix-7 register to register by
  1.18 ns in the first sweep (16 to 19 levels into `r_dropped`): the AXIS lite
  decided its events and counted drops in one cycle. Fixed the next day as
  monitor-lite ISSUE-003 with an event stage; the tables above carry the
  re-run: +1.65 ns on the Artix-7 and +1.87 ns on the Kintex-7 register to
  register, 6 logic levels, for 44 LUTs and 199 flops more.
- The full AXI4 monitors at 16 slots miss 6.667 ns on the Kintex-7 in the
  CAM; recorded above, no item filed: the lite is the recommended answer and
  the bridge's smaller preset meets.

## Files

`rtl/amba/fpga/tcl/monitor_synth.tcl` (the recipe), `bin/monitor_synth_sweep.sh`
(the matrix), `bin/summary_table.py` (these tables), `reports/<module>__<part>/`
(utilization, timing, power per run) and `reports/summary.csv` (one row per run).
