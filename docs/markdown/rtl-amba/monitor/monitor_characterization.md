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
fixture (`projects/components/fabric-gen-ip/bridge/fpga`): Vivado 2025.1, one clock at the
stated period, 30 % input/output delays, reset false-pathed. Utilization is
post-route. Power is Vivado's vectorless estimate (`report_power`, confidence
"Medium"): it ranks variants against each other and says nothing absolute.

**Plane:** cross-plane (measured cost of protocol-plane monitors and the output-plane group)

## Current refresh: 2026-11-21 (rtl/amba/monitors TASK-007)

The expanded default sweep ran 48 modules on each part: 96 fresh routed rows,
no failed or skipped runs. The table selects the modules that guide the current
optimization work; `reports/summary.csv` carries every row. WNS here is
register-to-register, not the artificial primary-I/O budget. The older tables
below remain the September comparison history.

| Module | Kintex LUT / FF / WNS ns | Artix LUT / FF / WNS ns |
|---|---:|---:|
| `axi4_master_rd_mon` | 7,164 / 5,552 / +0.664 | 7,499 / 5,552 / **-0.629** |
| `axi4_master_rd_monlite` | 1,371 / 1,416 / +1.969 | 1,375 / 1,416 / +1.732 |
| `axi4_master_wr_mon` | 8,345 / 6,156 / **-1.124** | 8,360 / 6,156 / **-3.779** |
| `axi4_master_wr_monlite` | 1,602 / 1,554 / +1.957 | 1,601 / 1,554 / +2.030 |
| `axis4_master_monlite` | 1,164 / 630 / +1.489 | 1,164 / 630 / +1.112 |
| `chi_rnf_port_monlite` | 4,532 / 3,480 / +0.326 | 4,647 / 3,480 / **-0.365** |
| `chi_hnf_port_monlite` | 4,432 / 3,308 / +0.274 | 4,558 / 3,308 / **-0.606** |
| `axi4ace_snoop_monitor_lite` | 613 / 797 / +1.367 | 623 / 797 / **-0.425** |
| `monbus_arbiter` | 1,032 / 1,970 / +2.843 | 1,033 / 1,970 / +3.575 |
| `monbus_group_core` | 1,377 / 552 / **-2.130** | 1,381 / 552 / **-6.750** |
| `monbus_burst_writer` | 592 / 379 / +0.757 | 601 / 379 / +0.174 |
| `monbus_cam` | 3,199 / 4,422 / **-0.740** | 3,197 / 4,422 / **-2.616** |

The smaller monitors remain small on Artix: AXIS 1,164 LUT / +1.112 ns,
CXS master/slave +1.860/+1.109 ns, Wishbone +0.105 ns. APB4/APB5 are
520/545 LUT but now miss 100 MHz by 0.133/0.278 ns internally. CHI, ACE snoop,
the group writer, and the CAM are the measured timing candidates; the shared
arbiter needs no repeat of MC-004's skid rewrite. The pipelined standalone
writer meeting both targets while the inline group writer fails both is the
clearest available A/B reference.

The AXI4/AXI-Lite rows above are the pre-storage-pass baseline. The subsequent
reset-free payload conversion is tabulated in [axi_monitor_lite.md](axi_monitor_lite.md):
at Kintex/Artix respectively, AXI4 read becomes 1,211/1,213 LUT and 1,008 FF,
AXI4 write 1,314/1,318 and 1,058 FF, AXI-Lite read 904/905 and 799 FF, and
AXI-Lite write 974/976 and 791 FF. Every one meets its target.

The ACE snoop allocation-payload conversion reduces its Kintex/Artix rows to
583/588 LUT and 381 FF, from 613/623 LUT and 797 FF. Kintex WNS is +0.827 ns;
Artix improves from -0.425 to +0.118 ns. Its address, snoop-type, and timestamp
arrays all infer distributed RAM.

CHI combines reset-free allocation payload with one-hot event selection. RN-F
moves from 4,532/4,647 LUT and 3,480 FF to 4,338 LUT and 3,096 FF on both
parts; HN-F moves from 4,432/4,558 LUT and 3,308 FF to 4,214/4,218 LUT and
2,924 FF. Kintex WNS is +0.941/+0.984 ns. Artix RN-F closes at +0.065 ns;
HN-F remains -0.647 ns in response matching into the snoop counter, with the
former event/output-FIFO path removed.

AXIS, CXS, and Wishbone meet both targets and have no justified storage/cone
change. APB4/APB5 remain small (about 520–545 LUT on Artix) with residual
-0.133/-0.278 ns latency/event-selection-to-FIFO paths; splitting their mixed
command/state structs is deferred rather than presented as a fix.

The inline group writer now uses a two-stage epoch cap, a trigger-time FIFO
snapshot, and an in-flight room down-counter. Routed A/B:

| Top | Kintex LUT / FF / WNS | Artix LUT / FF / WNS |
|---|---:|---:|
| `monbus_group_core` | 1,386 / 619 / +1.354 ns | 1,389 / 619 / **-0.785 ns** |
| AXIL/AXIL group | 1,703 / 1,095 / +0.250 ns | 1,709 / 1,095 / **-0.038 ns** |
| AXI4/AXI4 group | 1,907 / 1,337 / +0.928 ns | 1,915 / 1,337 / +0.209 ns |
| AXIL/AXI4 group | 1,860 / 1,261 / +1.045 ns | 1,874 / 1,261 / **-0.095 ns** |
| AXI4/AXIL group | 1,753 / 1,171 / +1.421 ns | 1,760 / 1,171 / +0.119 ns |

The core's Artix baseline was 1,381 LUT / 552 FF / -6.750 ns. The residual
path is FIFO-count modulo-3 rounding into the first cap register. Exact burst
shape is preserved, including the directed 24-beat watermark case. The
`bridge_1x2_rd_lite_mon` system fixture meets at +0.659 ns Kintex and +0.034 ns
Artix, with zero unrouted nets and no group-writer worst path.

Production uses `monbus_cam_pipe`, not the unpipelined reference CAM. The pipe
meets at 2,154/2,168 LUT, 4,655 FF, +1.565/+0.857 ns on Kintex/Artix. Removing
payload resets increases it to 2,232/2,247 LUT with no FF saving, so that edit
was reverted; its clear/reuse equivalence check remains in the test suite.

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

## Full observer FPGA optimization campaign (2026-11-22)

The passive full observer variants and their unoptimized RTL baseline are in
`be7f8e891`; the approved experiment is
`docs/superpowers/specs/2026-11-22-full-monitor-fpga-observers-design.md`.
The full-feature rows enable all six reporter cones and four address ranges at
16 transactions in one bank. Deployment-shaped rows use 64 transactions in
four banks and the observer's existing cone defaults. Lite rows are included
for size context only; they are not feature-equivalent controls. Every row has
zero BRAM and zero unrouted nets. Setup failing endpoints include the OOC
primary-I/O paths; WNS and logic levels below are register-to-register.

| Profile / part | LUT | FF | LUTRAM | WNS (ns) | Levels | Setup failing endpoints |
|---|---:|---:|---:|---:|---:|---:|
| Full feature master, Kintex-7 | 21,658 | 16,876 | 444 | -1.046 | 14 | 4,628 |
| Full feature slave, Kintex-7 | 21,658 | 16,876 | 444 | -1.046 | 14 | 4,628 |
| Full feature master, Artix-7 | 21,976 | 16,866 | 444 | -3.868 | 14 | 10,497 |
| Full feature slave, Artix-7 | 21,976 | 16,866 | 444 | -3.868 | 14 | 10,497 |
| Full deployment, Kintex-7 | 33,571 | 10,313 | 288 | -14.841 | 56 | 9,222 |
| Full deployment, Artix-7 | 33,544 | 10,305 | 288 | -30.753 | 57 | 10,729 |
| Lite deployment, Kintex-7 | 13,647 | 11,228 | 804 | +0.188 | 14 | 0 |
| Lite deployment, Artix-7 | 14,002 | 11,237 | 804 | -1.654 | 15 | 3,171 |

At the full-feature Kintex baseline, the read tap is 7,225 LUT / 5,349 FF and
the write tap 8,595 LUT / 6,101 FF. Their CAMs are the largest logic blocks:
3,845 LUT / 1,920 FF read and 4,744 LUT / 2,208 FF write. The reporters cost
2,235 / 2,246 LUT each, including 1,802 / 1,818 FF in their local snapshots.
These measurements select CAM reset/allocation experiments first and the
reporter snapshot reset experiment second; no RAM attribute is applicable to
parallel-read CAM state.

The full-feature worst path is `r_widq_count` through the write transaction
manager into CAM `r_payload`: -1.046 ns on Kintex and -3.868 ns on Artix, 14
levels with over 80 percent routing delay. Deployment full is much worse:
valid-to-payload update cones at 56 / 57 levels and -14.841 / -30.753 ns. This
is an unoptimized baseline, not a claim that the full observer meets either
clock target. The Artix lite context also misses 10 ns at this large capacity;
its worst path is read-skid data into `r_beats`, not a full-monitor cone.

Reproduce the eight-row baseline (and later same-configuration comparisons)
with:

```bash
source env_python
RUN_LABEL=full_before JOBS=4 rtl/amba/fpga/bin/full_observer_synth_sweep.sh
```

`rtl/amba/fpga/results/full_observer_<label>/summary.csv` collects the rows;
the per-row report directories contain depth-8 hierarchy, route status, power,
and register-to-register timing. Raw results remain uncommitted measurement
artifacts. The candidate A/B row is `feature_master` on both parts.

### Experiment 1: CAM ID/payload reset removal -- rejected

Removing reset from parallel-read CAM `r_id` / `r_payload` while retaining
validity reset/clear passed all 7 CAM configurations, all 3 transaction-manager
cells, and both transaction-manager prove/cover runs. The new
`t19_sync_clear_reuse` checks exact old/new IDs and payloads and remains in the
suite; corrupting payload readback fails it.

| Part | Before LUT / FF / WNS | After LUT / FF / WNS | Delta |
|---|---:|---:|---|
| Kintex-7 | 21,658 / 16,876 / -1.046 ns | 22,037 / 16,873 / -0.888 ns | **+379 LUT, -3 FF, +0.158 ns** |
| Artix-7 | 21,976 / 16,866 / -3.868 ns | 22,433 / 16,873 / -4.421 ns | **+457 LUT, +7 FF, -0.553 ns** |

LUTRAM stayed at 444 and both rows had zero unrouted nets. The small Kintex
slack change is not a consistent timing win and does not justify hundreds of
extra LUTs. The RTL conversion was reverted; the clear/reuse test and this
negative measurement remain. Reproduce with
`RUN_LABEL=cam_reset_after JOBS=2 rtl/amba/fpga/bin/full_observer_synth_sweep.sh feature_master`.

### Experiment 2: reporter snapshot reset removal -- rejected

The reporter transaction snapshot moved to reset-free storage behind a guarded
first-post-reset view. It passed reporter prove/cover and all 84 observer cells,
including normal reset/reissue and a zero-clock async-reset case. The latter
establishes a terminal reporter event and checks `reporter.monbus_valid`
directly; disabling the guard replays a stale completion, while the guarded
implementation stays quiet and accepts new traffic.

| Part | Before LUT / FF / WNS | After LUT / FF / WNS | Delta |
|---|---:|---:|---|
| Kintex-7 | 21,658 / 16,876 / -1.046 ns | 21,693 / 16,877 / -0.990 ns | **+35 LUT, +1 FF, +0.056 ns** |
| Artix-7 | 21,976 / 16,866 / -3.868 ns | 22,020 / 16,875 / -4.063 ns | **+44 LUT, +9 FF, -0.195 ns** |

LUTRAM stayed at 444 and both rows had zero unrouted nets. The conversion
increases area on both parts and has no consistent timing benefit, so it was
reverted. The strengthened reset tests and negative result remain. Reproduce
with `RUN_LABEL=reporter_reset_after JOBS=2 rtl/amba/fpga/bin/full_observer_synth_sweep.sh feature_master`.

### Experiment 3: lowest-set CAM allocation -- rejected

Replacing the serial lowest-free scans with `x & (~x + 1)` in the CAM and its
transaction-manager mirror proved equivalent to the baseline golden CAM. The
harness compares all match, free, allocation, valid, ID, and payload outputs;
restricting the golden address pick to the highest slot fails the proof. The
rewritten candidate also passed all 7 CAM configurations, all 3
transaction-manager cells, and both transaction-manager prove/cover runs.

| Part | Before LUT / FF / WNS | After LUT / FF / WNS | Delta |
|---|---:|---:|---|
| Kintex-7 | 21,658 / 16,876 / -1.046 ns | 22,120 / 16,873 / -1.080 ns | **+462 LUT, -3 FF, -0.034 ns** |
| Artix-7 | 21,976 / 16,866 / -3.868 ns | 22,489 / 16,872 / -3.318 ns | **+513 LUT, +6 FF, +0.550 ns** |

LUTRAM stayed at 444 and both rows had zero unrouted nets. Kintex timing did
not improve; Artix gained slack but paid 513 LUTs. The worst endpoints remain
CAM payload registers, with the source moving from `r_widq_count` to age state,
so this is not a demonstrated allocator-path closure. The RTL was reverted.
Directed mask boundaries and the reusable equivalence harness in
`formal/amba/monitor_trans_cam/` remain. Reproduce with
`RUN_LABEL=cam_alloc_after JOBS=2 rtl/amba/fpga/bin/full_observer_synth_sweep.sh feature_master`.

### Final accepted result

The passive full observer variants, refusal accounting, and strengthened tests
are retained; none of the three optimization conversions is retained. The final
`full_after` matrix at source `2733f5516` exactly matches `full_before` in every
published metric. There is no cumulative LUT, FF, LUTRAM, BRAM, WNS, or logic-
level improvement to claim.

| Profile / part | Final LUT / FF / LUTRAM / WNS | Delta from baseline |
|---|---:|---|
| Full feature master, Kintex-7 | 21,658 / 16,876 / 444 / -1.046 ns | 0 |
| Full feature slave, Kintex-7 | 21,658 / 16,876 / 444 / -1.046 ns | 0 |
| Full feature master, Artix-7 | 21,976 / 16,866 / 444 / -3.868 ns | 0 |
| Full feature slave, Artix-7 | 21,976 / 16,866 / 444 / -3.868 ns | 0 |
| Full deployment, Kintex-7 | 33,571 / 10,313 / 288 / -14.841 ns | 0 |
| Full deployment, Artix-7 | 33,544 / 10,305 / 288 / -30.753 ns | 0 |
| Lite deployment, Kintex-7 | 13,647 / 11,228 / 804 / +0.188 ns | 0 |
| Lite deployment, Artix-7 | 14,002 / 11,237 / 804 / -1.654 ns | 0 |

All eight final rows have zero unrouted nets. Residual full-monitor misses are
the ones listed above, not closed timing. The full variants are justified only
when performance windows, debug, or other full-only behavior is required and
the integration accepts the measured cost. Further timing work needs a new
report-led candidate; these three negative experiments must not be represented
as an FPGA efficiency improvement. Reproduce the final rows with
`RUN_LABEL=full_after JOBS=4 rtl/amba/fpga/bin/full_observer_synth_sweep.sh`.

Final formal sign-off comprises 19 PASS results: clean prove/cover for the
transaction manager (unbanked and banked), base, filtered, reporter, and four
AXI4 full wrappers, plus the CAM equivalence proof. Directed mutation checks
are recorded in the individual experiments. The final clean FULL AMBA
regression passed **2999/2999** in 1457.85 s; clean FULL misc FUB passed
**282/282** in 497.24 s.

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
  rtl/amba/monitors ISSUE-003 with an event stage; the tables above carry the
  re-run: +1.65 ns on the Artix-7 and +1.87 ns on the Kintex-7 register to
  register, 6 logic levels, for 44 LUTs and 199 flops more.
- The full AXI4 monitors at 16 slots miss 6.667 ns on the Kintex-7 in the
  CAM; recorded above, no item filed: the lite is the recommended answer and
  the bridge's smaller preset meets.

## Files

`rtl/amba/fpga/tcl/monitor_synth.tcl` (the recipe), `bin/monitor_synth_sweep.sh`
(the matrix), `bin/summary_table.py` (these tables), `reports/<module>__<part>/`
(utilization, timing, power per run) and `reports/summary.csv` (one row per run).
The full observer campaign uses `rtl/amba/fpga/bin/full_observer_synth_sweep.sh`
and `rtl/amba/fpga/results/full_observer_<label>/`.

## References

The Ocelus is an original design of this repository. The papers and standards below are related work for comparison, not sources of the design; protocol specifications define the rules the monitor observes.

- Ciordas, C., Basten, T., Rădulescu, A., Goossens, K., van Meerbergen, J. "An Event-Based Monitoring Service for Networks on Chip." *ACM Trans. Design Automation of Electronic Systems*, 10(4):702-723, Oct. 2005. DOI: [10.1145/1109118.1109126](https://doi.org/10.1145/1109118.1109126). -- for comparison: probe area reported at 17-24% of NoC area.
- Goossens, K., Vermeulen, B., van Steeden, R., Bennebroek, M. "Transaction-Based Communication-Centric Debug." *Proc. 1st Int. Symp. Networks-on-Chip (NOCS 2007)*, pp. 95-106, May 2007. DOI: [10.1109/NOCS.2007.46](https://doi.org/10.1109/NOCS.2007.46). -- for comparison: monitors plus event interconnect at 4.5% of NoC area.
- Ciordas, C., Goossens, K., Basten, T., Rădulescu, A., Boon, A. "Transaction Monitoring in Networks on Chip: The On-Chip Run-Time Perspective." *Proc. IEEE Int. Symp. Industrial Embedded Systems (IES 2006)*, pp. 1-10, Oct. 2006. DOI: [10.1109/IES.2006.357464](https://doi.org/10.1109/IES.2006.357464). -- for comparison: transaction monitoring at about 5% of NoC area.
- Fiorin, L., Palermo, G., Silvano, C. "MPSoCs Run-Time Monitoring through Networks-on-Chip." *Proc. Design, Automation & Test in Europe (DATE 2009)*, pp. 558-561, Apr. 2009. DOI: [10.1109/DATE.2009.5090726](https://doi.org/10.1109/DATE.2009.5090726). -- for comparison: ASIC overhead and added traffic of a run-time monitoring system.
- Indexed in `rtl/amba/references/README.md` (Monitor subsystem family; citation only)
