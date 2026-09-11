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

# Latency Analysis

## Overview

Where the cycles go on the way through the bridge: address path, data path, response path, then the end-to-end best cases and the conversion costs. The headline numbers for a direct AXI4 path are measured, not estimated — the note after Table 5.7 explains how, and why an earlier version of that table was wrong.

## Timing

### Address Path Latency

| Stage | Cycles | Notes |
|-------|--------|-------|
| Master Adapter (skid) | 1 | Pipeline registration |
| Address Decode | 0 | Combinational |
| Arbitration | 0-1 | 0 if no contention, 1 if arbitrate |
| Slave Router | 1 | Pipeline registration |
| **Total Address** | **2-3** | Best/worst case |

: Table 5.5: Address Path Latency

### Data Path Latency

| Stage | Cycles | Notes |
|-------|--------|-------|
| W follows AW | 0 | Same grant |
| Width conversion | 0-1 | 0 if match, 1 if convert |
| Protocol conversion | 0-2+ | 0 for AXI4, 2+ for APB |
| **Total Data** | **0-3+** | Best/worst case |

: Table 5.6: Data Path Latency

### Response Path Latency

| Stage | Cycles | Notes |
|-------|--------|-------|
| Slave response | Variable | Slave-dependent |
| ID extraction | 0 | Combinational -- routing is by FIFO position, no lookup |
| Response routing + master delivery | 2 | Registered; NOT a direct connection |
| **Total Response** | **2 + slave** | Plus slave latency |

: Table 5.7: Response Path Latency

> **Measured.** `bridge_2x2_rw`, cpu master to ddr slave, idle bridge:
>
> | Path | Cycles |
> |---|---|
> | AW accepted at the master -> AWVALID at the slave port | **2** |
> | B accepted at the slave port -> BVALID at the master | **2** |
>
> Two skid stages each way: the master adapter's `axi4_slave_wr` AW skid, then
> the slave adapter's `axi4_master_wr` AW skid. The response path has the same
> structure, which is why the two figures match.
>
> The response row previously read "Master delivery 0 (Direct connection)",
> total 1. It is registered, and the figure is 2.
>
> **What this measures, and what an earlier revision of this note got wrong.**
> These are PROPAGATION times -- how long a beat takes to appear on the far
> side. An earlier revision quoted 4 cycles for the request path, measured
> accept-to-accept. That metric also counts however long the far side held
> READY low, so it describes the attached slave's timing as much as the
> bridge's, and it was not even stable: successive runs gave 4/2 and then 2/6.
> Propagation is 2/2 on every run.
>
> `test_bridge_2x2_rw_latency` asserts both values EXACTLY, so adding or
> removing a pipeline stage fails the test rather than silently ageing this
> table.
>
> Other configurations differ -- width converters and the APB/AXIL shims add
> stages -- so this is the figure for a direct AXI4 path, not a universal
> constant.

### Loaded Write Latency (measured)

`test_bridge_2x2_rw_perf` streams 16-beat write bursts from one master and
pairs the k-th AW accepted at the master port with the k-th BVALID there:

| Queue | AW accepted -> BVALID (cycles) |
|---|---|
| First burst, fabric empty | **23** = 16 W beats + the 2 + 2 skid stages + the slave's turnaround |
| k bursts queued ahead | about 16 k + 7; maximum 323 at a 20-deep queue |

: Table 5.7a: Write latency under load, `bridge_2x2_rw`, 32-bit direct path

The queue exists because the bridge accepts AWs ahead of their W data --
the master adapter's AW skid, the slave adapter's 16-entry response-tracking
FIFO and its AW skid together hold about 20 bursts -- so a requester that
issues many AWs before its data sees its B responses spaced by the data
time, not by the fabric. Read latency does not queue the same way: the R
stream is one beat per cycle end to end (Table 5.1a).

### End-to-End Latency

#### Write Transaction (Best Case)

```
Cycle 0: AW arrives at Bridge
Cycle 1: AW exits to Slave (skid buffer)
Cycle 2: Slave receives AW
Cycle 1: W arrives (same cycle as AW skid)
Cycle 2: W exits to Slave
Cycle 3: Slave receives W, generates B
Cycle 4: B routed back to Master

Total: 4 cycles (minimum)
```

#### Read Transaction (Best Case)

```
Cycle 0: AR arrives at Bridge
Cycle 1: AR exits to Slave (skid buffer)
Cycle 2: Slave receives AR, generates R
Cycle 3: R routed back to Master

Total: 3 cycles (minimum)
```

#### Contention Latency

When multiple masters contend for same slave:

```
Arbitration adds 1 cycle per contending master

Example: 4 masters requesting same slave
  Worst case: Wait for 3 other masters = 3 extra cycles
  Average case: Wait for 1.5 masters = 1-2 extra cycles
```

### Width Conversion Latency

#### Upsize Latency

| Ratio | Extra Cycles | Notes |
|-------|--------------|-------|
| 1:1 | 0 | No conversion |
| 2:1 | 0 | Pack on fly |
| 4:1 | 0 | Pack on fly |
| 8:1 | 0-1 | May need accumulation |

: Table 5.8: Upsize Latency by Ratio

#### Downsize Latency

| Ratio | Extra Cycles | Notes |
|-------|--------------|-------|
| 1:1 | 0 | No conversion |
| 1:2 | +1 | 2 output beats |
| 1:4 | +3 | 4 output beats |
| 1:8 | +7 | 8 output beats |

: Table 5.9: Downsize Latency by Ratio

### Protocol Conversion Latency

| Phase | Cycles |
|-------|--------|
| AXI4 AW decode | 1 |
| APB setup | 1 |
| APB access | 1+ (PREADY) |
| B generation | 1 |
| **Total** | **4+ cycles** |

: Table 5.10: AXI4 to APB Conversion Latency

#### APB Wait States

APB slaves may insert wait states:

```
PREADY deasserted: +1 cycle per wait
Typical UART/GPIO: 0-2 wait states
Slow peripherals: May have many wait states
```

## Design Notes

### Design Recommendations

1. **Match data widths** - Avoid conversion latency
2. **Use AXI4 for fast paths** - Avoid APB latency
3. **Minimize contention** - Spread traffic across slaves
4. **Use bursts** - Amortize address latency
5. **Pipeline responses** - Don't block on slow slaves
