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

## Latency Components

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

> **Measured, not estimated.** `bridge_2x2_rw`, cpu master to ddr slave, idle
> bridge, prompt slave, counted at the ports:
>
> | Path | Cycles |
> |---|---|
> | master AW accepted -> AW accepted at the slave port | **4** |
> | B accepted at the slave port -> B accepted at the master | **2** |
>
> The response row previously read "Master delivery 0 (Direct connection)",
> giving a total of 1. It is registered, and the measured figure is 2. Both
> numbers come from `test_bridge_2x2_rw_latency`, which asserts each path is
> at least one cycle so a future edit cannot silently restore the zero. Figures
> elsewhere quoting "2-3 cycles" describe the request path and understate it;
> the measured value is 4 for this configuration.
>
> Other configurations differ -- width converters and the APB/AXIL shims add
> stages -- so treat these as the measured floor for a direct AXI4 path, not a
> universal constant.

## End-to-End Latency

### Write Transaction (Best Case)

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

### Read Transaction (Best Case)

```
Cycle 0: AR arrives at Bridge
Cycle 1: AR exits to Slave (skid buffer)
Cycle 2: Slave receives AR, generates R
Cycle 3: R routed back to Master

Total: 3 cycles (minimum)
```

### Contention Latency

When multiple masters contend for same slave:

```
Arbitration adds 1 cycle per contending master

Example: 4 masters requesting same slave
  Worst case: Wait for 3 other masters = 3 extra cycles
  Average case: Wait for 1.5 masters = 1-2 extra cycles
```

## Width Conversion Latency

### Upsize Latency

| Ratio | Extra Cycles | Notes |
|-------|--------------|-------|
| 1:1 | 0 | No conversion |
| 2:1 | 0 | Pack on fly |
| 4:1 | 0 | Pack on fly |
| 8:1 | 0-1 | May need accumulation |

: Table 5.8: Upsize Latency by Ratio

### Downsize Latency

| Ratio | Extra Cycles | Notes |
|-------|--------------|-------|
| 1:1 | 0 | No conversion |
| 1:2 | +1 | 2 output beats |
| 1:4 | +3 | 4 output beats |
| 1:8 | +7 | 8 output beats |

: Table 5.9: Downsize Latency by Ratio

## Protocol Conversion Latency

### AXI4 to APB

| Phase | Cycles |
|-------|--------|
| AXI4 AW decode | 1 |
| APB setup | 1 |
| APB access | 1+ (PREADY) |
| B generation | 1 |
| **Total** | **4+ cycles** |

: Table 5.10: AXI4 to APB Conversion Latency

### APB Wait States

APB slaves may insert wait states:

```
PREADY deasserted: +1 cycle per wait
Typical UART/GPIO: 0-2 wait states
Slow peripherals: May have many wait states
```

## Latency Optimization

### Design Recommendations

1. **Match data widths** - Avoid conversion latency
2. **Use AXI4 for fast paths** - Avoid APB latency
3. **Minimize contention** - Spread traffic across slaves
4. **Use bursts** - Amortize address latency
5. **Pipeline responses** - Don't block on slow slaves
