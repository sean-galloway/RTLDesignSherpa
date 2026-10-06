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

# Fabric AXI4 Master Timing

The `amber` pair-rig top uses the house `axi4_master_rd` and `axi4_master_wr` wrappers for plain AXI4 memory access. This chapter documents the cycle-level handoff between `amber_fill` / `amber_drain` and those wrappers.

## Read (Fill) Timing

`amber_fill` drives the `fub_axi_*` side of `axi4_master_rd`:

```
Cycle :  0   1   2   3   4   5   6
AR_v  :  1   0   0   0   0   0   0
AR_r  :  1   0   0   0   0   0   0   <- AR handshake
R_v   :  0   0   0   1   1   1   0
R_r   :  0   0   0   1   1   1   0   <- R beats accepted
last  :  0   0   0   0   0   1   0
```

- `ARLEN = FILL_BEATS - 1`, `ARSIZE = log2(BUS_WIDTH/8)`, `ARBURST = INCR`.
- `RREADY` is asserted as long as `amber_data_array` port A can accept the beat.
- Each accepted R beat is written to `amber_data_array` and the pending-fill bypass register is updated.
- `fill_done` pulses one cycle after `RLAST` is accepted.

## Write (Drain) Timing

`amber_drain` drives the `fub_axi_*` side of `axi4_master_wr`:

```
Cycle :  0   1   2   3   4   5   6
AW_v  :  1   0   0   0   0   0   0
AW_r  :  1   0   0   0   0   0   0   <- AW handshake
W_v   :  0   1   1   1   0   0   0
W_r   :  0   1   1   1   0   0   0   <- W beats accepted
last  :  0   0   0   1   0   0   0
B_v   :  0   0   0   0   0   1   0
B_r   :  0   0   0   0   0   1   0   <- B handshake
```

- `AWLEN = FILL_BEATS - 1`, `AWSIZE = log2(BUS_WIDTH/8)`, `AWBURST = INCR`.
- `WSTRB` is all-1s for every beat.
- `drain_done` pulses one cycle after the B handshake.

## Single Outstanding

There is at most one AR transaction and one AW transaction in flight at any time because the blocking pipeline does not launch a new miss until the previous one completes. No reorder buffer is needed inside `amber_fill` or `amber_drain`.

---

**Last Updated:** 2026-10-06
