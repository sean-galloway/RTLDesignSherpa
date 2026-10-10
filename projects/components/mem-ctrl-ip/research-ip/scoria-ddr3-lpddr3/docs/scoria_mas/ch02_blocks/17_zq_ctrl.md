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

# ZQ Controller (`scoria_zq_ctrl`)

**Module:** `scoria_zq_ctrl.sv`
**Location:** `rtl/fub/`
**Category:** maintenance / ZQ calibration
**Parent:** `scoria_scheduler_layer`
**Status:** complete and sim-verified; DDR3-only at the current design point because the scheduler gates `w_zq_run` on `memtype_i == MEMTYPE_DDR3`

---

## Purpose

`scoria_zq_ctrl` issues periodic ZQ short-calibration commands (`ZQCS`) as maintenance traffic. It is new in scoria: pumice's DDR2/LPDDR2 target has no ZQ calibration, and LiteDRAM's working DDR3 core implements its ZQCS executor inside the refresh path. scoria splits it out so the arbiter sees one maintenance request/grant channel per source, with a source tag rather than a special case.

The block is intentionally small. Its job is to wait the programmed interval, ask for the bus, hold the post-grant `tZQCS` window, and start the next interval. It does not block traffic during `tZQCS`; that obligation lives in the arbiter.

## Parameters

`scoria_zq_ctrl` has no parameters; all configuration is runtime CSR.

: Table 2.17.1: ZQ controller parameters (none — all ports)

## Interface

### Configuration and timing

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mc_clk` | in | 1 | controller clock |
| `mc_rst_n` | in | 1 | active-low reset |
| `enable_i` | in | 1 | ZQCS enable; also gated on `init_done` upstream |
| `t_zqcs_interval_i` | in | 32 | cycles between calibrations; 0 disables |
| `t_zqcs_i` | in | 16 | post-grant `tZQCS` hold count |

### Mode C placement policy

| Signal | Direction | Width | Description |
|---|---|---|---|
| `placement_i` | in | 2 | 0 = request on expiry, 1 = defer under demand, 2 = reserved |
| `overdue_max_i` | in | 13 | maximum deferral cycles; 0 = no cap |
| `demand_i` | in | 1 | scheduler has read/write work waiting |

### Arbiter handshake and telemetry

| Signal | Direction | Width | Description |
|---|---|---|---|
| `zq_req_o` | out | 1 | request to the scheduler; held until granted |
| `zq_grant_i` | in | 1 | scheduler grant pulse |
| `obs_busy_o` | out | 1 | high in the post-grant `tZQCS` window |
| `obs_zqcs_total_o` | out | 16 | total ZQCS commands issued since reset |
| `obs_interval_cnt_o` | out | 32 | live interval countdown |
| `obs_overdue_o` | out | 1 | interval expired and still no grant, or intentionally deferred |

: Table 2.17.2: ZQ controller ports

## Microarchitecture internals

### Interval counter

`r_interval` is a 32-bit down-counter loaded from `t_zqcs_interval_i`. A 32-bit width is required: a ~128 ms interval at 75 MHz is ~9.6M cycles, which does not fit the 16-bit counter `tREFI` uses. If `t_zqcs_interval_i == 0`, the block treats the interval as disabled rather than as "as fast as possible".

At reset the counter is seeded from the input rather than zeroed. A zero reset would make the first interval zero-length and issue a calibration immediately out of reset, along with a spurious `obs_overdue_o` if demand is already up. The upstream `enable_i` is normally low out of reset and additionally gated on `init_done`, but the seed removes a latent coupling on those reset values.

### The four FSM states

`scoria_zq_ctrl` has a real FSM, unlike `refresh_ctrl`, because its behavior is genuinely sequential: it must wait, then ask, then hold, and it needs a separate deferred-wait state for the placement policy.

```text
ZQ_IDLE  — counting down to the next calibration
ZQ_REQ   — requesting the arbiter, waiting for grant
ZQ_HOLD  — granted; holding tZQCS before reloading the interval
ZQ_DEFER — Mode C: interval expired but demand is high, deferring
```

### Placement policy

`placement_i == 0` requests on expiry; this is bit-identical to the v1 behavior. `placement_i == 1` enters `ZQ_DEFER` if `demand_i` is high when the interval expires. `placement_i == 2` is reserved and should not be used.

`ZQ_DEFER` exits to `ZQ_REQ` when any of these occurs:

- `demand_i` goes low,
- `placement_i` is changed away from 1,
- `overdue_max_i != 0` and `r_defer_cnt >= overdue_max_i`.

`obs_overdue_o` is high while deferred, and also while in `ZQ_REQ` with demand still present. The telemetry exists to make starvation visible: a request that withdrew itself under load would starve silently.

### Post-grant hold semantics

On `zq_grant_i`, the FSM moves to `ZQ_HOLD` and loads `r_hold` with `t_zqcs_i`. When `r_hold` reaches zero, the FSM returns to `ZQ_IDLE` and reloads `r_interval` from `t_zqcs_interval_i`. The hold simply delays the next interval reload; it does not itself block traffic. The arbiter enforces the actual `tZQCS` command-spacing window through its `w_zq_busy` term and final safety gate, which is where BUG-002 was fixed.

## FSM policy

The FSM is the right tool here because ZQCS has a non-arithmetic lifecycle: count, request, hold, repeat. The `ZQ_DEFER` state adds a conditional wait that cannot be expressed as a counter threshold alone. The state register is 2 bits; the combinational outputs are derived directly from it.

## Timing

One grant per calibration. The interval reload happens at the end of `ZQ_HOLD`, so the effective spacing between calibrations is `t_zqcs_interval_i + t_zqcs_i` cycles measured from grant to the start of the next request. `t_zqcs_interval_i` is counted in controller-clock cycles; the CSR value is derived from the JEDEC specification and the desired calibration frequency.

## Notes

- **ZQCS never preempts:** The block raises `zq_req_o` and waits. This matches LiteDRAM's behavior and is consistent with the family doctrine that maintenance is request-and-wait traffic.
- **DDR3-only today:** `scoria_scheduler_layer` computes `w_zq_run = zq_enable_i && init_done && (memtype_i == MEMTYPE_DDR3)`. For LPDDR3, ZQ calibration is handled differently and this block is not exercised.
- **Traffic blocking is the arbiter's job:** Do not rely on `ZQ_HOLD` to space commands. The arbiter's `w_zq_busy` term and final safety gate prevent any new command from issuing inside the `tZQCS` window; that is where BUG-002 was caught and fixed.
- **Placement policy trap:** `placement_i == 2` is reserved. If programmed, the block falls out of the defined policy and behavior is unspecified. Firmware should keep it at 0 or 1.
- **Overdue semantics trap:** `obs_overdue_o` is set intentionally in `ZQ_DEFER` and incidentally in `ZQ_REQ` while demand is present. A high value is not by itself an error; it is a starvation indicator that should be bounded by `overdue_max_i`.
