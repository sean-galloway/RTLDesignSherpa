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

# CPU GAXI Request/Response Timing

## Channel Structure

The CPU-side port is two house-GAXI streams:

| Signal | Direction | Width | Payload |
|---|---|---|---|
| `cpu_req_wr_valid` | in | 1 | request valid |
| `cpu_req_wr_ready` | out | 1 | request accepted |
| `cpu_req_wr_data` | in | `CPU_REQ_W` | packed {addr, we, be, wdata} |
| `cpu_rsp_rd_valid` | out | 1 | response valid |
| `cpu_rsp_rd_ready` | in | 1 | response accepted |
| `cpu_rsp_rd_data` | out | `CPU_RSP_W` | packed {rdata} |

: Table 3.1.1: CPU GAXI channels

## Request Timing

Because the cache is blocking, `cpu_req_wr_ready` is asserted only when `amber_control` is in `CTRL_IDLE` and no higher-priority snoop stall is active.

```
Cycle :  0   1   2   3   4   5
req_v :  1   0   0   0   0   0
req_r :  1   0   0   0   0   0   <- handshake at cycle 0
state :  L0  L1  HR  HR  RSP RSP
```

- Cycle 0: request accepted; `amber_cpu_frontend` latches it.
- Cycle 1: `CTRL_LOOKUP` drives tag-array port A.
- Cycle 2–3: hit service (`CTRL_HIT_RD` or `CTRL_HIT_WR`).
- Cycle 4–5: response valid until accepted.

On a miss, `cpu_req_wr_ready` stays low from cycle 1 through the entire miss sequence. The front end does not accept a new request until the replay completes.

## Response Timing

`cpu_rsp_rd_valid` is asserted when `amber_control` enters the response state. The data is held stable until `cpu_rsp_rd_ready` is high. Because the response is single-beat and the front end blocks, backpressure is expected to be rare, but the handshake is still honored.

## Write-Allocate Fills

A write miss triggers a fill, a merge of the CPU write data with the fill data, and then a replay of the write as a hit. The GAXI slave sees only the original single-beat write request and the eventual single-beat write response; the read-modify-write sequence is internal to `amber_control`.

---

**Last Updated:** 2026-10-06
