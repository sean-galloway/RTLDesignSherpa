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
| `cpu_req_wr_data` | in | `CPU_REQ_W` | packed {[maint,] addr, we, be, wdata} |
| `cpu_rsp_rd_valid` | out | 1 | response valid |
| `cpu_rsp_rd_ready` | in | 1 | response accepted |
| `cpu_rsp_rd_data` | out | `CPU_RSP_W` | packed {rdata} |

: Table 3.1.1: CPU GAXI channels

## Request Timing

The cache blocks on a miss but pipelines hits (amber TASK-005, the 1-cycle
hit). `cpu_req_wr_ready` is high when `l1_control` is in `CTRL_IDLE`, or in
`CTRL_HIT_RD` with the response FIFO empty (back to back, at most
`HIT_RUN_MAX` = 8 in a row before one cycle with ready low, which is when a
waiting snoop is taken). Every ready term is a register.

```
Cycle :  0    1    2    3    4    5
req_v :  A    B    C    0    W    0
req_r :  1    1    1    1    1    0
state :  IDL  HRD  HRD  HRD  IDL  HWR
rsp_v :  0    A    B    C    0    W
```

- Cycle 0: request A accepted in `CTRL_IDLE`; the tag compare and the data
  read run on A's address in this cycle.
- Cycle 1: A's response is valid (`CTRL_HIT_RD`); B is accepted in the same
  cycle. Read hits stream one per cycle.
- Cycle 4–5: a write hit W is answered in cycle 5 (`CTRL_HIT_WR`), but ready
  is low there: W's merge lands at the end of cycle 5, so the next request
  is accepted in cycle 6. A write hit occupies the port for two cycles.

On a miss (or an S-line write, which upgrades), the accept cycle goes to
`CTRL_LOOKUP` and `cpu_req_wr_ready` stays low through the entire miss
sequence; the response comes from the replay's hit state.

## Response Timing

`cpu_rsp_rd_valid` is asserted in the hit state itself, the cycle after the
accept: `l1_cpu_frontend` (`RSP_BYPASS = 1`) presents `l1_control`'s
response directly while its depth-2 staging FIFO is empty, and writes it
into the FIFO only when `cpu_rsp_rd_ready` is low in that cycle. A held
response stays byte-stable in the FIFO until taken, responses keep request
order, and the FIFO cannot overflow (ready requires it empty while a
response is up, and at least one free entry otherwise).

With `BUS_ERR_EN = 1` (amber TASK-008) the response carries one more bit,
`cpu_rsp_rd_data[BUS_WIDTH]`: the request's fill was answered SLVERR /
DECERR, nothing was installed, and the data is not meaningful. It travels
with the data through the bypass and the FIFO. An error response comes one
cycle after the failed fill's commit cycle, without the replay; OKAY
responses keep every cycle they had.

## Clean-All Request (amber TASK-004)

With `MAINT_EN = 1` on `amber_top` / `amber_ace_top` (default 0, the
classic packing above), the request carries one more bit above `addr`:

```
CPU_REQ_W = 1 + ADDR_WIDTH + 1 + BUS_WIDTH/8 + BUS_WIDTH
cpu_req_wr_data = {maint, addr, we, be, wdata}
```

| `maint` | `we` | Request |
|---|---|---|
| 0 | 0 / 1 | Ordinary read / write, as above. |
| 1 | 0 | **Clean-all**: write back every Modified line (WriteClean), leave each valid and clean (E). `addr`, `be` are ignored; drive `wdata` = 0. |
| 1 | 1 | Reserved (handled as a clean-all today; do not rely on it). |

: Table 3.1.2: request op encoding

The clean-all is one GAXI transaction: one accept, one response. The
response (`rdata` = the request's `wdata`, so 0) is valid only after the
last write-back's B response, so when the CPU sees it, memory holds every
line that was dirty. Ready stays low for the whole walk. Snoops are served
during it (at each set the walk scans, and while each write-back is in
flight). Latency is about one cycle per set plus, per dirty line, the
`FILL_BEATS`-cycle gather and the write-back's round trip.

peregrine uses it for `fence.i` (PRD P10): clean the D$, then invalidate
its own I$ and refetch. A clean-all does not invalidate anything.

## Write-Allocate Fills

A write miss triggers a fill, a merge of the CPU write data with the fill data, and then a replay of the write as a hit. The GAXI slave sees only the original single-beat write request and the eventual single-beat write response; the read-modify-write sequence is internal to `l1_control`.

---

**Last Updated:** 2026-11-24
