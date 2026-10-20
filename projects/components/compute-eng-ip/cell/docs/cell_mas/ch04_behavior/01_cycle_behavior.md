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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Cycle Behavior: Fill Path as Built

## Slice-1 Fill Path

The slice-1 RTL already implements the receive and store side of the
cell. This section documents its cycle behavior so that the slice-2/3
work can be checked against it.

### Head-Beat Reception

A packet arrives on the node's local port as a sequence of AXI4-Stream
beats. On the head beat:

- `s_user[11:0]` carries the destination `{X, Y, Z}`.
- `s_user[13:12]` carries the QoS class; it must be `2'b01` (non-zero)
  so the node does not consume the packet as its own config traffic.
- `s_user[29:15]` carries the source coordinate `{ext, level, X, Y, Z}`.
- `s_user[32:30]` carries `ptype`: `cfg=0`, `mem=2`, `credit=3`, …
- `s_user[33]` carries `op` (write/read or credit add/set).
- `s_user[49:34]` carries a compacted 16-bit length.
- `s_user[59:50]` carries a compacted 10-bit target address.
- `s_user[63:60]` carries the 4-bit tag.

This 64-bit TUSER packing is provisional and exists only because the
instantiated delta node exposes a 64-bit `TUSER`. It is superseded in
slice 2/3 by the `TILE_SPEC` §11.6 two-header model.

### Coordinate Match

`cell_rx` compares the destination `{X, Y, Z}` against its own
`POS_X/Y/Z`. The `ext` bit and QoS are not part of the match; QoS is
already required to be non-zero so the node did not consume the packet.

### Demux Decision

| `ptype` | `op` | Action |
|---|---|---|
| `mem` | 0 (write) | Accept payload beats into `cell_mem_in` starting at `target_addr`; increment `mem_wr_ptr` per beat |
| `cfg` | 0 (write) | Drive `cfg_wr_valid` to `cell_cfg_regs` with `target_addr[7:0]` and `s_data[31:0]` |
| `cfg` | 1 (read) | Counted TODO drop in slice 1; slice 2 builds a reply packet |
| `credit` | any | Counted TODO drop in slice 1; slice 2 routes to `cell_credit` |
| other | any | Drop head; increment `o_err_drop_cnt` via `inc_err_drop` |

: Table 4.1: Slice-1 head-beat dispatch

### Payload Write Timing

For a `mem` write packet:

- Cycle 0: head beat accepted; `in_pkt` latches `pkt_src_coord`,
  `pkt_ptype`, `pkt_target`; `mem_wr_ptr` clears.
- Cycle N: each payload beat with `s_valid && s_ready && mem_wr_ready`
  writes `mem_data[addr]` and `mem_tag[addr]` and increments
  `mem_wr_ptr`, where `addr = pkt_target + mem_wr_ptr`.
- The last payload beat (`s_last`) clears `in_pkt`.

`cell_mem_in` exposes `wr_ready = !o_full`; `cell_rx` backpressures the
local port while a `mem` payload is in flight and the memory is full.

### Occupancy Accounting

`cell_mem_in` increments its occupancy counter on every accepted write
and decrements it on every accepted read. The read side is held idle in
slice 1 (`mem_in_rd_valid = 1'b0` in `cell_top`), so occupancy only
rises during fill tests.

## Expected Slice-2/3 Cycle Behavior

Slice 2/3 keeps the same fill timing but changes the header transport:

- The head beat's `TUSER` carries only the delta route header.
- The 128-bit tile header is **payload**, beat-chained per the owner
  ruling 2026-10-18: on the 64-bit local port, beat 0 carries
  `tdata = header[63:0]` and beat 1 carries `tdata = header[127:64]`;
  payload beats follow. The demux reassembles the header across the two
  beats before dispatching on `ptype`.
- Payload beats carry one 32-bit line per 64-bit flit today; slice 3
  packs two lines per 64-bit flit.

The demux still records the source coordinate from the tile header's
source field (not delta's hop-source route header) and tags each
input-memory line with it.

---

**Last Updated:** 2026-10-18
