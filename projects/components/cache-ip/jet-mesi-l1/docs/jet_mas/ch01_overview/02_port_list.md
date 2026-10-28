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

# Top-Level Port List

**Status:** planned contract — no RTL yet. The external pin contract is
inherited from amber (HAS ch04); jet adds nothing and removes nothing at
the boundary. Widths follow `l1_pkg` geometry parameters.

## `jet_top` (pair rig)

| Group | Signals | Dir | Notes |
|---|---|---|---|
| Clock/reset | `clk`, `reset_n` (`aresetn` at the AMBA edge) | in | single clock; see ch01/03 |
| CPU request (GAXI) | `req_valid`, `req_ready`, `req_addr`, `req_we`, `req_be`, `req_wdata` | in | single-beat request; accept stalls when lookup resources block (ch03/01) |
| CPU response (GAXI) | `rsp_valid`, `rsp_ready`, `rsp_data` | out | issue-order release via `jet_rsp_seq` (J4) |
| Fabric read (AXI4) | `m_axi_ar*` , `m_axi_r*` | out/in | single ID; fills issue in alloc order, R returns in order |
| Fabric write (AXI4) | `m_axi_aw*`, `m_axi_w*`, `m_axi_b*` | out/in | drains from the WB buffer, oldest-first |
| Snoop (ACE-shaped) | `snoop_req`/`snoop_addr`/`snoop_type` (AC), `snoop_ready`/`crresp` (CR), `cd*` (CD) | in/out | onyx D7 contract; CD before CR |
| Observation | `monbus_*` (128-bit packet + timestamp sideband) | out | merged core/transport observers |
| Status | `busy` | out | ctrl non-idle OR MSHR non-empty OR WB non-empty OR adapter skid occupancy |

## `jet_ace_top` (onyx rig)

Same skeleton; the fabric masters speak ACE (`axi4ace_master_*`): AR carries
`ARSNOOP` (`ReadNotSharedDirty` / `ReadUnique` / `CleanUnique` per amber's
issue-#106 mapping), AW carries `AWSNOOP` (`WriteBack` / `Evict`). The
snoop port is the onyx D7 AC/CD/CR contract. RACK/WACK are omitted (family
ruling 2026-10-11).

## What is deliberately NOT here

- **No response ID tags.** The J4 ruling re-sequences internally instead.
- **No cache-enable / flush pins.** Software-visible cache maintenance is a
  future hook (HAS ch06/04); snoops always see the arrays.
- **No second AXI4 read ID.** Parallel fills are a measured future step
  (design spec §2).
