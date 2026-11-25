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

# peregrine_top (D-side wrapper)

**Module:** `peregrine_top.sv`

## Responsibility

`peregrine_top` instantiates the core at `CACHE_EN=1`, the I\$, amber, the CLINT, the uncached port and the arbiter, and contains the logic between the core's data port and those targets: the address decode, the valid/ready request, the core's hold, the response capture, amber's lane placement, the clean engine and the `fence.i` sequence. Its ports and parameters are in the HAS ("peregrine_top Port Specification"); the cycle rules are in "The D Side" and "fence.i".

## Instances

| Instance | Module | Arbiter port |
|----------|--------|--------------|
| `u_core` | `peregrine_core` (`CACHE_EN=1`) | - |
| `u_rst_sync` | `reset_sync` (the same synchronized reset the core uses) | - |
| `u_icache` | `peregrine_icache` | 0 |
| `u_dcache` | `amber_top` (`MAINT_EN=1`, `USE_MONITOR=0`, snoop port idle) | 1 |
| `u_uc` | `peregrine_uc_axi` | 2 |
| `u_clint` | `peregrine_clint` | - |
| `u_arb` | `peregrine_axi4_arb` (`NM=3`) | - |

: peregrine_top instances

## Wrapper State

| Register | Meaning |
|----------|---------|
| `r_outstanding` | An accepted access whose response is due; set on accept, cleared by its response |
| `r_tgt`, `r_lane` | The target (CLINT, uncached, D\$) and the amber lane of the access in flight, for the response mux |
| `r_mem_done` | MEM's access was accepted while the core was held; do not present it again |
| `r_mem_have`, `r_mem_data` | MEM's response, captured while the core was held; becomes WB's when MEM moves |
| `r_have`, `r_have_data` | WB's response, captured while the core was held; given to WB until it retires |
| `r_cl_wait` | A clean-all is in flight in amber |
| `r_fi_clean_done`, `r_fi_done` | `fence.i` progress: the clean is done; the invalidate is done |
| `r_ext_done` | The `dc_clean_req` clean is done |

: peregrine_top wrapper registers

## Key Combinational Terms

- `w_other_hold = I$ stall | fence.i busy | external clean busy`: holds that do not depend on a D-side ready.
- `w_dvalid = dmem_req_pre & ~r_mem_done & ~fence.i busy & ~clean busy & (~r_outstanding | response arriving)`: the request.
- `w_mem_wait = w_other_hold | (dmem_req_pre & ~r_mem_done & ~accepted) | (r_outstanding & ~response)`: the core's hold.
- `dmem_rdata = r_have ? r_have_data : the arriving response word`.

## amber Lane Placement

amber's beat is `BUS_WIDTH = AXI_DW` (64) bits and the CPU word is 32, so there is no width converter. A request carries its word in its lane: `be = wstrb << (4 x lane)` and `wdata` replicated across the lanes, with the lane taken from address bit 2. The response word is selected by `r_lane`, registered at the accept.

## Clean Engine

One clean-all (`{maint = 1, we = 0}` on amber's request) in flight at a time, issued only when nothing is outstanding and done on amber's response, which amber gives after the last WriteClean's B. Two sources ask for it: `fence.i`, and the `dc_clean_req` hook. A finishing clean satisfies every source pending at the time, since the core has been held since each one rose. A clean and a data access never coincide: the clean's sources hold the core, so `w_dvalid` is low while a clean is presented.

## D-side Observation

`dobs_valid` is the D-side handshake; `dobs_addr`, `dobs_wstrb` and `dobs_wdata` are the accepted access. The TB uses them to detect the `tohost` store and to count memory side effects against retired loads and stores.

---

**Last Updated:** 2026-11-25
