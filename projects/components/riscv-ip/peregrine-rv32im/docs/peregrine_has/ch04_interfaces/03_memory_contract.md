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

# Memory Contract

## The Cacheless Core (`CACHE_EN=0`)

The core keeps merlin's registered-read contract, one port for fetch and one for data, both answered without a handshake.

### Fetch

- In every cycle, `imem_rdata` must be the word at `imem_addr` (the PC).
- A memory may meet that combinationally, reading at `imem_addr`, or with a synchronous read addressed by `imem_addr_next` one cycle earlier.
- The PC changes only at an edge where `mem_wait` is low.

### Data

- A load or store is issued in MEM: `dmem_req` is high for one cycle (with `mem_wait` low) with `dmem_addr` (word address), `dmem_wstrb` and `dmem_wdata`.
- A store is written at that edge, byte by byte under `dmem_wstrb`; the data is already rotated onto its lanes.
- A load's word must be on `dmem_rdata` in the next cycle, when the load is in WB, and must stay there until the core retires it. A memory that registers its read data on `dmem_req` meets this: the register holds while no new request arrives, and none arrives while `mem_wait` holds the core.

### The Hold

`mem_wait` is the only flow control. While it is high, no state element in the core updates: the PC, every pipeline register, the register file, the CSRs, the predictor and the M unit all hold, no instruction retires, and `dmem_req` is low. A memory that needs more than one cycle raises `mem_wait` for as long as it needs.

## The Cached Build (`peregrine_top`)

Inside `peregrine_top` the same core contract is met by the I\$ and the D-side wrapper, so the core is unchanged:

- **Fetch** goes through the I\$. A hit answers with no hold. A miss holds the core (`mem_wait`) through the line refill and one replay cycle.
- **Data** is decoded by address to amber, the CLINT or the uncached port. The access is accepted in MEM with a valid/ready handshake. A D\$ hit's response arrives one cycle later, when the load is in WB, so a hit adds no stall. A miss, an uncached access, or a request that is not accepted at once holds the core until the response arrives.
- **One access is in flight.** amber is blocking and the uncached port holds one transaction, so the wrapper never presents a second access before the first one's response.
- **No request is withdrawn.** Once the wrapper presents an access it stays valid until accepted (the GAXI and AXI rule). The core helps: an instruction whose request was presented during a hold cannot be interrupted on the cycle the hold drops ("Trap and Interrupt Behavior").

The MAS chapter on the D side gives the cycle rules, including an access accepted while the core is held for an I\$ miss and a response captured while the core waits.

## Self-Modifying Code

Software that writes instructions must execute `fence.i` before running them, as the ISA requires. In the cached build `fence.i` writes every dirty amber line back to memory, invalidates the I\$, and refetches the instruction after it; without it, the I\$ and the pipeline may run stale instructions.

---

**Last Updated:** 2026-11-25
