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

# Event Taps and Debug Taps

**RTL:** `onyx_ccu.sv:434-453` (ports), `1539-1586` (drive).

Both sets are outputs of `onyx_ccu` that nothing inside it reads. The event
taps feed `onyx_monlite` and `onyx_counters`; the debug taps keep the pair
fabric's names so jet-prime's pair-rig testbench reads onyx unchanged.

## Event taps

Every tap is a one-cycle pulse in the cycle of the handshake it reports,
with its payload valid in the same cycle.

| Tap | Width | Fires when | Payload |
|---|---|---|---|
| `evt_grant` | 1 | a grant (`w_grant`) | `evt_grant_cls[2:0]` the class; port, slot, address on `dbg_grant_dir`, `dbg_grant_slot`, `dbg_grant_addr` |
| `evt_ac` | `N_PORTS` | per peer, an AC handshake | - (the observer does not use it: `TXN_START` times the peer count) |
| `evt_gather` | `N_PORTS` | per answering peer, its CR completes a slot's gather (the last of the cycle's CRs for that slot) | `evt_gather_slot[p]`, `evt_gather_dt[p]`, `evt_gather_pd[p]` (the slot's verdict including this cycle's CRs) |
| `evt_read_wasted` | `N_PORTS` | per answering peer, a DataTransfer CR for a slot whose memory read is issued or presented | the slot is `evt_gather_slot[p]` |
| `evt_mem_ar` | 1 | a memory AR handshake | the slot is `mem_arid` |
| `evt_absorb` | 1 | an absorption's BRESP | `evt_absorb_slot` (`r_w_slot`) |
| `evt_wb` | 1 | a write AW handshake on the write port other than an absorption | `evt_wb_io` (the IO's), address `mem_awaddr` |
| `evt_lock_wait` | `N_REQ` | per requester, every cycle its valid candidate is held by the lock | `evt_lock_wait_addr[d]` the candidate's address |

: Table 3.4: Event taps

Two design points carry findings with them:

- **Per answering port, not one bit.** Two peers can each complete a
  different slot's gather in the same cycle; a single `evt_gather` bit
  merged them and lost an event that nothing counted (TASK-001 step 6b).
  Two peers completing the *same* slot report once (`w_cr_last`).
- **`evt_lock_wait_addr` is assigned per element** (`onyx_ccu.sv:1560-1565`):
  a whole-array alias made sv2v pack `w_cand_addr`, which the formal
  harness exposes per element.

## Debug taps

| Tap | Meaning |
|---|---|
| `dbg_busy` | some slot is valid (`|r_vld`) |
| `dbg_slot_vld[SLOTS-1:0]` | `r_vld` |
| `dbg_pend_vld[N_PORTS-1:0]` | each cache's pending queue is non-empty |
| `dbg_abs_pend` | some valid slot has PassDirty and no absorption BRESP yet |
| `dbg_grant`, `dbg_grant_dir`, `dbg_grant_addr`, `dbg_grant_slot` | the grant this cycle: requester (a cache port, or `N_PORTS` for the IO), the candidate's address, the slot allocated |

: Table 3.5: Debug taps

`dbg_grant_slot` is the free-slot index every cycle, meaningful when
`dbg_grant` is high.
