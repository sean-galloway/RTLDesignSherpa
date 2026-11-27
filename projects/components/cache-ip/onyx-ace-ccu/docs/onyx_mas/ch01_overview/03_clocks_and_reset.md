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

# Clocks and Reset

onyx is a single-clock IP. `onyx_ccu`, `onyx_monlite` (including its
`gaxi_fifo_sync` output queue) and `onyx_counters` all run on `clk`; no CDC
path exists inside `onyx_top`. A rig whose caches or memory run elsewhere
crosses outside onyx.

## Reset rules

- `rst_n` is active-low and asynchronous at the flops. onyx does not
  synchronize it; the rig is responsible for a synchronous release. Handbook:
  `vault/handbook/design/reset-and-clocking.md`.
- All **control** state uses the `ALWAYS_FF_RST` macro (`reset_defs.svh`):
  the table's valid and completion bits, the peer counters, the requester
  of each slot (`r_dir`), the queue counts, the hold registers, the replay
  engines, the write port's state and selection, the IO port's busy bits,
  the order flags `r_aw_pres` / `r_aw_yield` / `r_aw_old` and the line of
  the burst in flight `r_wfly_line` (`onyx_ccu.sv:1251-1307`, `1055-1063`,
  `1122-1128`, `1172-1180`).
- **Payload carries no reset.** The slot's `r_line`, `r_type`, `r_arid`,
  `r_arcache`, `r_arprot`, `r_aruser`; the pending queues' address and
  class (`r_pend_addr`, `r_pend_type`); the snoop queues' slot indices
  (`r_snq`, `r_sni`); and the snoop-data buffers (`g_buf[*].mem`, an
  `always_ff` with no reset branch, `onyx_ccu.sv:937-949`). Each is read
  only under a reset-qualified valid bit or count (`r_vld`, `r_pend_cnt`,
  `r_snq_cnt`, `r_sni_cnt`), so an unreset word is never observable, and the
  buffers stay inferable as distributed RAM (GLOBAL_REQUIREMENTS 1.4,
  handbook `design/sram-and-memories.md`).
- In `onyx_counters` the per-slot line mirror `r_sl_line` carries no reset
  (it is read only under `r_sl_gath`); every counter and flag resets to
  zero. In `onyx_monlite` the holders, the grant-cycle store, the watch bits
  and the drop count reset.
- After reset the table is empty, every queue is empty, the grant and
  write-port round-robin pointers point at requester 0, and the write port
  is idle.

## Quiescence

`dbg_busy = |r_vld` (`onyx_ccu.sv:1576`): some slot is valid. It is **not**
the whole completion contract. A cache write-back or an IO WriteNoSnoop
holds no slot, so the write port can be mid-burst with `dbg_busy` low, and
the pending queues (`dbg_pend_vld`) and the absorption (`dbg_abs_pend`, a
subset of `dbg_busy`) are separate taps. A testbench declaring onyx idle
reads `dbg_busy`, `dbg_pend_vld` and the memory write channel together; the
pair rig learned this when it sampled quiescence while a correct drain was
still running (TASK-001, 2026-11-26).
