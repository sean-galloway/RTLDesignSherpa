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

# rapids_seq_g and the Scheduler Firmware

**Module:** `rapids_seq_g.sv`; firmware `rtl/fw_g/sched_g.S`
**Location:** `projects/components/dma-ip/rapids/rtl/macro_g/`
**Status:** Implemented (rapids TASK-034)
**Last Updated:** 2026-10-22

---

## rapids_seq_g

One `gatling_core`, used unchanged through its own filelist, with the three memories it needs, each answering in one stage as gatling requires:

| Block | What | Size |
|---|---|---|
| Instruction ROM | the firmware image, from `sched_g_fw.svh`; one read port serves every hart (the barrel fetches for one context per cycle) | `IMEM_WORDS` = 1024 |
| Scratch | per-hart memory, indexed `{context, word}`; the run-base generator state of each slot | `SCRATCH_WORDS` = 128 per hart |
| Window decoder | routes a data access to the slot's `scheduler_g` by context and slot | -- |

: Table 5.3.1: rapids_seq_g

Parameters: `NUM_CHANNELS` (4 or 8), `NUM_HARTS` (4 or 8, dividing `NUM_CHANNELS`; default `NUM_CHANNELS`, one hart and one slot per channel; hart h serves channels h + `NUM_HARTS` x s), `IMEM_WORDS`, `SCRATCH_WORDS` (a power of 2, at least 64 per slot; a smaller scratch would alias slot 1 onto slot 0, and elaboration refuses it).

### Data Memory Map

| Address | Region |
|---|---|
| 0x0000_0000 | instruction ROM (fetch only; a data read returns 0) |
| 0x1000_0000 | slot 0 window (Section 5.2), word-indexed |
| 0x1000_0100 | slot 1 window |
| 0x1000_1000 | SUMMARY: `[1:0]` `seq_attn` of this hart's slots |
| 0x1000_1004 | SLOTS: slots per hart (1 or 2) |
| 0x1000_3000 | register mailbox (below), aliased by context |
| 0x2000_0000 | scratch, aliased by context |

: Table 5.3.2: Data memory map

Contexts stay implicit (gatling PRD 7): every hart runs the same image, and "slot 0" is a different channel for each, chosen by the context the access comes from. Reads are registered (address in X, data in W); window writes are registered into `scheduler_g` one cycle after X, so a hart's next instruction, `NUM_HARTS` (at least four) cycles later, always sees the effect of its own write. Each hart issues one instruction every `NUM_HARTS` clocks: at the default 8 harts an instruction costs a hart 8 clocks, which is the unit of every firmware cost in Section 5.5.

### Register Mailbox

Each hart can read and write its own half's PeakRDL registers -- the same `rapids_regs` the host programs -- through a mailbox: REG_ADDR (+0x00, byte offset within the half), REG_WDATA (+0x04), REG_CTRL (+0x08: `[0]` go, `[1]` write), REG_STATUS (+0x0C: `[0]` busy, `[1]` done, `[2]` error), REG_RDATA (+0x10). The firmware posts an access and polls; a single-stage barrel cannot wait on a bus. The harts' accesses go out one at a time (`arbiter_round_robin_simple_ack`) on the gatling's one master port, `seq_reg_*`, which the generated tree carries up to the top base. There `rapids_g_reg_arb` decides who pushes into the register block's command queue: the host's APB, the SOURCE gatling and the SINK gatling, round robin, one access outstanding, the response steered back by the held grant. Each gatling's offset is pinned to its half (SRC at 0x0000, SNK at 0x1000), so neither can reach the other's registers. The per-channel `CH_SCRATCH[n].SCRATCH` bits (0x300 in each half) are there for the host and the gatling to share flags or semaphores (not atomic across masters: give each bit one writer). The scheduler firmware does not use the mailbox today.

### Faults

`seq_fault[c]` is the halted bit of the hart serving channel c, so a firmware trap is a fatal fault for that hart's channels: they enter CH_ERROR and send the scheduler's error packet. A halted hart restarts from address 0 once every channel it serves is in channel reset.

## Firmware

`sched_g.S` is RV32I with no stack and no data section; state that outlives one service call lives in the slot's scratch.

### Main Loop

The image reads SLOTS at start-up and takes one of two poll loops.

**One slot per hart** (the default, `NUM_HARTS` = `NUM_CHANNELS`). The loop reads HEAD_SUM first. HEAD_SUM = 13 (open, valid, `next_ptr` != 0, not last) is a chained head: the loop writes STAGE | STAGE_ARM | STAGE_ARM_NEXT, held in a register, so a running chain costs four instructions from the read to the CMD write. Any other open head is judged inline (`JUDGE`: stage it armed with its own chain outcome, or decline it). With no open head the loop reads SUMMARY; the idle pass is seven instructions. When SUMMARY shows attention, the loop reads HEAD_SUM again before it calls `service`: a head that arrived between the two reads is judged inline. Without that re-read such a head went down `service`'s IDLE / NEXT_DESC path, about 30 instructions later than the inline path, which a fixed-time test (`tile_source_bad_ptype`, 3 seeds in 8) caught.

**Two slots per hart** (`NUM_HARTS` = 4 at 8 channels). The loop reads SUMMARY, then for each slot with attention reads HEAD_SUM and judges an open head inline, else calls `service`.

### Figure 5.3.1: One Hart's Poll Loop

![rapids-g firmware poll loop](../assets/graphviz/12_rapids_g_fw_poll_loop.png)

**Source:** `assets/graphviz/12_rapids_g_fw_poll_loop.dot`

A service call reads STATUS and takes the slot as far as it can. Whatever the state, a head not yet judged is judged first: valid -> STAGE with STAGE_ARM and the head's own chain outcome from HEAD_SUM, so the hardware takes it armed and runs it to completion on its own; not valid -> DECLINE (Section 5.2). In XFER_DATA it then sets up the run bases if the hardware took an EXT descriptor, and tops them up. The hand path covers a descriptor taken unarmed and a declined head: ARM, or COMPLETE, IDLE or NEXT_DESC, then FETCH_DESC and everything FETCH_DESC needs. When a handler's last STATUS read shows the slot has moved on, the call carries on from the new state rather than returning to the poll loop. The dispatch tests XFER_DATA, then NEXT_DESC, the two states a chain sits in. That carry-on is also the call's cost: a hart that enters `service` during a chain can stay in it for several descriptors at about 32 instructions each, which is why the one-slot loop judges every open head itself (measured in Section 5.5; a run-to-completion executive with one handler per step is rapids TASK-037).

### Figure 5.3.2: service(), Dispatched on the Channel State

![rapids-g firmware service call](../assets/graphviz/13_rapids_g_fw_service.png)

**Source:** `assets/graphviz/13_rapids_g_fw_service.dot`

### FETCH_DESC

1. An invalid or tile_bad descriptor: CMD ERROR.
2. Beat totals need no firmware: `scheduler_g` computes them in hardware, with `scheduler`'s own ceiling, when it takes the head (Section 5.2). The EXT set-up reads them back.
3. For TYPE=EXT, the run-base generator of each enabled direction is set up in scratch and its FIFO prefilled.
4. CMD XFER_DATA (pending until the records can go).

### EXT Run Bases

The positions, the step and the 16-bit index wrap are exactly `stream_run_addr_gen`'s: run-contiguous when `stride_0` equals the beat size (one base per run of `inner_count` beats, rows 1, 2, ...), otherwise per beat (every beat after the first, inner index fastest). A base is `base + ((i0 * s0) & m0) + ((i1 * s1) & m1)` in 64 bits. Without wrap masks (the common case) the firmware keeps the address itself and a base is one 64-bit add (`cur += s0` along a row, `row += s1` at a row's end); with masks it keeps the two products as running sums and masks them for each base. Whenever an EXT descriptor's FIFO has room, attention brings the firmware back to top it up; the last base sets the direction's bases-done bit.

### Building the Image

`bin/gen_rapids_g_fw.py` runs `riscv-none-elf-as` / `ld` (text at 0) / `objcopy -O binary` and writes `FW_WORDS` and `FW_IMAGE[]` into `rtl/macro_g/generated/fw/sched_g_fw.svh`, which `rapids_seq_g` includes, so neither simulation nor synthesis needs a file path. `--check` fails when the include is stale. Never edit the include.
