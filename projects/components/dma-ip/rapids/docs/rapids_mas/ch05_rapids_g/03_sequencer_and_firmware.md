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
**Status:** Implemented (rapids TASK-034, TASK-037, TASK-035)
**Last Updated:** 2026-10-23

---

## rapids_seq_g

One `gatling_core`, used unchanged through its own filelist, with the three memories it needs, each answering in one stage as gatling requires:

| Block | What | Size |
|---|---|---|
| Instruction ROM | the firmware image, from `sched_g_fw.svh`; one read port serves every hart (the barrel fetches for one context per cycle) | `IMEM_WORDS` = 1024 |
| Scratch | per-hart memory, indexed `{context, word}`; the run-base generator state of each slot | `SCRATCH_WORDS` = 128 per hart (256 at four slots) |
| Window decoder | routes a data access to the slot's `scheduler_g` by context and slot | -- |

: Table 5.3.1: rapids_seq_g

Parameters: `NUM_CHANNELS` (4, 8 or 16), `NUM_HARTS` (4, 8 or 16, dividing `NUM_CHANNELS` with at most four slots per hart; default `NUM_CHANNELS`, one hart and one slot per channel; hart h serves channels h + `NUM_HARTS` x s), `IMEM_WORDS`, `SCRATCH_WORDS` (a power of 2, at least 64 per slot; a smaller scratch would alias slot 1 onto slot 0, and elaboration refuses it).

### Data Memory Map

| Address | Region |
|---|---|
| 0x0000_0000 | instruction ROM (fetch only; a data read returns 0) |
| 0x1000_0000 | slot 0 window (Section 5.2), word-indexed |
| 0x1000_0100 + 0x100 s | slot s window (s < SLOTS) |
| 0x1000_1000 | SUMMARY: `[SLOTS-1:0]` `seq_attn` of this hart's slots |
| 0x1000_1004 | SLOTS: slots per hart (1, 2 or 4) |
| 0x1000_3000 | register mailbox (below), aliased by context |
| 0x2000_0000 | scratch, aliased by context |

: Table 5.3.2: Data memory map

Contexts stay implicit (gatling PRD 7): every hart runs the same image, and "slot 0" is a different channel for each, chosen by the context the access comes from. Reads are registered (address in X, data in W); window writes are registered into `scheduler_g` one cycle after X, so a hart's next instruction, `NUM_HARTS` (at least four) cycles later, always sees the effect of its own write. Each hart issues one instruction every `NUM_HARTS` clocks: at the default 8 harts an instruction costs a hart 8 clocks, which is the unit of every firmware cost in Section 5.5.

### Register Mailbox

Each hart can read and write its own half's PeakRDL registers -- the same `rapids_regs` the host programs -- through a mailbox: REG_ADDR (+0x00, byte offset within the half), REG_WDATA (+0x04), REG_CTRL (+0x08: `[0]` go, `[1]` write), REG_STATUS (+0x0C: `[0]` busy, `[1]` done, `[2]` error), REG_RDATA (+0x10). The firmware posts an access and polls; a single-stage barrel cannot wait on a bus. The harts' accesses go out one at a time (`arbiter_round_robin_simple_ack`) on the gatling's one master port, `seq_reg_*`, which the generated tree carries up to the top base. There `rapids_g_reg_arb` decides who pushes into the register block's command queue: the host's APB, the SOURCE gatling and the SINK gatling, round robin, one access outstanding, the response steered back by the held grant. Each gatling's offset is pinned to its half (SRC at 0x0000, SNK at 0x1000), so neither can reach the other's registers. The per-channel `CH_SCRATCH[n].SCRATCH` bits (0x300 in each half) are there for the host and the gatling to share flags or semaphores (not atomic across masters: give each bit one writer). The scheduler firmware does not use the mailbox today.

### Faults

`seq_fault[c]` is the halted bit of the hart serving channel c, so a firmware trap is a fatal fault for that hart's channels: they enter CH_ERROR and send the scheduler's error packet. A halted hart restarts from address 0 once every channel it serves is in channel reset.

## Firmware

`sched_g.S` is RV32I with no stack and no data section; state that outlives one step lives in the slot's scratch. It is an **executive** over a **policy table** (rapids TASK-037). The executive polls and dispatches and is the same for every policy; the table says what each (state, event) pair does. Both firmware defects found on 2026-10-22 came from mixing the two (Section 5.5): the poll and the handlers disagreed about who owned an open head, and a handler that re-dispatched itself kept a hart for several descriptors. Neither can recur in this shape.

### The Executive

Run to completion, no preemption: the barrel's harts are the threads. Each pass of the poll gives a slot at most one handler, and the handler returns to the poll. The image reads SLOTS at start-up and takes one of two polls.

**One slot per hart** (the default, `NUM_HARTS` = `NUM_CHANNELS`). The poll reads HEAD_SUM first. HEAD_SUM = 13 (open, valid, `next_ptr` != 0, not last) is a chained head: the poll writes STAGE | STAGE_ARM | STAGE_ARM_NEXT, held in a register, so a running chain costs four instructions from the read to the CMD write. This chain hook is the one policy entry that lives in the poll itself. Any other open head is judged inline (`judge_head`: stage it armed with its own chain outcome, or decline it). With no open head the poll reads SUMMARY; the idle pass is seven instructions. When SUMMARY shows attention, the poll reads HEAD_SUM again, so a head that arrived between the two reads is judged inline too, then calls `step`.

**Two slots per hart** (`NUM_HARTS` = 4 at 8 channels, or 8 at 16). The poll reads SUMMARY, then for each slot with attention reads HEAD_SUM and judges an open head inline, else calls `step`, unrolled for the two slots.

**Four slots per hart** (`NUM_HARTS` = 4 at 16 channels, rapids TASK-036). The same poll as a loop over SUMMARY's bits, the slot's offset in `sp` (window and scratch share the 0x100 slot stride).

`step` reads STATUS and jumps through `ptab`, indexed by the 6-bit one-hot state: four instructions from the STATUS read to the state's row. `ptab` has 64 entries, so no value of the field can index past it; the five states with work have a jump to their row, and every other entry (CH_ERROR, which only a channel reset leaves, and the values that are not states) returns. The image is linked at 0 and `ptab` sits below 2 KB, so the jump is `jalr` off the index register alone and needs no base register (`gen_rapids_g_fw.py` refuses an image where it does not fit).

### Figure 5.3.1: One Hart's Poll

![rapids-g firmware poll loop](../assets/graphviz/12_rapids_g_fw_poll_loop.png)

**Source:** `assets/graphviz/12_rapids_g_fw_poll_loop.dot`

### The Policy Table

A state's row picks one handler by event, highest priority first. A handler does one step -- one or two CMD writes, or one run-base set-up or top-up -- and returns. No handler loops, re-reads STATUS to carry on, or calls `step`: the slot's next step is the next pass of the poll.

| State | Event, in priority order | Handler | What it does |
|-------------------|----------------------|-------------------|------------------------------|
| any | an open head (in the poll) | `judge_head` | valid: STAGE armed with its chain outcome; not valid: DECLINE |
| IDLE (enabled), NEXT_DESC | head staged, or no head | -- | nothing: the hardware takes a staged head |
| | head declined | `fetch_start` | CMD FETCH_DESC; FETCH_DESC then takes it to CH_ERROR |
| | head open | `judge_head` | as above |
| FETCH_DESC | tile_bad, or descriptor invalid | `fetch_error` | CMD CH_ERROR |
| | start already pending | -- | nothing |
| | valid (never: see below) | `fw_fault` | firmware error packet carrying STATUS; CMD CH_ERROR |
| XFER_DATA | not armed (never) | `fw_fault` | as above |
| | GEN_NEED (an EXT descriptor the hardware took) | `ext_start` | CMD GEN_OK, then set up and prefill the run bases (`ext_init`) |
| | EXT, bases not all out | `ext_refill` | top up both directions' base FIFOs from one STATUS snapshot |
| COMPLETE | armed | -- | nothing: the hardware leaves COMPLETE next cycle |
| | not armed (never) | `fw_fault` | as above |

: Table 5.3.3: The policy table

**The rows marked "never".** Every valid head is staged armed, so the hardware takes it, completes it and leaves COMPLETE on its own; the firmware takes a head itself (FETCH) only when it declined it, and a declined head is invalid by the same test the latch applies. A descriptor can therefore never be in XFER_DATA or COMPLETE unarmed, nor valid in FETCH_DESC by the firmware's hand. TASK-034's firmware still carried a hand path for those states (arm in XFER_DATA, route out of COMPLETE, start from FETCH_DESC); the mutation set showed no test could reach it (MAS 5.5), because nothing can. It is replaced by `fw_fault`: a state the policy never creates stops the channel visibly instead of being guessed at, and a channel reset recovers it.

The run-base routines (`ext_init`, `refill`) are a layer below the table: they are where the next-address algorithm lives, and the descriptor's selector picks one (rapids TASK-035, below).

### Figure 5.3.2: step(), the Policy Table

![rapids-g firmware step and policy table](../assets/graphviz/13_rapids_g_fw_service.png)

**Source:** `assets/graphviz/13_rapids_g_fw_service.dot`

### EXT Run Bases

The positions, the step and the 16-bit index wrap are exactly `stream_run_addr_gen`'s: run-contiguous when `stride_0` equals the beat size (one base per run of `inner_count` beats, rows 1, 2, ...), otherwise per beat (every beat after the first, inner index fastest). A base is `base + ((i0 * s0) & m0) + ((i1 * s1) & m1)` in 64 bits. Without wrap masks (the common case) the firmware keeps the address itself and a base is one 64-bit add (`cur += s0` along a row, `row += s1` at a row's end); with masks it keeps the two products as running sums and masks them for each base. Whenever an EXT descriptor's FIFO has room, attention brings the firmware back to top it up; the last base sets the direction's bases-done bit.

### Next-Address Selector

The descriptor's selector (chunk 0 `[224:217]`, HAS Section 5.1) chooses the algorithm. The image declares the highest one it implements with `.equ ALG_MAX`; `gen_rapids_g_fw.py` writes it into `sched_g_fw.svh` as `FW_ALG_MAX`, and `rapids_seq_g` drives it to every `scheduler_g` as `seq_alg_max`. The check is hardware, the same in both places it is made: `scheduler_core` latches a descriptor whose selector is above it (or non-zero without TYPE=EXT) as invalid, and `scheduler_g` folds the same test into HEAD_SUM's valid bit, so the firmware declines such a head and the chain hook (HEAD_SUM = 13) is untouched. A selector is refused from reset, before the firmware runs an instruction.

| Selector | Set-up | Top-up |
|---|---|---|
| 0 | `gen_init`: positions, step and masks as `stream_run_addr_gen` | `refill` (masked) or `refill_fast` (no wrap) |
| 1, Z-order | `gen_init_z`: unit = a beat or a run of `inner_count` beats; S0 = `stride_0` or `inner_count << OFF_W`; position k = 1 | `refill_z` |

: Table 5.3.4: Next-address algorithms in the image

`refill_z` keeps x x S0 and y x `stride_1` as running sums, like the masked path, and steps the position in Morton order without a multiplier: k -> k + 1 clears k's trailing ones and sets the bit above them, and bit 2i is x's bit i, bit 2i + 1 is y's, so each cleared bit subtracts the stride shifted by i and the set bit adds it -- about two bits a step on average. The generator block's mode word tells `refill` which path to take (1 fast, 0 masked, -1 Z-order), so selector 0 costs one instruction more per masked top-up and nothing on the fast path.

### Building the Image

`bin/gen_rapids_g_fw.py` runs `riscv-none-elf-as` / `ld` (text at 0) / `objcopy -O binary` and writes `FW_WORDS` and `FW_IMAGE[]` into `rtl/macro_g/generated/fw/sched_g_fw.svh`, which `rapids_seq_g` includes, so neither simulation nor synthesis needs a file path. `--check` fails when the include is stale. Never edit the include.
