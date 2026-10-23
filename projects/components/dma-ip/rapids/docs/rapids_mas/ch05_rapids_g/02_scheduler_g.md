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

# scheduler_g

**Module:** `scheduler_g.sv`, `scheduler_g_base_fifo.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/fub_g/`
**Status:** Implemented (rapids TASK-034)
**Last Updated:** 2026-10-22

---

## Overview

`scheduler_g` has the whole port list of RAPIDS's `scheduler` plus a sequencer window. Inside it is `scheduler_core` (Section 2.1), the same two byte-to-beat ceilings as `scheduler`, and small pieces in place of its state machine and run-base generators:

- a state register written by command, with an edge table and the two interlocks;
- pre-validation: the firmware judges the next descriptor while this one runs, and the hardware takes the approved edges itself;
- the beat totals, computed in hardware with `scheduler`'s own ceiling and loaded from the skid head on the cycle it is taken, and the bases-done flags, written by the firmware;
- two four-entry run-base FIFOs (`scheduler_g_base_fifo`), one per direction.

## Sequencer Port

| Signal | Dir | Description |
|---|---|---|
| `seq_wr_en`, `seq_wr_addr[4:0]`, `seq_wr_data[31:0]` | in | a word write into the window (registered in `rapids_seq_g`) |
| `seq_rd_addr[4:0]`, `seq_rd_data[31:0]` | in / out | a word read; combinational here, registered in `rapids_seq_g` |
| `seq_attn` | out | the firmware has something to do on this channel |
| `seq_fault` | in | the hart serving this channel has halted: a fatal fault |

: Table 5.2.1: Sequencer port

## Register Window

| Word | Read | Write |
|---|---|---|
| 0 | STATUS | CMD: `[6:0]` next state (0 = none), `[8]` read bases done, `[9]` write bases done, `[10]` STAGE, `[11]` ARM, `[12]` ARM to NEXT_DESC, `[13]` GEN_OK, `[14]` DECLINE, `[15]` STAGE_ARM, `[16]` STAGE_ARM to NEXT_DESC |
| 1-2 | SRC_LO, SRC_HI | 1: FW_ERROR (sends an error packet, data `{word, PKT_LO}`); 2: reserved |
| 3-4 | DST_LO, DST_HI | 3: RD_BASE_LO, 4: RD_BASE_HI (the HI write pushes `{HI, LO}`) |
| 5 | LENGTH (bytes) | WR_BASE_LO |
| 6 | NEXT_PTR | WR_BASE_HI (pushes) |
| 7-12 | chunk 1 words 0-5 (`descriptor_ext_t`) | 7: PKT_LO (the next packet's low data word); 8: FW_DEBUG (sends a debug packet, data `{word, PKT_LO}`); 9-12: reserved |
| 13 | FIFO: `[2:0]` read bases queued, `[6:4]` write bases queued, `[15:8]` CMD_ERR, `[16]` firmware packet pending | -- |
| 14 | CFG: `[15:0]` BYTE_LANES, `[19:16]` OFF_W, `[20]` EN_READ, `[21]` EN_WRITE, `[22]` EXT built, `[23]` TILE_HDR built | -- |
| 15-18 | the skid head, before it is taken: src `[31:0]`, dst `[31:0]`, length, descriptor `[223:192]` (valid, opcode, type, tile op) | -- |
| 19-20 | the beat totals in use (hardware) | -- |
| 21 | HEAD_SUM: the skid head's `[0]` valid, `[1]` last, `[2]` chain (`next_ptr != 0`), `[3]` open (not yet staged or declined, in a state where STAGE and DECLINE are legal) | -- |

: Table 5.2.2: The window, by word

| STATUS bits | Field |
|---|---|
| `[6:0]` | state (`channel_state_t`) |
| `[7]` | `seq_attn` |
| `[8]`, `[9]`, `[10]` | descriptor at the skid head, channel enable, channel reset active |
| `[11]`, `[13:12]` | descriptor valid, opcode |
| `[14]`, `[15]`, `[16]` | last, gen_irq, chain (`next_ptr != 0`) |
| `[17]`, `[18]`, `[19]` | tile_bad, pkt_ok, exec_complete |
| `[20]`, `[21]` | start pending, cmd_err (sticky) |
| `[22]`, `[23]`, `[24]`, `[25]` | EXT, header only, read per-beat, write per-beat |
| `[26]`, `[27]` | read bases done, write bases done |
| `[28]`, `[29]`, `[30]`, `[31]` | armed, head staged, EXT set-up needed, head declined |

: Table 5.2.3: STATUS

## Commands and the Edge Table

A CMD write names the next state. The table below is the only way state changes outside the interlocks. A command it does not list is ignored, sets the sticky `cmd_err` and counts in CMD_ERR (saturating at 255; a channel reset clears both).

| From | Command | Condition | Effect |
|---|---|---|---|
| IDLE | FETCH_DESC | a descriptor at the head, channel enabled | the head is taken on the same edge |
| NEXT_DESC | FETCH_DESC | a descriptor at the head | taken |
| FETCH_DESC | XFER_DATA | descriptor valid, not tile_bad | start pending; taken the cycle `pkt_ok` holds, which is the cycle the packet records fire |
| XFER_DATA | COMPLETE | exec_complete | |
| COMPLETE | IDLE or NEXT_DESC | -- | |
| FETCH_DESC, XFER_DATA, COMPLETE, NEXT_DESC | ERROR | -- | |

: Table 5.2.4: Legal edges

CH_ERROR is left only by a channel reset, as in RAPIDS's `scheduler`. The pending start is what keeps the packet records a single handshake: `scheduler_core` raises them only with `start_req`, so a FETCH_DESC held by the firmware never offers a record early.

A command that arrives after a channel reset it was not written for -- the firmware was part-way through a handler when the reset came -- is ignored by the same table and counted. The equivalence tests expect CMD_ERR to stay 0 on every channel that is never reset.

## Pre-validation and the Automatic Edges

Owner direction, 2026-10-21: "Pre validation is a must." While descriptor N transfers, the firmware:

- ARMs N: complete it on `exec_complete`, then go to NEXT_DESC (`[12]` = 1) or IDLE. Legal once per descriptor, in XFER_DATA.
- judges the descriptor at the skid head: valid -> STAGE; not valid -> DECLINE. Legal while a descriptor is at the head and not yet judged, from XFER_DATA through NEXT_DESC.
- with STAGE, may set STAGE_ARM (`[15]`) and its NEXT_DESC choice (`[16]`): the head's own chain outcome, decided from HEAD_SUM. The hardware then takes that head already armed. STAGE_ARM without STAGE is illegal and counted.

STAGE_ARM is how the firmware keeps up with short descriptors. Without it, every descriptor needs an ARM written inside its own XFER_DATA, and the firmware's path to that write is about 25 instructions -- 200 clocks at 8 harts, where a 64-beat descriptor transfers in under 90. Each such descriptor finished before it was armed and went the hand path: 672 clocks per descriptor on a 64-beat sink chain (Section 5.5). With STAGE_ARM, a descriptor needs one firmware write, made any time before its predecessor completes.

With N armed, the hardware then takes, in the cycles RAPIDS's `scheduler` would: XFER_DATA -> COMPLETE (on `exec_complete`) -> IDLE or NEXT_DESC -> FETCH_DESC (the staged head, its totals, the start already requested) -> XFER_DATA (when `pkt_ok`). The latched descriptor is still checked (valid, tile_bad) as on the hand path. Anything not approved stops the sequence and raises attention: an unarmed descriptor, an unstaged or declined head, a disabled channel.

Three ordering rules make it safe, each the fix of a race the equivalence bench found:

| Rule | Why |
|---|---|
| An EXT descriptor completes automatically only once both directions' bases-done bits are set | the firmware writes them after its last push, so no push or done bit of this descriptor can land after the next is taken |
| GEN_OK (set-up done) is written before the set-up | a descriptor cannot complete before its done bits, which the set-up writes after GEN_OK, so a GEN_OK can never land on the next descriptor |
| The firmware judges both directions' refills on one STATUS snapshot | a fresh STATUS read after the first direction's last done bit may already describe the next descriptor |

A head the hardware takes is flagged (`[30]`) when it is EXT, and the firmware sets up its run bases in XFER_DATA; run 0 uses the descriptor's own address, so only short first runs wait for them.

## Firmware Packets

The firmware can put its own packets on the channel's MonBus port, from the channel's agent:

| Write | Packet type | Event code | Event data |
|---|---|---|---|
| FW_DEBUG (word 8) | `PktTypeDebug` | `RAPIDS_EVENT_FW_DEBUG` (0x09) | `{written word, PKT_LO}` |
| FW_ERROR (word 1) | `PktTypeError` | `RAPIDS_EVENT_FW_ERROR` (0x0A) | `{written word, PKT_LO}` |

: Table 5.2.5: Firmware packets

`scheduler_core`'s own packets are one-cycle pulses and always win the cycle; a firmware packet leaves in the first cycle with none and `mon_ready` high. One packet waits at a time (FIFO `[16]`); a send while one waits is dropped and counted in CMD_ERR, like a push to a full base FIFO. A firmware error packet only reports: it does not move the channel to CH_ERROR, which stays a CMD or an interlock. Neither packet type is a completion, so `cfg_sched_compl_enable` does not filter them.

## Attention

`seq_attn` is high when the firmware has work on the channel, and is what the sequencer's SUMMARY register reports:

- IDLE with the channel enabled and an unstaged descriptor at the head; NEXT_DESC with an unstaged descriptor at the head;
- FETCH_DESC with no start pending, or turned tile_bad;
- XFER_DATA not yet armed, EXT set-up needed, an EXT base FIFO with room and bases still to come, or an unjudged head;
- COMPLETE not armed (the hand path).

Nothing raises attention in CH_ERROR, during a channel reset, or on a fault.

## Run-Base FIFOs

`scheduler_g_base_fifo` holds four 64-bit bases (the depth of `stream_run_addr_gen`'s own queue). A LO write is held; the HI write pushes `{HI, LO}`. The FIFO is flushed whenever the channel is outside FETCH_DESC and XFER_DATA, and on a channel reset, so a base can never outlive its descriptor. A push to a full FIFO is dropped and counted in CMD_ERR. `scheduler_core` takes a base only between runs, exactly as from the generator.
