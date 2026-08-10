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

# Design Technique Index

Where to see each design technique used in real, tested code.

This page exists instead of a set of toy examples. The plan was once to write
small demonstration designs — a watchdog here, a CRC pipe there — but every
technique they would have shown is already demonstrated by working project
code that ships, simulates and, in most cases, has run on silicon or FPGA. A
toy copy of a technique is a second implementation that nobody keeps current;
the real one is maintained because it has to work. So: read the real one.

Each entry names the technique, points at the best worked examples in the
tree, and says what to look at when you get there. The method behind each
technique — the rule and the failure that taught it — lives in the repo
handbook under `vault/handbook/design/`; the note name is given with each
entry.

For small self-contained composition examples, this area's own modules
([fifo_sync_multi](fifo_sync_multi.md), [fifo_sync_multi_sigmap](fifo_sync_multi_sigmap.md))
remain the right first read: they wire library blocks together and are fully
tested in `val/integ_common/`.

---

## Streaming datapath — no FSM

Data movers are valid/ready pipelines, never state machines: a state machine
that can observe a data beat caps throughput and hides the backpressure
contract. Handbook note: `streaming-no-fsm`.

| Worked example | What to look at |
|---|---|
| `projects/components/dmas/stream/rtl/fub/axi_read_engine.sv` | A full read mover with zero states on the beat path — flags and qualifiers where an FSM would put states |
| `projects/components/dmas/stream/rtl/fub/axi_write_engine.sv` | The write side; the `axi_wr_sram_drain = m_axi_wvalid && m_axi_wready` coupling fixed a real lost-WLAST deadlock |
| `rtl/amba/gaxi/gaxi_skid_buffer.sv` | The primitive: `s_ready = !r_valid \|\| m_ready`, register the beat, propagate backpressure |

## Minimal control FSM

Where a state machine IS right — schedulers, descriptor lifecycles, init
sequences — keep the fewest states that carry real distinctions: a state that
only waits is a register; a counter does the timing. Handbook note:
`minimal-fsm`.

| Worked example | What to look at |
|---|---|
| `projects/components/dmas/stream/rtl/fub/scheduler.sv` | A real lifecycle FSM in the two-process idiom: registered state, combinational next with default-hold |
| `projects/components/dmas/stream/rtl/fub/descriptor_engine.sv` | Chain/prefetch decisions as FSM exits; the datapath around it stays pipelined |
| `projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/bank_timer.sv` | The de-FSM precedent: a whole state machine retired into counters plus qualifiers, and the result was simpler AND faster |

## Valid/ready handshake discipline

Once valid asserts it holds, payload stable, until ready; ready may be
combinational; never require ready before valid. Handbook note:
`valid-ready-contracts`.

| Worked example | What to look at |
|---|---|
| `rtl/amba/gaxi/gaxi_skid_buffer.sv` | The contract implemented in under 200 lines; every stream block in the repo leans on it |
| `projects/components/dmas/stream/rtl/fub/axi_write_engine.sv` | Registers `awvalid` across the abort boundary — the read engine's combinational `arvalid` retraction is the documented counter-case |

## Clock-domain crossing

Never sample a foreign-domain signal raw; pointers cross Gray-coded and
REGISTERED in the source domain; events cross by handshake. Handbook note:
`cdc`. Everything that crosses a domain lives in `rtl/cdc/` — see the
[rtl-cdc book](../rtl-cdc/index.md).

| Worked example | What to look at |
|---|---|
| `rtl/cdc/counter_bingray.sv` | Why the Gray value is registered before it crosses — combinational bin2gray can glitch through a code that is neither old nor new |
| `rtl/cdc/gaxi_fifo_async.sv` | The async FIFO: Gray vs Johnson pointer trade (`USE_JOHNSON`), power-of-2 depth rule, flag-lag margin |
| `rtl/cdc/cdc_4_phase_handshake.sv` | Req/ack transfer for a word that crosses occasionally; timeout option |
| `rtl/amba/apb4/apb4_slave_cdc.sv` | A consumer wiring it all: a whole APB slave moved across a domain |

## Arbitration and fairness

A shared resource gets an arbiter and a qualifier, not a turn-taking state
machine — and fairness is a measured property, not an assumption (random
traffic does not prove it). Handbook notes: `streaming-no-fsm` (the
turn-taking row), DV note `randomization`.

| Worked example | What to look at |
|---|---|
| `rtl/common/arbiter_round_robin.sv` | The library round-robin with grant/ack mode; its compliance model in the DV framework replays every grant |
| `rtl/amba/monitor/monbus_arbiter.sv` | Arbitration in monitoring infrastructure — many packet sources, one bus |
| `projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_cmd_arbiter.sv` | Bank-parallel selection: per-entry vectors arbitrated in one cycle, the fix that took board bandwidth off a single-bank serialization |

## Timeout, saturation and recovery

Blocking may throttle, never deadlock: reserve the slots that guarantee
recovery, time out the transactions that never complete, and make the
timeout a recoverable event rather than a terminal state. Handbook note:
`sizing-invariants`.

| Worked example | What to look at |
|---|---|
| `rtl/amba/monitor/axi_monitor_timeout.sv` | Per-transaction timeout detection against a shared timer |
| `rtl/amba/includes/monitor_common_pkg.sv` | `cmd_entry_reserve()` — the saturation-recovery contract: tables of 16+ reserve slots so `block_ready` always releases |
| `projects/components/dmas/stream/rtl/fub/scheduler.sv` | A configurable write-timeout that recovers the channel instead of wedging it |

## In-line data integrity

CRC and ECC belong on the datapath as pipelined blocks, computed as the data
flows — not as a post-pass. Library blocks: `dataint_*` in
[rtl-common](../rtl-common/index.md).

| Worked example | What to look at |
|---|---|
| `rtl/amba/shared/axi4_slave_wr_crc_check.sv` | Per-channel CRC over write data, cascade-fed a beat at a time, checked at end of frame |
| `rtl/common/dataint_ecc_hamming_encode_secded.sv` / `_decode_secded.sv` | The SECDED pair — encode, correct single, detect double |

## Composition and field packing

Wrap a generic block once, by name, instead of packing and slicing bits at
every call site. This area's own two modules are the worked example — see
[fifo_sync_multi](fifo_sync_multi.md) and the
[overview](overview.md) for when to reach for them.

---

## Navigation

- **[Index](index.md)** · **[Overview](overview.md)**
- **[Back to Main Documentation Index](../index.md)**
