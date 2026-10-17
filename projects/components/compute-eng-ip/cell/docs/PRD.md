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

**[← Back to cell](../README.md)**

# Cell — Compute Engine IP Product Requirements Document

**Version:** 0.1 (owner datapath decisions 2026-10-16; ALU element-width
note 2026-10-16)
**Status:** Pre-HAS PRD. This document is the cell's product definition;
the HAS/MAS follow it. The tile architecture it plugs into is the adopted
hierarchy of [`tile/docs/TILE_SPEC.md`](../../tile/docs/TILE_SPEC.md) §11
(owner decision 2026-10-16); the packet header, payload types, coordinate,
and credit/grant protocols referenced below are defined there and are not
restated except where the cell consumes them.

---

## 1. Identity and scope

The **cell** is the tile's compute unit: sixteen of them make a tile.
Each cell contains exactly **one delta node** — a `delta_mesh_cell`
instantiated inside the cell, its local port facing the cell's internal
datapath and its seven other ports passing through to the cell
boundary. That containment is the **entire** cell↔delta relationship
(owner clarification 2026-10-16): the node is a black-box subcomponent
governed by delta's own HAS/MAS, and everything else in the cell — the
memories, the execution FSM, the ALU, the packetizer, the credit logic,
the registers — is the cell's own design, speaking the tile-level
contracts of TILE_SPEC §11, not delta internals. The node fills the
cell's input memory from rapids traffic; the cell's ALU and execution
FSM consume that memory and produce results; results leave as batched
flits back through the node toward rapids. As each input line is
consumed, a credit returns to rapids so it may write more.

Owner decision 2026-10-16: the cell's compute engine is the
**ALU + execution FSM** described here. The earlier CGRA-array ambition
([README](../README.md), 2026-10-13) is **deferred** — §11 — and the
[`axon_spec.md`](axon_spec.md) sketch (SERV-based result collector) is
**superseded**: the result collection, packetization, and streaming it
proposed are this PRD's output path, and its interfaces section predates
the adopted §11 header/credit protocols.

Out of scope: tetrad/root node internals, rapids internals, the CXS
modules themselves, and fabric-level Z stacking.

## 2. Architecture

```
                        mesh ports (±X/±Y/±Z, P_DIA, P_DIA2)
                                │
              ┌─────────────────┴───────────────────┐
              │     delta_mesh_cell (from delta)    │
              │            local port               │
              └───────┬───────────────────▲─────────┘
            packets   │                   │ result packets
                      ▼                   │ (grants gate this path)
              ┌──────────────┐     ┌──────┴───────┐
              │ rx header/   │     │  packetizer  │  batch X flits + header
              │ demux        │     └──────▲───────┘
              └──────┬───────┘            │ result lines
                     ▼                    │
              ┌──────────────┐     ┌──────┴───────┐
              │ INPUT MEMORY │     │ RESULT MEMORY│
              └──────┬───────┘     └──────▲───────┘
                     │ lines              │ lines
                     ▼                    │
              ┌───────────────────────────┴──┐
              │  ALU + execution FSM          │
              │  (config-selected function)   │
              └───────────────────────────────┘
                     │
                     │ consumed line
                     ▼
              ┌──────────────┐     credit packets (ptype=credit, add)
              │ credit logic │────▶ node local port ──▶ rapids
              └──────────────┘
```

| Block | Function | Notes |
|---|---|---|
| `delta_mesh_cell` | network attachment | instantiated black box, not owned, here — containment is the whole cell↔delta relationship (owner clarification 2026-10-16); the cell consumes its local port and passes its mesh ports through; delta HAS/MAS govern only the node |
| rx header/demux | parses §11.5 header, routes payload to input memory, handles `cfg` writes to registers | header on head-beat TUSER (AXIS) or first flit (CXS), per §11.6 |
| input memory | rapids-written operand/input buffer | sized in lines; its flit capacity is the boot advertisement value |
| ALU + execution FSM | pops line(s), applies config-selected function, pushes result line(s) | §4; the cell's only datapath |
| result memory | buffers result lines before packetization | sized with §12 |
| packetizer | batches result writes into X flits, builds §11.5 header, sends via node | sends only against grants (§6.3) |
| credit logic | returns credits for consumed input lines | §6.2; batching config N, default 1 |
| config registers | AXIL, registers-only per house rule | §7 |

## 3. Dataflow

1. **Fill.** Rapids sends a write packet (`ptype` = `mem`, destination
   coordinate `{level=0, cell X, Y, Z}`, target address inside the
   cell's input-memory window). The node receives it on the local port;
   the demux writes payload lines into the input memory. Rapids spends
   one end-to-end credit per flit sent, header included, from the
   per-destination counter it holds for this cell (§11.9).
2. **Consume.** The execution FSM pops the configured number of input
   lines for its function, computes, and pushes result line(s) into the
   result memory.
3. **Credit return.** As each input line is consumed, the credit logic
   returns credit toward rapids (`ptype` = `credit`, `op` = `add`,
   destination = `level` 3, count per §6.2), so rapids refills the
   space. Credits return on consumption, not arrival (§11.9(3)).
4. **Emit.** When the packetizer has ≥ X result flits (or a flush
   condition fires, §6.3), it builds the §11.5 header — destination
   `level` 3, source = this cell's coordinate, `op` = 0, length = bytes
   that follow, tag = the sink channel rapids granted — and sends the
   packet through the node. A cell never sends into rapids's sink port
   without a grant covering the whole packet, header included (§11.9).

`cfg` packets (`ptype` = `cfg`) write the §7 registers instead of the
input memory; a `cfg` read is answered with a write-format packet to
`level` 3 echoing the tag, per §11.8.

## 4. ALU and execution FSM

The FSM is a simple pop→compute→push loop with a one-function-at-a-time
pipeline; functions are register-selected, and both the function and its
operand pattern come from config, so new functions are RTL table rows,
not new blocks.

**Element-width model (owner note 2026-10-16):** the ALU prioritizes
packed sub-word operations at **B4 / B8 / B16 / B32** granularity. A
32-bit line is read as 8×B4, 4×B8, 2×B16, or 1×B32 elements selected by
an element-width config field; the ALU applies the function to every
element in the line in parallel (SIMD within the line) or to the line
as a scalar, per the function's operand pattern. Wider lines (§12) scale
the element counts, not the element widths.

**v1 function set:**

| Opcode | Function | Operand pattern |
|---|---|---|
| 0 | copy / passthrough | 1 line → 1 line |
| 1 | add | 2 lines → 1 line |
| 2 | sub | 2 lines → 1 line |
| 3 | mul | 2 lines → 1 line (low half) |
| 4 | mac | accumulate: 2 lines + accumulator → 1 line |
| 5 | and / or / xor (sub-op) | 2 lines → 1 line |
| 6 | min / max (sub-op) | 2 lines → 1 line |
| 7 | compare / threshold (sub-op) | 2 lines or line+imm → 1 line (mask/flags) |

Opcode space reserves 5 bits; 8–31 are growth. Exact datapath widths and
multiplier strategy land in the MAS, consistent with the math area's
learning ethos (sophisticated low-latency techniques).

## 5. Packet interface

The cell consumes and produces the §11.5 header unchanged; §11.6
locates it per transport. Fields the cell uses directly:

| Field | Cell use |
|---|---|
| Destination coordinate | demux match against `{level=0, own X/Y/Z}` |
| Source coordinate | reply and credit-return destination (`level` 3 for rapids-bound) |
| `ptype` | `mem` → input memory; `cfg` → registers; `credit` → credit/grant handler |
| `op` | write vs `cfg` read; credit `add` vs `set` |
| Length | payload bytes / credit count / read size |
| Target address | input-memory line index or register offset |
| Tag | echoed on replies and result packets so rapids routes them to the right sink channel |

## 6. Credit behavior

### 6.1 Boot advertisement

After reset the cell sends one `set` credit packet (`op` = 1) to
`level` 3 carrying its input memory's size **in flits**. Rapids's
per-destination counter for this cell starts at 0 and cannot send until
the advertisement arrives — the advertisement is the cell's "alive"
(§11.10). The packet rides the credit VC and needs no grant.

### 6.2 Consumed-line credit returns

- Each input line consumed by the FSM owes rapids one credit return.
- Returns are `add` credit packets to `level` 3, per §11.9(4): routed
  like any packet by destination coordinate; the sink port accepts them
  unconditionally and never stores them.
- **Batching (owner decision 2026-10-16):** a config register `N`
  batches returns — one credit packet per N consumed lines, with a
  timeout so a partial batch drains. **N = 1 is the default and the
  exact per-line behavior.** N > 1 trades return latency for less
  credit-packet traffic on the fabric.

### 6.3 Grants on the result path

The result path adopts §11.9's grant mechanism as decided:

1. The cell keeps one grant counter per sink channel it uses. Rapids
   grants with a `credit`/`add` packet (destination = the cell, tag =
   sink channel, length = N flits); the cell adds N to that channel's
   counter.
2. The packetizer sends a result packet only while the counter covers
   the whole packet, header included, and spends the counter as it
   sends.
3. A multicast `set`-0 from rapids (failover resync, §11.10) zeroes all
   grant counters; the cell then waits for fresh grants.
4. Whether a cell may *ask* for a grant is a §10 open item (rapids-side
   policy); the cell needs no ask path for v1.

## 7. Config registers

AXI4-Lite, registers-only (house rule); routing/mode config travels
in-band as `cfg` packets per the standing owner decisions. v1 map:

| Offset | Register | Notes |
|---|---|---|
| 0x00 | `CTRL` | enable, soft reset, flush-and-send (packetizer) |
| 0x04 | `STATUS` | busy, input-empty, result-nonempty, grant counters nonzero |
| 0x08 | `FUNC_SEL` | opcode (5b) + sub-op (2b) + element width (2b: 00=B4, 01=B8, 10=B16, 11=B32) |
| 0x0C | `OP_LINES` | input lines per function invocation |
| 0x10 | `EMIT_BATCH_X` | flits per result packet (packetizer) |
| 0x14 | `CREDIT_BATCH_N` | consumed lines per credit packet, default 1 |
| 0x18 | `IRQ_EN` | done, error, grant-starved, credit-timeout enables |
| 0x1C | `IRQ_STATUS` | write-1-clear status |
| 0x20+ | counters | lines in, lines out, credits returned, packets sent (§8) |

## 8. Status and observability

- IRQs: computation done, error, grant-starved (a packetizer with data
  and no grant, time-limited), credit-timeout.
- Software counters per §7.
- One MonBus observer stream per cell, per the tile's §5 aggregation
  hierarchy: the cell's stream is the leaf the tetrad-level merge
  consumes. Exact leaf selection is the tile §10 open item.

## 9. Verification hooks

cocotb + rds-dv BFMs per the standing convention. Test levels follow the
house gate/func/full grid. Natural hooks: drive the node from a GAXI
master instead of a mesh (the node's local port is a normal stream
face), force credits and grants from the TB, and check the credit loop
(count lines in → credits out) independently of the datapath.

## 10. Dependencies

- `delta_mesh_cell` with modes 9–10 diagonal ports — **landed**
  (fabric-gen-ip/delta, Task 6c).
- rapids per-destination credit counters, grant issuer, and the
  sink-to-source credit-return path — §11.9 requirements list;
  sequencing with the rapids lane.
- rapids_cxs + delta CXS migration — **in flight** (amba lane); the
  cell's §11.6 transport note applies unchanged until delta ports move.
- TILE_SPEC §10 open items that touch the cell: input-buffer sizing,
  grant allocation policy, resync timing.

## 11. Deferred

- CGRA array of richer PEs (2026-10-13 ambition): the cell's
  block boundaries — node, input memory, compute, result memory,
  packetizer — are chosen so an array replaces the ALU+FSM block
  without disturbing the network, credit, or observation contracts.
- Context switching / multi-function pipelines.
- Cell-initiated grant requests.
- Wider-than-32-bit lines (element widths stay B4–B32 regardless; §4).

## 12. Open questions

- Input memory and result memory depths (lines, and flit-conversion for
  the advertisement) — sized in the MAS against the MAS injection-FIFO
  and credit-flow analysis.
- `cfg` read reply path: whether rapids's sink half strips headers
  (TILE_SPEC §11.7 open item) affects nothing here — the cell always
  builds a full reply header.
- Flush conditions for the packetizer beyond batch-X (idle timeout?
  end-of-job marker from the FSM?).

## References

- [`tile/docs/TILE_SPEC.md`](../../tile/docs/TILE_SPEC.md) — adopted tile
  hierarchy, §11 packet header, credits/grants (normative for §§3, 5, 6).
- [`delta_has/ch07_mesh_network/`](../../../fabric-gen-ip/delta/docs/delta_has/ch07_mesh_network/)
  — the node the cell instantiates.
- [`axon_spec.md`](axon_spec.md) — superseded 2026-10-16 (decision trail).
- [`2026-10-13-delta-mesh-design.md`](../../../../../docs/superpowers/specs/2026-10-13-delta-mesh-design.md)
  — working design record.

---

**Last Updated:** 2026-10-16
**Maintained By:** RTL Design Sherpa Project
