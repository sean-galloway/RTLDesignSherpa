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

# monbus_wr_mux2

**Module:** `monbus_wr_mux2.sv`
**Location:** `rtl/amba/ocelus/`
**Status:** New (2026-10-23); formally checked at the ports

**Plane:** output plane

---

## Overview

`monbus_wr_mux2` merges two AXI4-shaped write FUBs onto one. It exists so `monbus_group_core_1wr` can run two independent burst writers, one per address window, behind a single master-write port.

AXI4 requires the W stream to follow AW order and returns B in order per ID; both writers use the same single ID. So the mux keeps two small queues of source tags, both pushed at every AW handshake: the W queue's head names the port whose W beats go out next (popped on the `wlast` handshake), the B queue's head names the port the next B belongs to (popped on the B handshake). AW arbitration is fixed priority, port 0 over port 1, one AW per cycle. There is no state machine: the whole block is two circular queues and the handshake gating they imply.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `ADDR_WIDTH` | int | 32 | Address width |
| `AXI_ID_WIDTH` | int | 1 | ID width, passed through |
| `ORDER_DEPTH` | int | 8 | Entries per order queue (power of 2). Must cover the sum of both sources' outstanding caps; `monbus_burst_writer` caps at 4 each. |

: Parameters

---

## Ports

| Port | Dir | Description |
|------|-----|-------------|
| `s0_aw*`, `s0_w*`, `s0_b*` | | Port 0 (priority): AXI4-shaped write FUB in |
| `s1_aw*`, `s1_w*`, `s1_b*` | | Port 1: AXI4-shaped write FUB in |
| `m_aw*`, `m_w*`, `m_b*` | | Merged AXI4-shaped write FUB out |

: Ports (standard AXI4 write-channel fields: id, addr, len, size, burst on AW; data, strb, last on W; id, resp on B)

---

## Behaviour

| Channel | Rule |
|---|---|
| AW | `m_awvalid` when either source is valid and neither order queue is full. Port 0 is granted whenever it is valid; port 1 only when port 0 is not. `s*_awready` is `m_awready` gated the same way. |
| W | With the W queue non-empty, the head port's W channel passes through (`m_wvalid`, data, strb, last); its `wready` is `m_wready`, the other port's `wready` is 0. Empty queue: nothing moves. |
| B | With the B queue non-empty, `m_bvalid` is presented to the head port only, and `m_bready` is that port's `bready`. Empty queue: nothing moves. |

: Channel rules

A granted AW is pushed to both queues on the same cycle, so the source's W beats can start the next cycle, which is when `monbus_burst_writer` loads the sub-burst anyway: no bubble is added.

**Deadlock freedom** rests on the sources: a source that raises `awvalid` must be able to deliver that burst's W beats without waiting on anything the mux controls. `monbus_burst_writer` plans bursts only from beats already in its FIFO, so this holds. A source that issued an AW it cannot yet back with data would stall the other port behind it; that is an AXI ordering consequence, not a mux defect.

**Starvation** of port 1 under a sustained port 0 stream is by design: port 0 is the error writer.

---

## Verification

`formal/amba/monbus_wr_mux2` (`make prove cover`, BMC depth 16, `ORDER_DEPTH` 4) keeps its own AW-order queue from the port handshakes and checks at the ports:

- an `m_aw` handshake is exactly one `s_aw` handshake, port 0 first, fields passed through
- no AW handshake while the order queue is full; occupancy never exceeds the depth
- W: the oldest-AW port owns the W channel (valid, data, strb, last, ready), the other port's ready is 0; nothing moves with the queue empty
- B: handed to the oldest-AW port only, `m_bready` is that port's; nothing moves with the queue empty
- covers: the two ports interleaved with a B back to port 1, a port-1 burst completing behind a port-0 burst, the order queue full

Three mutations were checked (AW priority inverted; B routed to the wrong port; grant lock removed), each failing the proof. Induction does not close because the harness queue cannot be tied to the DUT's, which is why the sibling `monbus_group_core` proof is BMC too.

---

## Related

- [monbus_group_core_1wr](monbus_group_core_1wr.md): the consumer
- [monbus_burst_writer](monbus_burst_writer.md): the sources
- `rtl/amba/filelists/monbus_wr_mux2.f`
