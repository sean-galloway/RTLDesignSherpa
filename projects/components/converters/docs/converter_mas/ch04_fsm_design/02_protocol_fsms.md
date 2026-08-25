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

# 4.2 Protocol Converter FSMs

These are the state machines inside the protocol converters.

## 4.2.1 AXI4 to AXI4-Lite Read FSM

The real machine has THREE states, and none of them waits for R:

```systemverilog
typedef enum logic [1:0] {
    RD_IDLE       = 2'b00,   // no burst in flight
    RD_BURST      = 2'b01,   // issuing the AXIL4 reads of a burst
    RD_LAST_BEAT  = 2'b10    // issuing the burst's final read
} rd_state_t;
```

Earlier revisions documented IDLE/SINGLE/DECOMPOSE/WAIT_R. Two of those
never existed: a single-beat read (`ARLEN==0`) takes a passthrough leg
and never leaves `RD_IDLE`, and there is no wait-for-R state at all --
the address and data paths are decoupled, with ARs issuing at the
downstream accept rate regardless of R (see 3.2). What serializes
bursts is not an FSM
state but the one-outstanding-burst guard: the burst-tracking registers
(`r_r_id`/`r_r_len`/`r_r_beat_count`) hold exactly one burst, so
`s_axi_arready` is held off until the in-flight burst delivers its last
beat. Response aggregation is the live-beat worst-case fold of 4.3.3.

## 4.2.2 AXI4 to AXI4-Lite Write FSM

Also three states (`WR_IDLE`/`WR_BURST`/`WR_LAST_BEAT`), same
passthrough leg for `AWLEN==0`, same one-outstanding guard on the B
side. There are no `r_aw_pending`/`r_w_pending` flags: W is gated
directly against the state of the AW that owns it --

- during the burst-capture cycle W is held off (`w_burst_capture`), or
  the first W beat of the next burst would slip out while the previous
  burst is finishing and pair with the wrong address;
- during a burst, W passes only once this burst's AW has been sent
  (`r_aw_sent`) or is being sent in the same cycle;
- single beats pass straight through.

See 3.2's "W gated on the AW that owns it" for the exact equations.

## 4.2.3 AXI4 to APB FSMs

The convert core runs a command FSM (`IDLE`/`READ`/`WRITE`, writes
preferred) that packetizes each burst into per-APB-beat commands, and a
response FSM (`RSP_IDLE`/`RSP_ACTIVE`) that reassembles rsp packets
into AXI responses. PSEL/PENABLE setup/access phases are NOT here --
they belong to `apb4_master` on the far side of the shim's CDC. Full
description in 3.4.5.

## 4.2.4 Timing Analysis

**AXI4 to AXIL4.** A single-beat transfer is a combinational
passthrough -- no converter-inserted wait state. In a burst the
decomposed requests issue at the downstream ACCEPT rate, independent of
responses: `m_axil_arvalid` in RD_BURST holds every cycle and the beat
tracker advances on `m_axil_arvalid && m_axil_arready` -- no signal in
the request path samples `m_axil_rvalid`/`m_axil_bvalid`. Against a
pipelining slave, N requests issue in N consecutive cycles and the
burst finishes one response latency later; the old "2 cycles overhead /
2N cycles per burst" figures described a serialization the RTL does not
have. Bursts do not overlap each other (the one-outstanding guard
above); that is the only converter-imposed serialization.

**AXI4 to APB.** Per APB beat: command packet -> CDC (2-flop gray
crossing each way) -> APB setup + access (2 pclk minimum, plus
PREADY stalls) -> response packet -> CDC back. Latency is dominated by
the two clock crossings and the APB protocol itself; no measured
characterization is published here.
