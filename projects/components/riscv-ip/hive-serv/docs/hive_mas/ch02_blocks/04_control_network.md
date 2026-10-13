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

# control_network (Block 3)

The star between HIVE-C and the sixteen monitors. Low bandwidth, hard
latency and fairness requirements: commands in < 10 cycles, uplink
aggregation across all 16 < 20 cycles, no slave starves. The block spans
two clock domains — master side in `hive_c_clk`, slave side in `serv_clk` —
with the CDC FIFOs below as the only crossing.

```
control_network
├── control_packetizer.sv   # Command/status frame encode + decode
├── control_router.sv       # Star fan-out: address decode, multicast
├── control_arbiter.sv      # Round-robin uplink arbitration (16 → 1)
└── cdc_fifo_* (repo lib)   # Per-direction async FIFOs (see §1.2 depths)
```

: Control network module tree

## Submodules

**`control_packetizer`.** Frames are 32-bit (HAS §4.1 contract):

```
Bits [31:24]: Command / status opcode
Bits [23:16]: Target SERV id (command) or source SERV id (status);
              8'hFF = broadcast (commands only)
Bits [15:0]:  Payload (threshold values, context id, error code, ...)
```

Command and status share the opcode space with direction implied by the
port. Multicast is mask-free: broadcast reaches all slaves; selective
multicast is done by issuing multiple unicast frames.

**`control_router`.** Pure fan-out — one master port to sixteen slave
ports, address-decoded, no buffering beyond the CDC FIFOs. In-order per
slave; commands to different slaves may be in flight simultaneously.

**`control_arbiter`.** Round-robin over the sixteen uplink FIFOs,
non-preemptive per frame, urgent flag honored as next-grant priority (an
alert frame marked urgent wins the grant after the current frame). Fairness
is structural: equal weights, one frame per grant; starvation is
impossible by construction and asserted formally.

## Performance Verification Hooks

Grant sequence, per-slave service interval, and FIFO occupancy are exported
to the observation bus; the < 20-cycle all-16 aggregation target is checked
by a cocotb scoreboard counting grant cycles across a full round.

---

**Last Updated:** 2026-10-12
