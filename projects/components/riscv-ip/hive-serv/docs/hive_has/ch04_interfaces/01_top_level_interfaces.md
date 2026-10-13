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

# Top-Level Interfaces

`hive_top` is the subsystem boundary. Signal groups below are architectural —
final port names are fixed with the RTL (see MAS, Chapter 3); integrators
should treat the *classes* here as the contract.

## External Interface Summary

| Interface | Type | Width | Purpose |
|-----------|------|-------|---------|
| **Host interface** | Slave | 32-bit | UART and/or AXI4-Lite for host commands, status, and firmware load |
| **AXIS CDA TX** | Master | 256-bit | CDA descriptor injection toward RAPIDS (via Delta) |
| **AXIS SERV TX (16×)** | Master | 128-bit | PKT_CONFIG / PKT_STATUS injection from each SERV monitor |
| **AXIS HIVE-C RX** | Slave | 128-bit | PKT_STATUS aggregation return into HIVE-C |
| **Control Network** | Internal | 32-bit | HIVE-C ↔ SERV communication (Block 3) |
| **Router monitor taps (16×)** | Internal | per Delta | Buffer occupancy, packet counts, error flags from each tile router |

: External interface summary

## Communication Protocol Rule (owner, 2026-10-13)

**Everything that crosses a block boundary toward the fabric is a stream;
only register files are memory-mapped.**

- **AXI4-Stream** carries all packet traffic: CDA injection, SERV
  PKT_CONFIG/PKT_STATUS, and the status return path. AXIS is delta's
  native interface, and the `tuser`/`tdest`/`tid` packet classification
  (§4.2) with the ~10-20 cycle inband latency target only exist on the
  stream path.
- **AXI4-Lite** is used exclusively for register windows: the host
  interface and HIVE-C's AXIL master window to RAPIDS/Delta/SERV
  configuration.
- **No AXI4 full anywhere in HIVE.** HIVE never touches DDR and moves no
  burst traffic; the full protocol buys nothing here.
- The internal control network is **AXIS-shaped** too (32-bit frames on
  `tvalid/tready/tlast`, `tuser[0]` = urgent flag) so the repo stream BFMs
  and the Ocelus monitor system cover it without bespoke protocol work
  (MAS §2.4).

## Host Interface

Two physical options, one command set:

- **UART** — serial console-style command channel; default on the PoC board
  (NexysA7 USB-UART bridge). Fixed 115200 8N1 in the PoC; baud is a firmware
  configuration value, not a synthesis parameter.
- **AXI4-Lite slave** — memory-mapped command/status window for SoC
  integration (e.g., a Zynq or PCIe-attached host). Same command encodings as
  the UART path; selection is a synthesis-time option, not runtime.

The host issues high-level transfer commands ("matmul layer N, tiles 0-7");
HIVE-C decomposes them into descriptor batches. The host never writes RAPIDS
registers directly — all DMA control flows through HIVE-C firmware.

## AXIS CDA TX (HIVE-C → Delta)

- **Width:** 256-bit data beats, one descriptor per packet, `tlast` on every
  beat (descriptors are single-beat).
- **Sideband:** `tuser[1:0]` = 2'b01 (CDA) on every beat; `tdest` = 16 (RAPIDS
  virtual tile) for descriptor packets.
- **Rate:** sustained injection must not stall the descriptor engine; target
  is back-to-back descriptor issue with < 30-cycle HIVE-C → RAPIDS latency.

## AXIS SERV TX (16×, per-monitor injection)

- **Width:** 128-bit beats; packets are single-beat in the common case.
- **Sideband:** `tuser[1:0]` = 2'b10 (PKT_CONFIG) or 2'b11 (PKT_STATUS);
  `tdest` = target tile for config writes, 17 (HIVE-C) for status packets
  routed back through Delta where applicable, or local-tile distribution as
  defined by the Configuration Manager.
- **TID:** SERV monitors own their `tid` for identification in status traffic;
  the hardware TID-override rule (§4.2) does not apply to SERV-originated
  packets — only to compute-element PKT_DATA.

## AXIS HIVE-C RX (status return)

- **Width:** 128-bit beats.
- **Purpose:** receives PKT_STATUS traffic addressed to HIVE-C (virtual tile
  17) through the Delta fabric, where the source elected Delta routing rather
  than the control network (e.g., aggregated tile-level status).

## Control Network (internal)

Star topology, HIVE-C master / 16 SERV slaves. 32-bit command/status frames
with valid/ready handshake; in-order, lossless delivery. Frame layout is an
implementation decision and lives in the MAS (Chapter 3); the architectural
guarantees are the latency targets and the ordering/fairness contract in
Chapter 3 above.

## Router Monitor Taps (internal)

Each SERV monitor observes its local tile router through a passive tap —
buffer occupancy per direction, packet counters, error flags. Taps are
read-only observation; the SERV cannot inject values into the router data
path. SERV-originated *actions* travel as PKT_CONFIG packets through the
normal injection path, never through the tap.

---

**Last Updated:** 2026-10-13
