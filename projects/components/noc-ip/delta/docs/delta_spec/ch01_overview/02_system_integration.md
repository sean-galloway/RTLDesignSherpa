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

# 2. System Integration

## 2.1 Network Position

```
+--------------------------------------------------------------+
|                    HIVE Control Plane                        |
|                                                              |
|  +-------------+          +-------------------------+        |
|  |   HIVE-C    |          |  16x SERV Monitors      |        |
|  | (VexRiscv)  |          |  (one per tile)         |        |
|  +------+------+          +----+-------------+------+        |
|         |                      |             |               |
|    PKT_DESC              PKT_CONFIG    PKT_STATUS            |
|         |                      |             |               |
+---------+----------------------+-------------+---------------+
          |                      |             |
          v                      v             v
+---------------------------------------------------------+
|              DELTA Network (AXIS Mesh NoC)              |
|                                                         |
|  Packet Routing Based on TUSER[1:0]:                   |
|  - PKT_DATA   (00) -> Compute Tiles                     |
|  - PKT_DESC   (01) -> RAPIDS DMA                        |
|  - PKT_CONFIG (10) -> Target Tile(s) Config Registers   |
|  - PKT_STATUS (11) -> HIVE-C Monitoring Aggregator      |
|                                                         |
|   +----+----+----+----+                                 |
|   |R0  |R1  |R2  |R3  |  R = Router + Tile              |
|   +----+----+----+----+  Each has:                      |
|   |R4  |R5  |R6  |R7  |  - 5-port router (N/S/E/W/L)   |
|   +----+----+----+----+  - Network Interface (NI)       |
|   |R8  |R9  |R10 |R11 |  - SERV monitor                 |
|   +----+----+----+----+  - Compute element              |
|   |R12 |R13 |R14 |R15 |  - Packet filter                |
|   +----+----+----+----+                                 |
|                                                         |
|  Special Routing:                                       |
|  - RAPIDS attached as virtual tile 16 (external)        |
|  - HIVE-C attached as virtual tile 17 (external)        |
+---------+---------------------------------+-------------+
          |                                 |
     PKT_DATA                           PKT_DATA
   (to tiles)                          (from tiles)
          |                                 |
          v                                 v
    +----------+                       +----------+
    |  RAPIDS  |<--PKT_DESC------------+  HIVE-C  |
    |   DMA    |                       | (VexRiscv)
    +----------+                       +----------+
         ^
         | AXI4
         v
     [DDR Memory]
```

## 2.2 Packet Flow Matrix

| Source | Packet Type | Destination(s) | Path Through DELTA |
|--------|-------------|----------------|--------------------|
| HIVE-C | PKT_DESC | RAPIDS | Direct route to virtual tile 16 |
| HIVE-C | PKT_CONFIG | Tile(s) 0-15 | Multicast via tile mask |
| RAPIDS | PKT_DATA | Tile(s) 0-15 | XY route to TDEST tile |
| Tile N | PKT_DATA | RAPIDS | XY route to virtual tile 16 |
| Tile N | PKT_DATA | Tile M | XY route peer-to-peer |
| SERV N | PKT_CONFIG | Tile N (local) | Direct to local config registers |
| SERV N | PKT_STATUS | HIVE-C | XY route to virtual tile 17 |

## 2.3 Never Occurs (Hardware Prevents)

- RAPIDS sending PKT_DESC (only receives)
- Compute Tiles sending PKT_DESC (not authorized)
- PKT_DATA routed to HIVE-C (filtered)
- PKT_CONFIG routed to RAPIDS (filtered)

---

**Next:** [Packet Type Routing](03_packet_type_routing.md)
