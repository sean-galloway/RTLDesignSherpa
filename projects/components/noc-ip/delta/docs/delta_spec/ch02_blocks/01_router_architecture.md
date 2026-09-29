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

# 1. Router Architecture

## 1.1 Five-Port Router Design

```
         North (to tile i-4)
            ^
            |
West <------+------> East
  (i-1)     |       (i+1)
            |
            v
         South (to tile i+4)

            |
            v
        Local Port
    (to compute tile i)
```

## Port Functions

- **North/South/East/West:** Inter-router links (128-bit AXIS)
- **Local:** Connection to tile's Network Interface (NI)

## 1.2 Router Block Diagram

```
+------------------------------------------------------------+
|                  Router i                                  |
|                                                            |
|  +----------+  +----------+  +----------+    (×5 ports)    |
|  |  Input   |  |  Input   |  |  Input   |                 |
|  |  Buffer  |  |  Buffer  |  |  Buffer  |                 |
|  | (8 flits)|  | (8 flits)|  | (8 flits)|                 |
|  +-----+----+  +-----+----+  +-----+----+                 |
|        |             |             |                       |
|        +-------------+-------------+                       |
|                      v                                     |
|           +----------------------+                         |
|           |  Packet Classifier   |                         |
|           |  - Reads TUSER[1:0]  |                         |
|           |  - Reads TDEST[3:0]  |                         |
|           |  - Computes next hop |                         |
|           +----------+-----------+                         |
|                      v                                     |
|           +----------------------+                         |
|           |  Virtual Channel     |                         |
|           |  Allocator           |                         |
|           |  - 2 VCs per port    |                         |
|           |  - Credit-based FC   |                         |
|           +----------+-----------+                         |
|                      v                                     |
|           +----------------------+                         |
|           |   Crossbar Switch    |                         |
|           |   5×5 non-blocking   |                         |
|           +----------+-----------+                         |
|                      |                                     |
|        +-------------+-------------+                       |
|        v             v             v                       |
|  +----------+  +----------+  +----------+    (×5 ports)    |
|  |  Output  |  |  Output  |  |  Output  |                 |
|  |  Buffer  |  |  Buffer  |  |  Buffer  |                 |
|  | (4 flits)|  | (4 flits)|  | (4 flits)|                 |
|  +----+-----+  +----+-----+  +----+-----+                 |
|       |            |            |                          |
+-------+------------+------------+-------------------------+
        |            |            |
       AXIS         AXIS         AXIS
     (to next)    (to next)    (to next)
```

## 1.3 XY Routing Algorithm

```verilog
function [2:0] compute_output_port(
    input [3:0] current_tile,  // 0-15 for mesh, 16=RAPIDS, 17=HIVE-C
    input [3:0] dest_tile,
    input [1:0] pkt_type
);
    logic [1:0] curr_x, curr_y;
    logic [1:0] dest_x, dest_y;

    // Extract coordinates (4x4 mesh)
    curr_x = current_tile[1:0];  // Column
    curr_y = current_tile[3:2];  // Row

    // Handle virtual tiles
    if (dest_tile == 16) begin  // RAPIDS
        dest_x = 2'd0;  // Column 0
        dest_y = 2'd4;  // Virtual row 4 (south of row 3)
    end else if (dest_tile == 17) begin  // HIVE-C
        dest_x = 2'd3;  // Column 3
        dest_y = 2'd255; // Virtual row -1 (north of row 0)
    end else begin
        dest_x = dest_tile[1:0];
        dest_y = dest_tile[3:2];
    end

    // XY routing: X-dimension first
    if (dest_x < curr_x) begin
        return PORT_WEST;
    end else if (dest_x > curr_x) begin
        return PORT_EAST;
    end else if (dest_y < curr_y) begin
        return PORT_NORTH;
    end else if (dest_y > curr_y) begin
        return PORT_SOUTH;
    end else begin
        return PORT_LOCAL;  // Arrived at destination
    end
endfunction
```

## 1.4 Routing Latency

**Single-hop latency:**
- Input buffering: 1 cycle
- Routing decision: 1 cycle
- Crossbar traversal: 1 cycle
- Output buffering: 1 cycle (optional)
- **Total: 3-4 cycles per hop**

**Multi-hop examples (4×4 mesh):**
| Source -> Dest | Hops | Latency (cycles) |
|----------------|------|------------------|
| T0 -> T1 | 1 | 3-4 |
| T0 -> T5 | 2 | 6-8 |
| T0 -> T15 | 6 | 18-24 (worst case) |
| Any -> RAPIDS (avg) | 3.5 | 10-14 |
| Any -> HIVE-C (avg) | 3.5 | 10-14 |

---

**Next:** [Network Interface](02_network_interface.md)
