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

# 5. Crossbar Switch

## 5.1 Non-Blocking 5×5 Design

The crossbar provides conflict-free connections between any input-output port pair:

```
        N    S    E    W    L  (inputs)
      +---+---+---+---+---+
   N  | X | X | X | X | X |
      +---+---+---+---+---+
   S  | X | X | X | X | X |
      +---+---+---+---+---+
   E  | X | X | X | X | X |
      +---+---+---+---+---+
   W  | X | X | X | X | X |
      +---+---+---+---+---+
   L  | X | X | X | X | X |
      +---+---+---+---+---+
     (outputs)

Each X is a 128-bit mux + control
```

## 5.2 Crossbar Architecture

```
Input Port 0 (North)  ----+
                          |
Input Port 1 (South)  ----+
                          |
Input Port 2 (East)   ----+---- 5:1 Mux ----> Output Port 0
                          |
Input Port 3 (West)   ----+
                          |
Input Port 4 (Local)  ----+

(Repeat for each output port)
```

## 5.3 Control Logic

```verilog
// Crossbar control signals
logic [4:0][2:0] xbar_sel;  // 5 outputs × 3-bit select (0-4)

// Example: Route North input to East output
xbar_sel[PORT_EAST] = 3'd0;  // Select input 0 (North)

// Multiplexer implementation
always_comb begin
    case (xbar_sel[output_port])
        3'd0: output_data[output_port] = input_data[PORT_NORTH];
        3'd1: output_data[output_port] = input_data[PORT_SOUTH];
        3'd2: output_data[output_port] = input_data[PORT_EAST];
        3'd3: output_data[output_port] = input_data[PORT_WEST];
        3'd4: output_data[output_port] = input_data[PORT_LOCAL];
    endcase
end
```

## 5.4 Conflict Resolution

**No conflicts possible:** Each output port has independent control, and the VC allocator ensures only one input requests a specific output per cycle.

**Simultaneous transfers:**

```
Example: 4 packets routed simultaneously

Input North -> Output East   (Packet A)
Input South -> Output West   (Packet B)
Input East  -> Output Local  (Packet C)
Input West  -> Output North  (Packet D)
Input Local -> Output South  (Packet E)

All 5 transfers happen in parallel (non-blocking)
```

## 5.5 Performance

- **Latency:** 1 cycle (combinational mux + output register)
- **Throughput:** 5 × 128 bits @ 100 MHz = 8 GB/s aggregate per router
- **Resource cost:** ~400 LUTs (5 × 5:1 muxes for 128 bits), ~200 FFs

## 5.6 Implementation Trade-offs

| Approach | LUTs | Latency | Notes |
|----------|------|---------|-------|
| Full 5×5 muxes | ~400 | 1 cycle | Used in DELTA |
| Partial crossbar | ~250 | 1 cycle | Restricts some paths |
| Staged crossbar | ~300 | 2 cycles | Lower LUT cost, higher latency |

**DELTA uses full 5×5:** Maximum flexibility, single-cycle latency critical for low-latency routing.

---

**Back to:** [Block Overview](00_block_overview.md) | **Next Chapter:** [AXIS Interface Specification](../ch03_interfaces/01_axis_interface_spec.md)
