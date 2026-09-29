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

# 4. Virtual Channel Allocator

## 4.1 Virtual Channel Concept

Two virtual channels (VCs) per physical link prevent protocol-level deadlock and provide QoS:

**VC0 - High Priority:**
- PKT_DESC, PKT_CONFIG, PKT_STATUS
- Control/monitoring traffic has priority
- Lower buffer depth (4 flits) - less latency critical

**VC1 - Standard Priority:**
- PKT_DATA
- Bulk data transfers
- Larger buffer depth (8 flits) - more throughput critical

## 4.2 Credit-Based Flow Control

Each router uses credit-based flow control to prevent buffer overflow:

### Initialization

- Downstream router has 8-flit input buffer per VC
- Upstream router initialized with 8 credits per VC
- Credits represent available buffer slots

### Operation

```
1. Upstream wants to send flit
   - Check if credits[vc] > 0
   - If yes: send flit, decrement credits[vc]
   - If no: stall (wait for credit return)

2. Downstream receives flit
   - Store in input buffer
   - Process/forward flit
   - Send credit back upstream (increment credits[vc])

3. Steady state:
   - Credits flow opposite to flits
   - No overflow possible (guaranteed by credits)
   - Backpressure propagates naturally
```

## 4.3 Arbitration Logic

VC0 has strict priority over VC1:

```verilog
// VC0 has strict priority over VC1
if (vc0_has_packet && vc0_credits > 0) begin
    grant_vc0();
end else if (vc1_has_packet && vc1_credits > 0) begin
    grant_vc1();
end else begin
    idle();
end
```

## 4.4 Credit Management

```verilog
// Per output port, per VC
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        vc0_credits <= VC0_BUFFER_DEPTH;  // Initialize to 4
        vc1_credits <= VC1_BUFFER_DEPTH;  // Initialize to 8
    end else begin
        // Flit sent: decrement credits
        if (send_flit_vc0) begin
            vc0_credits <= vc0_credits - 1;
        end
        if (send_flit_vc1) begin
            vc1_credits <= vc1_credits - 1;
        end

        // Credit return: increment credits
        if (credit_return_vc0) begin
            vc0_credits <= vc0_credits + 1;
        end
        if (credit_return_vc1) begin
            vc1_credits <= vc1_credits + 1;
        end
    end
end
```

## 4.5 VC Assignment by Packet Type

```verilog
always_comb begin
    case (pkt_tuser)
        PKT_DATA:   vc_select = VC1;  // Standard priority
        PKT_DESC:   vc_select = VC0;  // High priority
        PKT_CONFIG: vc_select = VC0;  // High priority
        PKT_STATUS: vc_select = VC0;  // High priority
    endcase
end
```

## 4.6 Performance Characteristics

- **Arbitration latency:** 1 cycle
- **Credit loop latency:** 2-3 cycles (depends on wire delay)
- **Maximum throughput:** 100% (non-blocking when credits available)
- **Resource cost:** ~150 LUTs, ~100 FFs per router

---

**Next:** [Crossbar Switch](05_crossbar_switch.md)
