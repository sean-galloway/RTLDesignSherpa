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

# SoC-Level Controllable Arbiter Blocking: Strategic Benefits, PWM Usage Patterns, and Comprehensive Monitoring

## Executive Summary

For testability at SoC, I have combined in a single block a well-tested weighted round robin arbiter with a pulse width modulator (PWM) block and comprehensive monitoring system. The arbiter has a "block arbitration" input port that is connected to the output of the PWM, with all of the needed configuration controls brought out for easy integration.

The ability to controllably block arbiters at the SoC level represents a paradigm shift in system verification, performance analysis, and operational control. By integrating PWM-controlled blocking into weighted round-robin arbiters with real-time monitoring, we gain unprecedented precision in orchestrating system behavior for testing, debugging, and real-time adaptation scenarios.

## Configuration Register Layout

### **Register Organization (X = Instance Identifier)**

| Offset | Register Name | Field Name | High:Low | Description |
|--------|---------------|------------|----------|-------------|
| 0x00 | arb_thresh_lo | prio[31:0] | 31:0 | Agent 0-15 credits (2 bits each)<br/>[31:30]=agent15, [29:28]=agent14, ..., [1:0]=agent0 |
| 0x04 | arb_thresh_hi | prio[31:0] | 31:0 | Agent 16-31 credits (2 bits each)<br/>[31:30]=agent31, [29:28]=agent30, ..., [1:0]=agent16 |
| 0x08 | pwm_ctrl_lo | start | 31 | PWM start trigger (write 1 to begin sequence) |
| 0x08 | pwm_ctrl_lo | repeat_cnt[15:0] | 15:0 | PWM repeat count (0=infinite, 1=single shot, N=repeat N times) |
| 0x0C | pwm_ctrl_hi | period[15:0] | 31:16 | PWM period in clock cycles (1 to 65,535) |
| 0x0C | pwm_ctrl_hi | duty[15:0] | 15:0 | PWM duty cycle in clock cycles (1 to period) |

### **Monitor Configuration Registers**

| Offset | Register Name | Field Name | High:Low | Description |
|--------|---------------|------------|----------|-------------|
| 0x10 | mon_ctrl | enable | 31 | Monitor bus enable (1=enabled, 0=disabled) |
| 0x10 | mon_ctrl | reserved | 30:8 | Reserved, write as 0 |
| 0x10 | mon_ctrl | period[7:0] | 7:0 | Sample period as power of 2 (2^N cycles) |
| 0x14 | mon_thresh_lo | latency[15:0] | 31:16 | Request-to-grant latency threshold (cycles) |
| 0x14 | mon_thresh_lo | starvation[15:0] | 15:0 | Starvation detection threshold (cycles) |
| 0x18 | mon_thresh_hi | fairness[15:0] | 31:16 | Fairness deviation threshold (percentage) |
| 0x18 | mon_thresh_hi | active[15:0] | 15:0 | Active request count threshold |


### **Credit Encoding for Agent Priorities**

| Credit Value | Binary | Description | Relative Weight |
|--------------|--------|-------------|-----------------|
| 0 | 2'b00 | Disabled | No access granted |
| 1 | 2'b01 | Low Priority | Minimum service level |
| 2 | 2'b10 | Medium Priority | Standard service level |
| 3 | 2'b11 | High Priority | Maximum service level |

## Monitor Bus System Architecture

### **64-Bit Monitor Packet Format**

The monitor bus uses a standardized 64-bit packet format for all events:

| Bits | Field Name | Description |
|------|------------|-------------|
| 63:60 | packet_type[3:0] | Event packet type (Error/Threshold/Performance/Debug) |
| 59:58 | protocol[1:0] | Protocol identifier (AXI/Custom) |
| 57:54 | event_code[3:0] | Specific event type within category |
| 53:48 | channel_id[5:0] | Channel/client identifier (0-63) |
| 47:44 | unit_id[3:0] | Unit identifier within agent |
| 43:36 | agent_id[7:0] | Agent identifier |
| 35:0 | event_data[35:0] | Event-specific data payload |

### **Packet Type Definitions**

| Type Value | Type Name | Description | Priority |
|------------|-----------|-------------|----------|
| 4'h0 | PktTypeError | Critical system errors requiring immediate attention | Highest |
| 4'h1 | PktTypeThreshold | Threshold violations and warnings | High |
| 4'h2 | PktTypePerf | Performance metrics and statistics | Medium |
| 4'h3 | PktTypeDebug | Debug information and trace data | Low |

### **Event Code Classifications**

#### **Error Events (PktTypeError)**
| Code | Event Name | Description | Event Data Content |
|------|------------|-------------|-------------------|
| 4'h0 | AXI_ERR_ARBITER_STARVATION | Client starved beyond threshold | [15:0] = starvation timer value |
| 4'h1 | AXI_ERR_PROTOCOL_VIOLATION | Protocol compliance violation | [15:0] = violation type |
| 4'h2 | AXI_ERR_TIMEOUT | Transaction timeout occurred | [15:0] = timeout duration |
| 4'h3 | AXI_ERR_BUFFER_OVERFLOW | Buffer overflow condition | [15:0] = buffer depth |

#### **Threshold Events (PktTypeThreshold)**
| Code | Event Name | Description | Event Data Content |
|------|------------|-------------|-------------------|
| 4'h0 | AXI_THRESH_GRANT_LATENCY | Grant latency exceeded threshold | [15:0] = measured latency |
| 4'h1 | AXI_THRESH_ACTIVE_COUNT | Active request count exceeded | [7:0] = current count |
| 4'h2 | AXI_THRESH_FAIRNESS | Fairness violation detected | [15:0] = dominant client grants |
| 4'h3 | AXI_THRESH_BANDWIDTH | Bandwidth utilization threshold | [15:0] = utilization percentage |

#### **Performance Events (PktTypePerf)**
| Code | Event Name | Description | Event Data Content |
|------|------------|-------------|-------------------|
| 4'h0 | AXI_PERF_GRANT_EFFICIENCY | Grant efficiency metrics | [31:16] = total grants, [7:0] = active count |
| 4'h1 | AXI_PERF_BANDWIDTH_USAGE | Bandwidth utilization report | [15:0] = bandwidth percentage |
| 4'h2 | AXI_PERF_LATENCY_STATS | Latency statistics update | [15:0] = average latency |
| 4'h3 | AXI_PERF_FAIRNESS_REPORT | Fairness distribution report | [15:0] = fairness index |

### **Monitor Bus Interface Signals**

| Signal Name | Direction | Width | Description |
|-------------|-----------|-------|-------------|
| monbus_valid | Output | 1 | Monitor packet valid |
| monbus_ready | Input | 1 | Downstream ready to accept packet |
| monbus_packet | Output | 64 | Monitor packet data |

The monitor bus implements AXI-style valid/ready handshaking with an internal 8-entry FIFO to buffer events during congestion.

### **Monitoring State Machine**

The monitor system tracks multiple metrics simultaneously:

#### **Per-Client Tracking (Arrays)**
- **Request Timers**: 16-bit counters tracking how long each client has been requesting
- **Grant Counters**: 16-bit lifetime grant counters per client
- **Sample Grant Counters**: 32-bit grant counters reset each sample period

#### **Global Tracking**
- **Sample Counter**: Tracks current position in sample period
- **Total Grants**: 32-bit lifetime grant counter
- **Active Request Count**: Real-time count of active requests

### **Event Generation Priority**

The monitor system processes events in strict priority order to ensure critical events are never lost:

1. **Priority 1 - Starvation Detection** (Highest)
   - Triggers when any client's request timer exceeds `cfg_mon_starvation_thresh`
   - Generates `AXI_ERR_ARBITER_STARVATION` error packets
   - Only one starvation event reported per cycle

2. **Priority 2 - Latency Threshold Violations**
   - Triggers when any client's request timer exceeds `cfg_mon_latency_thresh`
   - Generates `AXI_THRESH_GRANT_LATENCY` threshold packets
   - Reported only if no starvation event in same cycle

3. **Priority 3 - Active Request Count Threshold**
   - Triggers when active request count exceeds `cfg_mon_active_thresh`
   - Generates `AXI_THRESH_ACTIVE_COUNT` threshold packets
   - System-wide metric, not client-specific

4. **Priority 4 - Performance Reporting**
   - Triggers on every grant event (when `gnt_valid` is active)
   - Generates `AXI_PERF_GRANT_EFFICIENCY` performance packets
   - Provides real-time system activity visibility

### **Fairness Monitoring Algorithm**

The fairness monitoring system operates continuously to detect bandwidth monopolization:

#### **Fairness Violation Detection**
```
For each client i:
  if (client_grants[i] * 100 > total_grants * fairness_threshold) {
    fairness_violation = true
    dominant_client = i
  }
```

#### **Fairness Threshold Configuration Examples**
| Threshold Value | Description | Use Case |
|-----------------|-------------|----------|
| 25 | Strict fairness (no client >25% of bandwidth) | Debug/test scenarios |
| 40 | Moderate fairness (allows some priority clients) | Normal operation |
| 60 | Loose fairness (allows high-priority dominance) | Real-time systems |
| 80 | Emergency detection only | Fault detection |

### **Monitor Configuration Examples**

#### **High-Sensitivity Debug Configuration**
```
cfg_mon_thresh_lo_latency = 16'd100      // 100 cycle latency warning
cfg_mon_thresh_lo_starvation = 16'd500   // 500 cycle starvation error
cfg_mon_thresh_hi_fairness = 16'd25      // 25% fairness threshold
cfg_mon_thresh_hi_active = 16'd8         // 8 active requests warning
cfg_mon_ctrl_enable = 1'b1               // Enable monitoring
cfg_mon_ctrl_period = 8'd10              // 2^10 = 1024 cycle samples
```

#### **Production Monitoring Configuration**
```
cfg_mon_thresh_lo_latency = 16'd1000     // 1000 cycle latency warning
cfg_mon_thresh_lo_starvation = 16'd10000 // 10000 cycle starvation error
cfg_mon_thresh_hi_fairness = 16'd60      // 60% fairness threshold
cfg_mon_thresh_hi_active = 16'd16        // 16 active requests warning
cfg_mon_ctrl_enable = 1'b1               // Enable monitoring
cfg_mon_ctrl_period = 8'd16              // 2^16 = 65536 cycle samples
```

#### **Stress Test Monitoring Configuration**
```
cfg_mon_thresh_lo_latency = 16'd50     // 50 cycle latency warning
cfg_mon_thresh_lo_starvation = 16'd200 // 200 cycle starvation error
cfg_mon_thresh_hi_fairness = 16'd20    // 20% fairness threshold
cfg_mon_thresh_hi_active = 16'd4       // 4 active requests warning
cfg_mon_ctrl_enable = 1'b1             // Enable monitoring
cfg_mon_ctrl_period = 8'd8             // 2^8 = 256 cycle samples
```

## Example Agent Priority Configurations

### **Equal Priority Configuration (All Agents Same Weight)**

**Configuration for 32 agents with equal priority:**
- `cfg_X_arbt_arb_thresh_lo_prio = 32'h55555555`  // All agents 0-15 get credit=1 (01 binary)
- `cfg_X_arbt_arb_thresh_hi_prio = 32'h55555555`  // All agents 16-31 get credit=1 (01 binary)

### **CPU Priority Configuration (Higher Priority for Processing Cores)**

**Configuration favoring CPU cores (agents 0-7) over peripherals:**
- `cfg_X_arbt_arb_thresh_lo_prio = 32'hAAAA5555`  // Agents 8-15: credit=1, Agents 0-7: credit=2  
- `cfg_X_arbt_arb_thresh_hi_prio = 32'h55555555`  // Agents 16-31: credit=1 (peripherals)

### **Tiered Priority Configuration (Multiple Service Levels)**

**Configuration with disabled, low, medium, and high priority agents:**
- `cfg_X_arbt_arb_thresh_lo_prio = 32'hF5A50000`  // Mixed priorities for agents 0-15
- `cfg_X_arbt_arb_thresh_hi_prio = 32'h5555AAAA`  // Mixed priorities for agents 16-31

**Breakdown:**
- Agents 0-3: Disabled (credit=0)
- Agents 4-7: Low priority (credit=1) 
- Agents 8-11: Medium priority (credit=2)
- Agents 12-15: High priority (credit=3)
- Agents 16-23: Medium priority (credit=2)
- Agents 24-31: Low priority (credit=1)

## Why Controllable Arbiter Blocking is Transformative for SoC Design

### 1. **Deterministic Scenario Orchestration**

Traditional SoC testing suffers from non-deterministic timing interactions between subsystems. Controllable arbiter blocking enables **choreographed system scenarios** where:

- **Memory subsystem testing** can precisely align cache miss handling with specific DMA burst patterns
- **NoC congestion scenarios** can be reproduced exactly by blocking critical arbiters at predetermined intervals
- **Multi-core synchronization** can be validated by controlling when cores get access to shared resources
- **Power management validation** requires synchronized quiet periods where specific arbiters are disabled

**Real-World Impact**: A memory controller arbiter blocked for 10μs every 100μs creates a repeatable 10% backpressure scenario that would be impossible to achieve reliably through software alone.

### 2. **Advanced Performance Characterization with Real-Time Monitoring**

Controllable blocking transforms arbiters into **system performance probes** with comprehensive monitoring:

- **Bottleneck analysis**: Systematically block different arbiters while monitoring cascade effects through the monitor bus
- **QoS validation**: Verify that high-priority traffic maintains performance guarantees during controlled congestion with real-time latency measurements
- **Latency profiling**: Create controlled backpressure scenarios while monitoring actual latency distributions
- **Bandwidth allocation**: Validate that weighted arbitration truly delivers expected bandwidth ratios with fairness monitoring

**Measurement Precision**: Instead of waiting for natural congestion (which may never occur), engineers can create exact stress conditions and measure system response with statistical confidence through the monitor bus.

### 3. **Real-Time System Adaptation with Monitoring Feedback**

Beyond testing, controllable blocking with monitoring enables **dynamic system optimization**:

- **Thermal management**: Temporarily reduce arbiter activity in hot zones while monitoring performance impact
- **Power gating coordination**: Ensure clean power domain transitions with starvation monitoring
- **Security isolation**: Create temporal firewalls with active request monitoring
- **Debug assistance**: Freeze specific data flows while monitoring system recovery

### 4. **Verification Coverage Acceleration with Event Tracking**

Traditional verification struggles with **corner case coverage**. Controllable blocking with monitoring provides:

- **Forced race conditions**: Create timing scenarios with real-time latency monitoring
- **State space exploration**: Systematically explore arbiter behavior with performance tracking
- **Protocol stress testing**: Validate handshake protocols with timeout detection
- **Cache coherency validation**: Create controlled memory access patterns with fairness monitoring

## PWM Usage Patterns for Maximum SoC Impact

### **One-Shot Scenario Triggers (repeat_count = 1)**

#### Pattern: **Critical Event Synchronization**

**Configuration @ 1GHz:**
- `cfg_X_arbt_pwm_ctrl_hi_duty = 16'd5000`       // 5μs blocking duration
- `cfg_X_arbt_pwm_ctrl_hi_period = 16'd5000`     // 5μs period (100% duty)
- `cfg_X_arbt_pwm_ctrl_lo_repeat_cnt = 16'd1`    // Single shot
- `cfg_X_arbt_pwm_ctrl_lo_start = 1'b1`          // Trigger sequence

**Monitoring Configuration:**
- Enable starvation monitoring with 1000-cycle threshold
- Monitor active request buildup during blocking
- Track recovery latency after blocking ends

**Use Cases:**
- **Cache flush coordination**: Block memory arbiter during cache maintenance operations
- **DMA setup synchronization**: Ensure clean DMA descriptor setup without interference
- **Power domain transitions**: Create quiet periods during voltage scaling events
- **Security context switches**: Isolate sensitive operations with temporal barriers
- **Debug breakpoint assistance**: Freeze specific data flows when the debugger halts the system

#### Pattern: **Test Stimulus Injection**

**Configuration @ 1GHz:**
- `cfg_X_arbt_pwm_ctrl_hi_duty = 16'd500`        // 500ns brief disturbance
- `cfg_X_arbt_pwm_ctrl_hi_period = 16'd500`      // 500ns period (100% duty)
- `cfg_X_arbt_pwm_ctrl_lo_repeat_cnt = 16'd1`    // One-shot stimulus
- `cfg_X_arbt_pwm_ctrl_lo_start = 1'b1`          // Trigger sequence

**Monitoring Focus:**
- Track immediate latency impact on pending requests
- Monitor buffer utilization during brief blocking
- Verify timeout mechanisms aren't triggered

### **Periodic Short Disruptions (High Frequency, Low Duty Cycle)**

#### Pattern: **Micro-Backpressure Simulation**

**Configuration @ 1GHz:**
- `cfg_X_arbt_pwm_ctrl_hi_duty = 16'd100`        // 100ns blocking duration
- `cfg_X_arbt_pwm_ctrl_hi_period = 16'd2000`     // 2μs period (5% duty cycle)
- `cfg_X_arbt_pwm_ctrl_lo_repeat_cnt = 16'd500`  // 500 cycles = 1ms total duration
- `cfg_X_arbt_pwm_ctrl_lo_start = 1'b1`          // Trigger sequence

**Comprehensive Monitoring:**
- Sample period set to 2^8 = 256 cycles for high-resolution fairness tracking
- Latency threshold set to 50 cycles to catch brief spikes
- Active request threshold monitoring for queue buildup
- Performance reporting on every grant for detailed analysis

**Real-World Modeling:**
- **DRAM refresh simulation**: Model periodic DRAM refresh cycles that block memory access
- **Cache coherency traffic**: Simulate snoop operations that briefly stall regular memory traffic
- **Interrupt service overhead**: Model brief CPU unavailability during interrupt handling
- **Bus arbitration delays**: Simulate realistic bus contention in multi-master systems

#### Pattern: **High-Frequency Stress Testing**

**Configuration @ 1GHz:**
- `cfg_X_arbt_pwm_ctrl_hi_duty = 16'd50`         // 50ns blocking duration
- `cfg_X_arbt_pwm_ctrl_hi_period = 16'd200`      // 200ns period (25% duty cycle)
- `cfg_X_arbt_pwm_ctrl_lo_repeat_cnt = 16'd25000` // 25,000 cycles = 5ms total duration
- `cfg_X_arbt_pwm_ctrl_lo_start = 1'b1`          // Trigger sequence

**Intensive Monitoring Configuration:**
- Aggressive latency threshold (20 cycles) to catch all impacts
- Strict fairness monitoring (20% threshold) to detect priority inversions
- High-frequency sampling (2^6 = 64 cycle periods) for detailed statistics
- Starvation threshold set to 100 cycles for stress testing

### **Medium Duration Blocking Patterns**

#### Pattern: **Bandwidth Throttling Simulation**

**Configuration @ 1GHz:**
- `cfg_X_arbt_pwm_ctrl_hi_duty = 16'd10000`      // 10μs blocking duration
- `cfg_X_arbt_pwm_ctrl_hi_period = 16'd50000`    // 50μs period (20% duty cycle = 20% bandwidth reduction)
- `cfg_X_arbt_pwm_ctrl_lo_repeat_cnt = 16'd200`  // 200 cycles = 10ms total duration
- `cfg_X_arbt_pwm_ctrl_lo_start = 1'b1`          // Trigger sequence

**Bandwidth Monitoring Strategy:**
- Extended sample periods (2^12 = 4096 cycles) to capture bandwidth effects
- Fairness monitoring set to 40% to detect bandwidth monopolization
- Performance reporting tracks grant efficiency during throttling
- Monitor recovery patterns after each blocking period

### **Long Duration Scenario Testing**

#### Pattern: **Extended Maintenance Windows**

**Configuration @ 1GHz:**
- `cfg_X_arbt_pwm_ctrl_hi_duty_cycles = 16'd65535`  // Maximum ~65.5μs maintenance window
- `cfg_X_arbt_pwm_ctrl_hi_period = 16'd65535`       // 65.5μs period (100% duty)
- `cfg_X_arbt_pwm_ctrl_lo_repeat_count = 16'd1`     // Single extended blocking period
- `cfg_X_arbt_pwm_ctrl_lo_start = 1'b1`             // Trigger sequence

**Extended Duration Monitoring:**
- Starvation threshold set to 30,000 cycles for maintenance scenarios
- Monitor request queue buildup during extended blocking
- Track system recovery time after maintenance window
- Fairness monitoring disabled during maintenance (expected imbalance)

## Monitor Bus Integration Patterns

### **System-Level Monitoring Architecture**

```
+-----------------+    +-----------------+    +-----------------+
|   Arbiter #1    |    |   Arbiter #2    |    |   Arbiter #N    |
|  (Memory Ctrl)  |    |  (NoC Router)   |    |  (Peripheral)   |
+-----------------+    +-----------------+    +-----------------+
| Monitor FIFO    |    | Monitor FIFO    |    | Monitor FIFO    |
| Agent ID: 0x10  |    | Agent ID: 0x20  |    | Agent ID: 0xN0  |
+-----+-----------+    +-----+-----------+    +-----+-----------+
      |                      |                      |
      +----------------------+----------------------+
                             |
                   +---------▼----------+
                   |  Monitor Bus       |
                   |  Aggregator        |
                   |                    |
                   +---------+----------+
                             |
                   +---------▼----------+
                   |  System Monitor    |
                   |  and Analytics     |
                   +--------------------+
```

### **Event Correlation Strategies**

#### **Cross-Arbiter Analysis**
- Correlate starvation events across multiple arbiters to identify system-wide congestion
- Track latency spikes in downstream arbiters when upstream arbiters are blocked
- Monitor fairness violations that cascade through interconnected arbiters

#### **Temporal Pattern Analysis**
- Identify periodic behavior patterns from PWM-induced blocking
- Correlate monitoring events with PWM cycle phases
- Detect unexpected system resonances or interference patterns

#### **Performance Baseline Establishment**
- Use monitoring data from unblocked operation to establish baseline metrics
- Compare blocked vs. unblocked performance to measure PWM impact
- Quantify system resilience to various blocking patterns

### **Debug and Diagnostics Integration**

#### **Real-Time Debug Triggers**
```systemverilog
// Example trigger logic
always_ff @(posedge clk) begin
  if (monbus_valid && monbus_packet[63:60] == PktTypeError) begin
    // Trigger debug capture on any error event
    debug_trigger <= 1'b1;
  end
end
```

#### **Performance Profiling**
- Continuous latency histograms from monitoring data
- Bandwidth utilization tracking across different blocking patterns
- Fairness index calculations for system optimization

#### **Automated Test Orchestration**
- Use monitoring feedback to automatically adjust PWM parameters
- Implement closed-loop testing where monitor events trigger new test patterns
- Create adaptive stress testing that increases intensity based on system response

## Strategic PWM Pattern Selection with Monitoring

### **Selection Criteria Matrix**

| Test Objective | Duration | Frequency | Repeat Count | Pattern Type | Monitor Focus |
|----------------|----------|-----------|--------------|--------------|---------------|
| Corner case triggering | 50ns-500ns | Single shot | 1 | One-shot stimulus | Latency spikes |
| Protocol stress testing | 100ns-1μs | 1-10kHz | 100-1000 | High-freq disruption | Timeout events |
| Performance characterization | 1μs-10μs | 100Hz-1kHz | 10-100 | Medium-freq testing | Bandwidth metrics |
| System integration | 10μs-100μs | 10-100Hz | 5-50 | Low-freq validation | Fairness tracking |
| Maintenance simulation | 100μs-1ms | Single shot | 1 | Extended blocking | Recovery analysis |

### **Monitoring-Driven Pattern Optimization**

1. **Start with Comprehensive Monitoring**: Enable all monitoring features during initial pattern exploration
2. **Analyze Event Patterns**: Use monitoring data to understand system response to different PWM configurations
3. **Refine Based on Feedback**: Adjust PWM parameters based on monitoring event frequencies and types
4. **Establish Acceptance Criteria**: Define acceptable monitoring event rates for different operational scenarios
5. **Automate Pattern Selection**: Use monitoring data to automatically select optimal PWM patterns for specific test objectives

The combination of controllable PWM blocking with comprehensive real-time monitoring creates a powerful platform for SoC validation, performance optimization, and system understanding that goes far beyond traditional testing approaches.