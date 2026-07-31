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

# fifo_sync (`fifo_sync.sv`)

## Purpose
A synchronous First-In-First-Out buffer for when everything lives in a single clock domain. Depth, data width, and output modes are all configurable, and you get the full set of status signals.

## Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `MEM_STYLE` | — | Memory implementation (`FIFO_AUTO`/SRL/BRAM) — see note below |
| `REGISTERED` | — | Output mode: 0=mux mode (combinational), 1=flop mode (registered) |
| `DATA_WIDTH` | 4 | Width of data bus |
| `DEPTH` | 4 | FIFO depth in words |
| `ALMOST_WR_MARGIN` | 1 | Almost full threshold |
| `ALMOST_RD_MARGIN` | 1 | Almost empty threshold |

**`MEM_STYLE` details:** In this module every branch honours `REGISTERED`: with
`REGISTERED=0` the BRAM branch gives a *combinational* read
(`always_comb w_rd_data = mem[r_rd_addr]`), not a registered one. Note that
`fifo_async` differs here — its BRAM branch is unconditionally registered — so
do not carry that assumption across. **Caveat:** `MEM_STYLE=FIFO_BRAM` with
`REGISTERED=0` asks for an asynchronous read from a block RAM, which real BRAM
cannot do; synthesis will ignore the `ram_style`/`ramstyle` attribute and map
to LUTRAM instead. Use `REGISTERED=1` when you actually want block RAM.

## Ports
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | System clock |
| `rst_n` | Input | 1 | Active-low reset |
| `write` | Input | 1 | Write enable signal |
| `wr_data` | Input | DATA_WIDTH | Data to write into FIFO |
| `read` | Input | 1 | Read enable signal |
| `wr_full` | Output | 1 | Write domain full flag |
| `wr_almost_full` | Output | 1 | Write domain almost full flag |
| `rd_data` | Output | DATA_WIDTH | Data read from FIFO |
| `rd_empty` | Output | 1 | Read domain empty flag |
| `rd_almost_empty` | Output | 1 | Read domain almost empty flag |

## Architecture Overview

### Core Components
1. **Binary counters** for the read/write pointers
2. **Memory array** for data storage
3. **FIFO control logic** for status generation
4. **Output multiplexing** based on the REGISTERED parameter

### Memory Organization
```systemverilog
logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // Memory array
assign r_wr_addr = r_wr_ptr_bin[AW-1:0];  // Write address
assign r_rd_addr = r_rd_ptr_bin[AW-1:0];  // Read address
```

## Implementation Details

### Pointer Management
Binary counters drive both the read and write pointers:

```systemverilog
counter_bin #(.WIDTH(AW + 1), .MAX(D)) write_pointer_inst (
    .clk(clk),
    .rst_n(rst_n),
    .enable(write && !wr_full),
    .counter_bin_curr(r_wr_ptr_bin),
    .counter_bin_next(w_wr_ptr_bin_next)
);
```

#### Pointer Characteristics
- **Width**: `$clog2(DEPTH) + 1` bits (the extra bit catches wraps)
- **Increment**: Only when the operation is valid (write && !full, read && !empty)
- **Wraparound**: Automatic modulo DEPTH counting

### Memory Operations

#### Write Operation
```systemverilog
always_ff @(posedge clk) begin
    if (write && !wr_full) begin   // the !wr_full guard is REQUIRED: it stops a
        mem[r_wr_addr] <= wr_data;  // write-while-full from clobbering unread data
    end
end
```

#### Read Operation - Dual Mode
```systemverilog
generate
    if (REGISTERED != 0) begin : gen_flop_mode
        // Flop mode - registered output
        always_ff @(posedge clk or negedge rst_n) begin
            if (!rst_n)
                rd_data <= 'b0;
            else
                rd_data <= w_rd_data;
        end
    end else begin : gen_mux_mode
        // Mux mode - non-registered output
        assign rd_data = w_rd_data;
    end
endgenerate
```

### Status Flag Generation
Status comes out of the shared `fifo_control` module:
- **Full detection**: Based on pointer comparison with wraparound handling
- **Almost full**: When remaining space ≤ `ALMOST_WR_MARGIN`
- **Empty detection**: When read pointer equals write pointer
- **Almost empty**: When available data ≤ `ALMOST_RD_MARGIN`

## Operating Modes

### Mux Mode (REGISTERED = 0)
- **Read latency**: 0 cycles (combinational output)
- **Data availability**: Immediate after write
- **Use case**: Low-latency applications
- **Timing**: Read data changes combinationally with the address

### Flop Mode (REGISTERED = 1)  
- **Read latency**: 1 cycle (registered output)
- **Data availability**: 1 cycle after read enable
- **Use case**: High-speed designs, timing closure
- **Timing**: Read data stable for the full clock cycle

## Functional Behavior

### Write Operations
- **Condition**: `write && !wr_full`
- **Action**: Store data at the write pointer, bump the pointer
- **Blocking**: Writes ignored when the FIFO is full
- **Status**: Full flags track the new occupancy

### Read Operations
- **Condition**: `read && !rd_empty`  
- **Action**: Advance the read pointer (data handling depends on mode)
- **Blocking**: Reads ignored when the FIFO is empty
- **Status**: Empty flags track the new occupancy

### Reset Behavior
- **Pointers**: Reset to 0
- **Flags**: Full flags → 0, Empty flags → 1
- **Data**: Read data cleared in flop mode
- **Memory**: Contents undefined, but that doesn't matter

## Timing Diagrams

### Write Sequence
```
clk     __|‾|__|‾|__|‾|__|‾|__
write   ______|‾‾‾‾‾|_________
wr_data ======[ D0 ]=========
wr_full _____________________|‾  (when FIFO becomes full)
```

### Read Sequence - Mux Mode
```
clk     __|‾|__|‾|__|‾|__|‾|__
read    ______|‾‾‾‾‾|_________
rd_data ======[ D0 ]=========  (immediate)
```

### Read Sequence - Flop Mode  
```
clk     __|‾|__|‾|__|‾|__|‾|__
read    ______|‾‾‾‾‾|_________
rd_data ===========[ D0 ]=====  (1 cycle delay)
```

## Use Cases

### Low Latency Applications (Mux Mode)
- Data streaming with minimal delay
- Real-time processing pipelines
- Clock domain buffers

### High Speed Applications (Flop Mode)
- High-frequency designs
- Timing-critical paths
- Pipelined architectures

## Design Considerations

### Mode Selection Guidelines
- **Choose Mux Mode when**: Latency is critical, moderate clock speeds
- **Choose Flop Mode when**: High clock speeds, timing closure issues
- **Performance impact**: Flop mode costs you 1 cycle of latency but buys fmax

### Sizing Considerations
- **Depth**: Must accommodate worst-case burst sizes
- **Almost flags**: Set margins based on producer/consumer response times
- **Data width**: Should match datapath requirements

### Error Detection
**Note:** the current RTL does **not** contain any runtime `$display`
overflow/underflow checks. The
`!wr_full` write guard is the only overflow protection. If you need write-while-
full / read-while-empty telemetry, add assertions in your own testbench.

## Performance Characteristics
- **Throughput**: 1 operation per clock cycle (when not full/empty)
- **Latency**: 0 cycles (mux) or 1 cycle (flop) for read
- **Occupancy**: 0 to DEPTH words
- **Efficiency**: 100% bandwidth utilization possible

## WaveDrom Visualization

**High-quality waveforms showcasing synchronous FIFO operation are available!**

Run the WaveDrom test to generate detailed timing diagrams:

```bash
# Generate synchronous FIFO waveforms (single clock domain)
pytest val/common/test_fifo_sync_wavedrom.py -v
```

**Waveform Scenarios Generated:**

1. **Write-Fill-Read-Empty Cycle**
   - Basic synchronous FIFO operation
   - Simple binary pointer management
   - No CDC complexity (single clock domain)

2. **Back-to-Back Operations**
   - Maximum throughput demonstration
   - Minimal inter-transaction delays
   - Sequential write and read bursts

3. **Simultaneous Write-Read (Ping-Pong)**
   - Read and write in same cycle
   - Steady-state FIFO operation
   - Demonstrating simultaneous access capability

4. **Flag Transitions**
   - Full/empty flag behavior at boundaries
   - Almost-full/almost-empty thresholds
   - Flow control signaling

**Key Characteristics vs. Async FIFOs:**

- **Single Clock Domain**: No CDC complexity, simpler design
- **Binary Pointers**: Direct addressing, no Gray code conversion
- **Zero CDC Latency**: Flags update immediately (no synchronization delay)
- **Simultaneous Access**: Can read and write in same cycle

**Comparison Tests:**

- `test_fifo_async_wavedrom.py` - Gray code CDC (power-of-2 depths)

## Test and Verification

**Comprehensive Test Suite:**
- `val/common/test_fifo_buffer.py` - Full functional verification
- `val/common/test_fifo_sync_wavedrom.py` - WaveDrom timing diagrams

**Run Tests:**
```bash
# Full functional test (basic/medium/full levels)
pytest val/common/test_fifo_buffer.py -v

# WaveDrom waveform generation
pytest val/common/test_fifo_sync_wavedrom.py -v
```

## Related Modules
- **fifo_async**: For clock domain crossing applications
- **fifo_control**: Shared status flag generation logic
- **counter_bin**: Binary counter implementation

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
