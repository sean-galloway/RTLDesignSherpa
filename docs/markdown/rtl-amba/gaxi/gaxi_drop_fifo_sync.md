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

# gaxi_drop_fifo_sync

**Module:** `gaxi_drop_fifo_sync.sv`
**Location:** `rtl/amba/gaxi/`
**Status:** Production Ready

---

## Overview

A synchronous GAXI FIFO with a trick most FIFOs don't have: a drop interface that removes entries without reading them. You get standard valid/ready handshaking on both the write and read sides, plus the ability to drop the N oldest entries or flush the whole buffer — the operation you want when stale packets are worse than no packets.

### Key Features

- **Standard Handshake:** GAXI valid/ready on write and read
- **Configurable:** Data width and depth
- **Drop by Count:** Remove N oldest entries
- **Drop All:** Flush entire FIFO
- **I/O Blocking:** Writes and reads pause during drop operations (3-cycle latency)
- **Two Output Modes:** Registered or mux-based
- **Occupancy Output:** FIFO count output (`[AW:0]`); the almost-full/almost-empty flags stay internal

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `MEM_STYLE` | fifo_mem_t | `FIFO_AUTO` | Memory inference hint: `FIFO_AUTO`, `FIFO_SRL` (distributed/MLAB), or `FIFO_BRAM` (block RAM). `FIFO_BRAM` forces a synchronous memory read, adding a cycle on top of `REGISTERED`. |
| `DATA_WIDTH` | int | 4 | Width of data bus in bits |
| `DEPTH` | int | 4 | FIFO depth (must be power of 2) |
| `REGISTERED` | int | 0 | 0 = mux mode, 1 = registered output |
| `ALMOST_WR_MARGIN` | int | 1 | Almost-full margin (internal only — see below) |
| `ALMOST_RD_MARGIN` | int | 1 | Almost-empty margin (internal only — see below) |

> The `DATA_WIDTH`/`DEPTH` defaults are 4 and 4, not 32 and 16. They are sized
> for a smoke test, so set both explicitly for anything real.

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `DW` | `DATA_WIDTH` |
| `D` | `DEPTH` |

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | Clock signal |
| `axi_aresetn` | input | 1 | Active-low asynchronous reset |

### Write Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `wr_valid` | input | 1 | Write data valid |
| `wr_ready` | output | 1 | FIFO ready to accept write |
| `wr_data` | input | DATA_WIDTH | Write data |

**Handshake:** Write occurs when `wr_valid && wr_ready` on rising edge of clock.

### Read Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `rd_valid` | output | 1 | Read data valid |
| `rd_ready` | input | 1 | Downstream ready to accept read |
| `rd_data` | output | DATA_WIDTH | Read data |

**Handshake:** Read occurs when `rd_valid && rd_ready` on rising edge of clock.

### Drop Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `drop_valid` | input | 1 | Drop request valid |
| `drop_ready` | output | 1 | Drop operation complete |
| `drop_count` | input | $clog2(DEPTH)+1 | Number of entries to drop. 5 bits at DEPTH=16, 9 bits at DEPTH=256 — not a fixed 8. |
| `drop_all` | input | 1 | Drop all entries (ignore count) |

**Handshake:** Drop completes when `drop_valid && drop_ready` on rising edge of clock.

**Drop Latency:** 3 clock cycles from `drop_valid` assertion to `drop_ready` assertion.

### Status

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `count` | output | $clog2(DEPTH)+1 | Current number of entries in FIFO |

> **There are no `almost_full` / `almost_empty` ports.** The module's port list
> ends at `drop_all`. `fifo_control` computes both flags, but they land on
> internal wires (`r_wr_almost_full`, `r_rd_almost_empty`) that are not brought
> out, so `ALMOST_WR_MARGIN` and `ALMOST_RD_MARGIN` have no observable effect.
> Use `count` against your own threshold instead.

---

## Functional Description

### Drop by Count

When `drop_valid=1` and `drop_all=0`, the FIFO removes `drop_count` oldest entries:

1. **Cycle 0**: Assert `drop_valid`, set `drop_count=N`
2. **Cycle 1-2**: Drop operation in progress, `drop_ready=0`, I/O blocked
3. **Cycle 3**: Drop complete, `drop_ready=1`
4. **Result**: the read pointer advances by exactly `N`

> **`drop_count` must not exceed `count`.** There is no clamp in hardware —
> `counter_bin_load` adds `drop_count` to the read pointer unconditionally.
> Dropping 5 from a FIFO holding 3 (DEPTH=16) leaves `rd_ptr=5` ahead of
> `wr_ptr=3`, and `fifo_control` then computes a count of 30 with `rd_empty`
> still low: the FIFO reports 30 entries of garbage and hands back memory
> that was never written. Simulation now catches this at the capture edge
> with a `$error` (the check the RTL header had always promised); silicon
> does not — bound `drop_count` on your side.

**I/O Blocking**: During drop operation (cycles 1-2):
- `wr_ready = 0` (writes blocked)
- `rd_valid = 0` (reads blocked)

### Drop All

When `drop_valid=1` and `drop_all=1`, the FIFO is completely flushed:

1. **Cycle 0**: Assert `drop_valid` and `drop_all=1`
2. **Cycle 1-2**: Drop operation in progress
3. **Cycle 3**: Drop complete, `drop_ready=1`
4. **Result**: FIFO count becomes 0

**Note**: `drop_count` is ignored when `drop_all=1`.

### Simultaneous Operations

**Write + Drop**: Blocked - writes cannot proceed during drop operation.

**Read + Drop**: Blocked - reads cannot proceed during drop operation.

**Drop + Drop**: Not supported - wait for `drop_ready` before issuing next drop.

---

## Timing Characteristics

### Fill FIFO

*Generated by test_gaxi_drop_fifo_wavedrom.py*

This scenario shows writing 4 entries to an empty FIFO:
- Write handshakes occur when `wr_valid && wr_ready`
- FIFO count increments with each successful write
- Data values: 0xA0, 0xA1, 0xA2, 0xA3

> *Timing diagram not yet captured.* The scenario is described above.
> `test_gaxi_drop_fifo_wavedrom.py` is intended to emit
> `gaxi_drop_fifo_fill.json` into `docs/markdown/assets/WAVES/`, but it does not
> currently write the file; the diagram is a documentation gap, not a
> missing feature of the module.

### Drop by Count

*Generated by test_gaxi_drop_fifo_wavedrom.py*

This scenario demonstrates dropping 2 oldest entries:
- `drop_valid` asserted with `drop_count=2`
- 3-cycle latency until `drop_ready` assertion
- FIFO count decreases by 2
- Normal I/O blocked during drop

> *Timing diagram not yet captured.* The scenario is described above.
> `test_gaxi_drop_fifo_wavedrom.py` is intended to emit
> `gaxi_drop_fifo_drop_by_count.json` into `docs/markdown/assets/WAVES/`, but it does not
> currently write the file; the diagram is a documentation gap, not a
> missing feature of the module.

### Drop All

*Generated by test_gaxi_drop_fifo_wavedrom.py*

This scenario shows flushing the entire FIFO:
- `drop_valid` asserted with `drop_all=1`
- 3-cycle latency until `drop_ready` assertion
- FIFO count becomes 0
- All entries discarded

> *Timing diagram not yet captured.* The scenario is described above.
> `test_gaxi_drop_fifo_wavedrom.py` is intended to emit
> `gaxi_drop_fifo_drop_all.json` into `docs/markdown/assets/WAVES/`, but it does not
> currently write the file; the diagram is a documentation gap, not a
> missing feature of the module.

### Comprehensive Scenario

*Generated by test_gaxi_drop_fifo_wavedrom.py*

This scenario demonstrates mixed operations:
- Read 1 entry from FIFO
- Drop remaining entries with `drop_all=1`
- Shows interaction between read and drop interfaces

> *Timing diagram not yet captured.* The scenario is described above.
> `test_gaxi_drop_fifo_wavedrom.py` is intended to emit
> `gaxi_drop_fifo_comprehensive.json` into `docs/markdown/assets/WAVES/`, but it does not
> currently write the file; the diagram is a documentation gap, not a
> missing feature of the module.

---

## Usage Examples

### Basic Write/Read

```systemverilog
// Instantiate FIFO
gaxi_drop_fifo_sync #(
    .DATA_WIDTH(32),
    .DEPTH(16),
    .REGISTERED(0)
) u_fifo (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),
    .wr_valid    (wr_valid),
    .wr_ready    (wr_ready),
    .wr_data     (wr_data),
    .rd_valid    (rd_valid),
    .rd_ready    (rd_ready),
    .rd_data     (rd_data),
    .drop_valid  (1'b0),        // No drop
    .drop_ready  (),
    .drop_count  (8'h0),
    .drop_all    (1'b0),
    .count       (fifo_count)
);

// Write logic
always_ff @(posedge clk) begin
    if (!rst_n) begin
        wr_valid <= 1'b0;
    end else if (wr_valid && wr_ready) begin
        wr_valid <= 1'b0;  // Deassert after handshake
    end else if (have_data_to_write && (fifo_count < DEPTH - 1)) begin
        wr_valid <= 1'b1;
        wr_data  <= next_data;
    end
end
```

### Drop Operation

```systemverilog
// Drop state machine
typedef enum logic [1:0] {
    IDLE,
    DROP_WAIT,
    DROP_DONE
} drop_state_t;

drop_state_t state;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state      <= IDLE;
        drop_valid <= 1'b0;
    end else begin
        case (state)
            IDLE: begin
                if (trigger_drop_all) begin
                    drop_valid <= 1'b1;
                    drop_all   <= 1'b1;
                    drop_count <= 8'h0;  // Ignored when drop_all=1
                    state      <= DROP_WAIT;
                end else if (trigger_drop_count) begin
                    drop_valid <= 1'b1;
                    drop_all   <= 1'b0;
                    drop_count <= num_to_drop;
                    state      <= DROP_WAIT;
                end
            end

            DROP_WAIT: begin
                if (drop_ready) begin
                    drop_valid <= 1'b0;
                    state      <= DROP_DONE;
                end
            end

            DROP_DONE: begin
                // Single-cycle state
                state <= IDLE;
            end
        endcase
    end
end
```

---

## Design Notes

### FIFO Depth Requirements

**MUST** be a power of 2 for efficient address pointer implementation.

Valid: 8, 16, 32, 64, 128, 256, ...

Invalid: 10, 15, 20, 100, ...

### Registered vs. Mux Mode

**Mux Mode (REGISTERED=0)**:
- Lower latency (combinatorial path from FIFO RAM to `rd_data`)
- Better for timing-critical paths where output is registered downstream
- Simpler implementation

**Registered Mode (REGISTERED=1)**:
- Extra register stage on `rd_data` output
- Better timing closure for long data paths
- Adds 1 cycle of read latency

### Drop Latency

The 3-cycle drop latency is inherent to the implementation:
1. **Cycle 1**: Latch drop request
2. **Cycle 2**: Update read pointer
3. **Cycle 3**: Assert drop_ready

This latency ensures clean separation between normal FIFO operations and drop operations.

### Almost Full/Empty Margins

`ALMOST_WR_MARGIN` and `ALMOST_RD_MARGIN` are accepted but have NO observable
effect on this module -- the almost-full/almost-empty flags exist only as
internal wires and are never brought out (the port list ends at `drop_all`).
Threshold logic belongs on YOUR side: compare `count` against your own
watermark. (This section previously gave sizing guidance for margins that can
never appear; the note earlier on this page was always the correct one.)

---

## Related Modules

- `fifo_control.sv` - Core FIFO control logic
- `counter_bin.sv` - Binary counter for address generation
- `counter_bin_load.sv` - Loadable binary counter for drop pointer updates
- `gaxi_drop_fifo_async.sv` - Asynchronous clock domain version (future)

---

## Testing

Comprehensive verification lives in `val/amba/test_gaxi_drop_fifo_sync.py`:

| Test Scenario | Coverage |
|---------------|----------|
| **Basic FIFO Operation** | Standard write/read without drops |
| **Drop by Count** | Partial FIFO flush with specific count |
| **Drop All** | Complete FIFO flush |
| **Drop During I/O** | Verify I/O blocking during drop |
| **Wraparound with Drop** | Drop across pointer wraparound boundary |

**Test Configurations**:
- Data widths: 8, 32, 64 bits
- Depths: 8, 16, 64, 256 entries
- Modes: Mux (REGISTERED=0) and Flop (REGISTERED=1)

**Results**: All 8 parameterized test cases pass

### Running Tests

```bash
# Run all drop FIFO tests
pytest val/amba/test_gaxi_drop_fifo_sync.py -v

# Run specific test configuration
pytest "val/amba/test_gaxi_drop_fifo_sync.py::test_gaxi_drop_fifo_sync[8-8-0-minimal-mux]" -v

# Run smoke test (quick verification)
pytest val/amba/test_gaxi_drop_fifo_sync.py::test_gaxi_drop_fifo_smoke -v

# Generate waveforms for documentation
env ENABLE_WAVEDROM=1 pytest val/amba/test_gaxi_drop_fifo_wavedrom.py -v
```

---

**Version:** 1.0
**Last Updated:** 2025-10-17

---

## Navigation

- **[← Back to GAXI Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
